{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE MonoLocalBinds #-}
{-|
  Given an input program 𝑝, equality saturation constructs an e-graph 𝐸 that
  represents a large set of programs equivalent to 𝑝, and then extracts the
  “best” program from 𝐸.

  The e-graph is grown by repeatedly applying pattern-based rewrites.
  Critically, these rewrites only add information to the e-graph, eliminating
  the need for careful ordering.

  Upon reaching a fixed point (saturation), 𝐸 will represent all equivalent
  ways to express 𝑝 with respect to the given rewrites.

  After saturation (or timeout), a final extraction procedure analyzes 𝐸 and
  selects the optimal program according to a user-provided cost function.
 -}
module Data.Equality.Saturation
    (
      -- * Equality saturation
      equalitySaturation, equalitySaturation', runEqualitySaturation

      -- * Re-exports for equality saturation

      -- ** Writing rewrite rules
    , Rewrite(..), RewriteCondition

      -- ** Writing cost functions
      --
      -- | 'CostFunction' re-exported from 'Data.Equality.Extraction' since they are required to do equality saturation
    , CostFunction --, depthCost

      -- ** Writing expressions
      -- 
      -- | Expressions must be written in their fixed-point form, since the
      -- 'Language' must be given in its base functor form
    , Fix(..), cata

    ) where

import qualified Data.IntMap.Strict as IM

import Data.Bifunctor
import Control.Monad

import Data.Equality.Utils
import Data.Equality.Graph.Nodes
import Data.Equality.Graph.Lens
import Data.Equality.Graph.Internal (EGraph(classes))
import qualified Data.Equality.Graph as G
import Data.Equality.Graph.Monad hiding (get)
import Data.Equality.Language
import Data.Equality.Analysis
import Data.Equality.Graph.Classes
import Data.Equality.Matching
import Data.Equality.Matching.Database
import Data.Equality.Extraction

import Data.Equality.Saturation.Rewrites
import Data.Equality.Saturation.Scheduler
import Control.Monad.State (MonadState (..))
import GHC.Stack (HasCallStack)
import qualified Data.Set as S
import qualified Data.Equality.Compiler.Index as Idx
import qualified Data.Equality.Compiler.QueryExecution as Exec
import qualified Data.Equality.Compiler.API as API
import qualified Control.Monad.State as M
import Debug.Trace (traceM)
import qualified Data.Equality.Saturation.Scheduler as Score
import Data.Equality.Compiler.RuleCompilation (_MAGIC_ROOT_INT, _MAGIC_ROOT)

-- | Equality saturation with defaults
equalitySaturation :: forall a l cost
                    . (HasCallStack, Show (l Int) ,Analysis a l, Language l, Ord cost)
                   => Fix l               -- ^ Expression to run equality saturation on
                   -> [Rewrite a l]         -- ^ List of rewrite rules
                   -> CostFunction l cost -- ^ Cost function to extract the best equivalent representation
                   -> (Fix l, EGraph a l)   -- ^ Best equivalent expression and resulting e-graph
equalitySaturation = equalitySaturation' defaultBackoffScheduler


-- | Run equality saturation on an expression given a list of rewrites, and
-- extract the best equivalent expression according to the given cost function
--
-- This variant takes all arguments instead of using defaults
equalitySaturation' :: forall a l schd cost
                    . (HasCallStack, Show (l Int), Analysis a l, Language l, Scheduler schd, Ord cost)
                    => schd                -- ^ Scheduler to use
                    -> Fix l               -- ^ Expression to run equality saturation on
                    -> [Rewrite a l]       -- ^ List of rewrite rules
                    -> CostFunction l cost -- ^ Cost function to extract the best equivalent representation
                    -> (Fix l, EGraph a l)   -- ^ Best equivalent expression and resulting e-graph
equalitySaturation' schd expr rewrites cost = egraph $ do

    -- Represent expression as an e-graph
    origClass <- represent expr

    -- Run equality saturation (by applying non-destructively all rewrites)
    runEqualitySaturation2 schd rewrites

    -- Extract best solution from the e-class of the original expression
    gets $ \g -> extractBest g cost origClass
{-# INLINABLE equalitySaturation' #-}

{-# INLINE runEqualitySaturation2#-}
runEqualitySaturation2 :: forall a l schd
                       . (Analysis a l, Language l, Scheduler schd)
                      => schd                -- ^ Scheduler to use
                      -> [Rewrite a l]       -- ^ List of rewrite rules
                      -> EGraphM a l ()
runEqualitySaturation2 schd rewrites = runEqualitySaturation' 0 mempty 
  where
      rwMap = IM.fromList $ zip [1..] rewrites 
     
      toPat (l :| _) = toPat l
      toPat (l := _) = [ API.Equation _MAGIC_ROOT l ]
      toMatch subst = Match (IM.delete _MAGIC_ROOT_INT subst) (subst IM.! _MAGIC_ROOT_INT)

      -- Take map each rewrite rule to stats on its usage so we can do
      -- backoff scheduling. Each rewrite rule is assigned an integer
      -- (corresponding to its position in the list of rewrite rules)
      runEqualitySaturation' :: Int -> IM.IntMap (Stat schd) -> EGraphM a l ()
      runEqualitySaturation' 5 _ = pure ()
      runEqualitySaturation' epoch stats = do
            eg <- get
            let allTups = Idx.toAllTuples (classes eg)
            let isActive ix _ =  maybe True (not . isBanned epoch) (IM.lookup ix stats) 
                matchesFound = Exec.runRewrites allTups (IM.filterWithKey isActive (fmap toPat rwMap))
            let
              (matches, stats') = mconcat $ do
                k <- IM.keys rwMap
                let lhs = rwMap IM.! k
                case IM.lookup k stats of
                  Just s | isBanned @schd epoch s -> pure ([], stats)
                  x -> do
                    let matches' = S.toList $ S.fromList $ toMatch <$> matchesFound IM.! k
                    let newStats = updateStats schd epoch k x stats matches'
                    pure (fmap (lhs,) matches', newStats)

            -- let stats' = foldr (\(k, v::Score) acc -> updateStatsScore schd epoch k (acc IM.!? k) acc v) stats (IM.toList matches)
            traceM ("Epoch " <> show (epoch, G.sizeNM (eg ^. _memo), IM.size (classes eg)))
            traceM . show =<< get
            traceM . simpEg =<< get
            traceM (unlines $ map show matches)
            forM_ matches $ \(lhs, subst) -> do 
                    applyMatchesRhs (lhs, subst) 
            traceM "Pre rebuild:"
            traceM . show =<< get
           
            rebuild
            -- traceM . simpEg =<< get
            let (beforeMemo, beforeClasses) = (eg^._memo, classes eg)
            (afterMemo, afterClasses) <- M.gets (\g -> (g^._memo, classes g))
            -- traceM (show (G.sizeNM afterMemo, IM.size afterClasses))
            unless (G.sizeNM afterMemo == G.sizeNM beforeMemo
                       && IM.size afterClasses == IM.size beforeClasses)
               (runEqualitySaturation' (epoch+1) stats')

-- {-# INLINE runEqualitySaturationFast#-}
-- runEqualitySaturationFast :: forall a l schd
--                        . (HasCallStack, Analysis a l, Language l, Scheduler schd)
--                       => schd                -- ^ Scheduler to use
--                       -> [Rewrite a l]       -- ^ List of rewrite rules
--                       -> EGraphM a l ()
-- runEqualitySaturationFast schd rewrites = runEqualitySaturationAPI endCheck schd (map toAPI rewrites)
--   where
--     endCheck i = pure (i> 7)
--     toAPI (l := r) = (l::Pattern l) API..== r
--     toAPI (l :|r) = toAPI l API..| r

simpEg :: (Show a, Show (l ClassId)) => EGraph a l -> String
simpEg (eg :: EGraph a l) = unlines $ do
    (pid, nodes) <- IM.toList (classes eg)

    [ show pid <> " ~= "<> show (eClassData nodes) ] <> do
        n <- S.toList $ G.eClassNodes nodes
        pure $ show pid <> ":=" <> show (unNode n)



-- | Run equality saturation on an e-graph by non-destructively applying all
-- given rewrite rules until saturation (using the given 'Scheduler')
runEqualitySaturation :: forall a l schd
                       . (Analysis a l, Language l, Scheduler schd)
                      => schd                -- ^ Scheduler to use
                      -> [Rewrite a l]       -- ^ List of rewrite rules
                      -> EGraphM a l ()
runEqualitySaturation schd rewrites = runEqualitySaturation' 0 mempty where -- Start at iteration 0

  -- Take map each rewrite rule to stats on its usage so we can do
  -- backoff scheduling. Each rewrite rule is assigned an integer
  -- (corresponding to its position in the list of rewrite rules)
  runEqualitySaturation' :: Int -> IM.IntMap (Stat schd) -> EGraphM a l ()
  runEqualitySaturation' 5 _ = return () -- Stop after X iterations
  runEqualitySaturation' i stats = do

      egr <- get
      -- traceM (show i)

      let (beforeMemo, beforeClasses) = (egr^._memo, classes egr)
          db = eGraphToDatabase egr

      -- Read-only phase, invariants are preserved
      -- With backoff scheduler
      -- ROMES:TODO parMap with chunks
      let (!matches, newStats) = mconcat (fmap (\(rw_id,rw) -> first (map (rw,)) $ matchWithScheduler db i stats rw_id rw) (zip [1..] rewrites))

      -- Write-only phase, temporarily break invariants
      traceM ("Epoch " <> show (i, G.sizeNM (egr ^. _memo), IM.size (classes egr)))
      traceM . simpEg =<< get

      traceM (unlines $ map show matches)
      forM_ matches applyMatchesRhs

      -- Restore the invariants once per iteration
      rebuild
      
      (afterMemo, afterClasses) <- gets (\g -> (g^._memo, classes g))
      -- traceM (show (G.sizeNM afterMemo, IM.size afterClasses))

      -- ROMES:TODO: Node limit...
      -- ROMES:TODO: Actual Timeout... not just iteration timeout
      -- ROMES:TODO Better saturation (see Runner)
      -- Apply rewrites until saturated or ROMES:TODO: timeout
      unless (G.sizeNM afterMemo == G.sizeNM beforeMemo
                && IM.size afterClasses == IM.size beforeClasses)
          (runEqualitySaturation' (i+1) newStats)

  matchWithScheduler :: Database l -> Int -> IM.IntMap (Stat schd) -> Int -> Rewrite a l -> ([Match], IM.IntMap (Stat schd))
  matchWithScheduler db i stats rw_id = \case
      rw  :| _ -> matchWithScheduler db i stats rw_id rw
      lhs := _ -> do
          case IM.lookup rw_id stats of
            -- If it's banned until some iteration, don't match this rule
            -- against anything.
            Just s | isBanned @schd i s -> ([], stats)

            -- Otherwise, match and update stats
            x -> do

                -- Match pattern
                let matches' = ematch db lhs -- Add rewrite to the e-match substitutions
                -- traceM (show (rw_id, foldMap (Score.fromSubst . matchSubst) matches'))

                -- Backoff scheduler: update stats
                let newStats = updateStats schd i rw_id x stats matches'

                (S.toList . S.fromList $ matches', newStats)

applyMatchesRhs :: (Analysis a l, Language l) =>  (Rewrite a l, Match) -> EGraphM a l ()
applyMatchesRhs =
  \case
      (rw :| cond, m@(Match subst _)) -> do
          -- If the rewrite condition is satisfied, applyMatchesRhs on the rewrite rule.
          egr <- get
          when (cond subst egr) $
             applyMatchesRhs (rw, m)

      (_ := VariablePattern v, Match subst eclass) -> do
          -- rhs is equal to a variable, simply merge class where lhs
          -- pattern was found (@eclass@) and the eclass the pattern
          -- variable matched (@lookup v subst@)
          case IM.lookup v subst of
            Nothing -> error "impossible: couldn't find v in subst"
            Just n  -> do
                _ <- merge eclass n
                return ()

      (_ := NonVariablePattern rhs, Match subst eclass) -> do
          -- rhs is (at the top level) a non-variable pattern, so substitute
          -- all pattern variables in the pattern and create a new e-node (and
          -- e-class that represents it), then merge the e-class of the
          -- substituted rhs with the class that matched the left hand side
          eclass' <- reprPat subst rhs
          _ <- merge eclass eclass'
          return ()

-- | Represent a pattern in the e-graph a pattern given substitions
reprPat :: (Language l, Analysis a l) => Subst -> l (Pattern l) -> EGraphM a l ClassId
reprPat subst = add . Node <=< traverse \case
  VariablePattern v ->
      case IM.lookup v subst of
          Nothing -> error ("impossible: couldn't find v in subst? " <> show v)
          Just i  -> return i
  NonVariablePattern p -> reprPat subst p
{-# INLINEABLE runEqualitySaturation #-}

