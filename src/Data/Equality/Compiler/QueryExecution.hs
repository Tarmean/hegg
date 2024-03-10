{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant lambda" #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.Equality.Compiler.QueryExecution where
import qualified Data.HashMap.Internal.Strict as HM
import Data.Equality.Compiler.JoinOrder
import Data.Equality.Compiler.Index
import Data.Equality.Graph (ClassId)
import qualified Data.IntMap as IM
import Control.Applicative (Alternative(empty))
import qualified Data.Equality.Graph as E
import Data.Equality.Matching (Pattern (VariablePattern, NonVariablePattern))
import Data.Equality.Compiler.PlanStep (PId)
import Data.Equality.Compiler.RuleCompilation (egraphConstraints, normalizePattern)
import qualified Data.Set as S
import qualified Data.Equality.Language as L
import qualified Data.Equality.Matching.Database as P
import Control.Monad.State (MonadState (..))
import qualified Data.Equality.Analysis as A
import qualified Data.Vector.Unboxed as VU
import Data.Traversable (for)
import Data.Equality.Saturation.Scheduler (Score)
import Data.Vector.Internal.Check (HasCallStack)
import Data.Equality.Compiler.Utils ((!!!))
import qualified Data.IntSet as IS
import qualified Data.Equality.Compiler.API as API
import Debug.Trace (traceM)
import Data.Semigroup (Endo(..))
import Control.Monad.Writer.CPS
import Control.Monad (forM_)
import Data.Functor.Identity

{-# INLINE runRewrites #-}
runRewrites :: forall lang . (L.Language lang) => AllTuples lang -> IM.IntMap [ API.Equation lang ] -> (IM.IntMap [ P.Subst ])
runRewrites db rw = 
   runIdentity $ runRewritesM db rw write getAll 
  where
   write _ x = tell (Endo (x:))
getAll :: (Monoid r, Monad m) => WriterT (Endo r) m () -> m r
getAll = fmap (flip appEndo mempty) . execWriterT

{-# INLINE runRewritesM_ #-}
runRewritesM_ :: (Monoid r, Monad m, L.Language lang) => AllTuples lang -> IM.IntMap [ API.Equation lang ] -> IM.IntMap (P.Subst -> m r) -> m (IM.IntMap r)
runRewritesM_ db rw conts = runRewritesM db rw app execWriterT
  where
    app idx v = tell =<< lift ((conts IM.! idx) v)

{-# INLINE runRewritesM #-}
runRewritesM :: (Monad m, Monad n, L.Language lang) => AllTuples lang -> IM.IntMap [ API.Equation lang ] -> (Int -> P.Subst -> m ()) -> (m () -> n r) -> n (IM.IntMap r)
runRewritesM db rw cont finalize =
   flip IM.traverseWithKey plans $ \k (toPat, queryPlan) ->
     finalize $
       forM_ (executeQuery queryPlan indices) (cont k . toPat)
  where
   plans = planQueries db rw
   reqIndices = S.fromList $ concatMap (IM.elems . usedIndexes . snd) (IM.elems plans)
   indices = buildIndices reqIndices db


{-# INLINABLE executeQuery #-}
executeQuery :: E.Language f => QueryPlan f -> Indices f -> [P.Subst]
executeQuery (AllClasses is) (Indices ls _) = [IM.fromList [ (var, cid) |var <- IS.toList is ] | cid <- VU.toList ls]
executeQuery query indices = go indexRoots (_queryOrder query) mempty
  where
   indexRoots = IM.map (allIndices indices HM.!) (usedIndexes query)
   idToVarOrder ixId = _varMappings query  !!! ixId
   -- Each level:
   -- - Iterate over keys from some source, which give us new substitutions
   -- - Lookup those substitutions in all indices which overlap. This moves us one level down in those trees
   -- We dynamically pick the source from the smallest index which covers all needed variables for this level
   go :: IM.IntMap HM -> [StepPlan] -> IM.IntMap ClassId -> [ IM.IntMap ClassId ]
   go _ [] subst = pure subst
   go indexes (step:steps) subst = do
      let
        idToIndex ixId = indexes !!! ixId
        indexChild key ixId  = case getIndex (idToVarOrder ixId) key (idToIndex ixId) of
          Nothing -> Nothing
          Just newIndex -> Just (ixId,newIndex)

        nextIndexId = bestSource step indexes

      newSubst <- iterKeys (idToVarOrder nextIndexId) (idToIndex nextIndexId)

      case traverse (indexChild newSubst) (VU.toList $ affectedIds step) of
         Just indexes' -> go (IM.fromList indexes' <> indexes) steps (newSubst <> subst)
         Nothing -> empty
bestSource :: HasCallStack => StepPlan -> IM.IntMap HM -> Int
bestSource sp indices
  | VU.null (sourceCandidates sp) = error "bestSource: No source candidates"
  | otherwise = VU.minimumOn (\idx -> indexSize (indices !!! idx)) (sourceCandidates sp)
genQueryPlan :: (E.Language l) => AllTuples l -> [API.Equation l] -> (VarMap, QueryPlan l)
genQueryPlan db pats
  | null constraints = (varMap, AllClasses (IS.fromList $ IM.elems varMap)) -- Contains no NonVariablePattern
  | otherwise = (varMap, qPlan)
  where
    qPlan = planQuery db constraints
    (constraints, varMap) = egraphConstraints $ normalizePattern [ (l,r) | API.Equation l r <- pats ]

data Indices f = Indices{ allClasses :: VU.Vector Int, allIndices :: HM.HashMap (IndexPlan f) HM }
buildIndices :: E.Language f => S.Set (IndexPlan f) -> AllTuples f -> Indices f
buildIndices s db = Indices (dbClasses db) $ HM.fromList $ do
   ix <- S.toList s
   pure (ix, buildIndex ix db)




type VarMap = IM.IntMap PId
{-# INLINABLE planQueries #-}
planQueries :: (L.Language lang) => AllTuples lang -> IM.IntMap [ API.Equation lang ] -> IM.IntMap (IM.IntMap PId -> P.Subst, QueryPlan lang)
planQueries db = IM.map toQ
  where
    toQ rule = (\m -> IM.map (m!!!) varMap, queryPlan)
      where
         (varMap, queryPlan) = genQueryPlan db rule


type Applier m = IM.IntMap ClassId -> m Score
-- {-# INLINABLE toApplier #-}
-- toApplier :: (MonadState (E.EGraph ana lang) m, Monad m, L.Language lang, A.Analysis ana lang) => (P.Subst -> m Score) -> VarMap -> Applier m
-- toApplier app varToCompact = \compactToClass -> do
    -- let subst = IM.map (compactToClass !!!) varToCompact
--     _ <- app subst -- FIXME: old implementation scores before filtering, but maybe we want to hoist filters up the query tree?
--     let score = fromSubst subst
--     pure score

{-# INLINABLE mapPat #-}
mapPat :: (Functor lang)=> (P.Var -> ClassId) -> Pattern lang -> Pattern lang
mapPat f (VariablePattern i) = VariablePattern (f i)
mapPat f (NonVariablePattern r) = NonVariablePattern (fmap (mapPat f) r)


