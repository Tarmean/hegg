{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant lambda" #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.Equality.Compiler.QueryExecution where
import qualified Data.HashMap.Internal.Strict as HM
import Data.Equality.Compiler.JoinOrder
import Debug.Trace (trace)
import Data.Equality.Compiler.Index
import Data.Equality.Graph (ClassId)
import qualified Data.IntMap as IM
import Control.Applicative (Alternative(empty))
import qualified Data.Equality.Graph as E
import Data.Equality.Matching (Pattern (VariablePattern, NonVariablePattern))
import Data.Equality.Compiler.PlanStep (PId)
import Data.Equality.Compiler.RuleCompilation (egraphConstraints, normalizePattern, _MAGIC_ROOT, _MAGIC_ROOT_INT)
import qualified Data.Set as S
import qualified Data.Equality.Saturation.Rewrites as R
import qualified Data.Equality.Language as L
import qualified Data.Equality.Matching.Database as P
import Control.Monad.State (MonadState (..))
import Control.Monad (void, (<=<))
import qualified Data.Equality.Analysis as A
import Data.Foldable (forM_)
import qualified Data.Vector.Unboxed as VU
import Control.Monad.Writer.CPS
import Data.Traversable (for)
import Data.Equality.Saturation.Scheduler (Score)
import qualified Data.Equality.Saturation.Scheduler as Score
import Data.Vector.Internal.Check (HasCallStack)
import Data.Equality.Compiler.Utils ((!!!))
import qualified Data.IntSet as IS

runRewrites :: forall m ana lang. (MonadState (E.EGraph ana lang) m, L.Language lang, A.Analysis ana lang) => AllTuples lang -> IM.IntMap (R.Rewrite ana lang) -> m (IM.IntMap Score)
runRewrites db rw = do
   let plans = planQueries db rw
   let reqIndices = S.fromList $ concatMap (IM.elems . usedIndexes . snd) (IM.elems plans)
   let indices = buildIndices reqIndices db
   for plans $ \(applyMatch, queryPlan) -> execWriterT $
     forM_ (executeQuery queryPlan indices) (tell <=< applyMatch)

executeQuery :: E.Language f => QueryPlan f -> Indices f -> [P.Subst]
executeQuery (AllClasses is) (Indices ls _) = [IM.fromList [ (var, cid) |var <- IS.toList is ] | cid <- VU.toList ls]
executeQuery query indices = go ixs0 (_queryOrder query) mempty
  where
   ixs0 = IM.map (allIndices indices HM.!) (usedIndexes query)
   -- Each level:
   -- - Iterate over keys from some source, which give us new substitutions
   -- - Lookup those substitutions in all indices which overlap. This moves us one level down in those trees
   -- We dynamically pick the source from the smallest index which covers all needed variables for this level
   go :: IM.IntMap HM -> [StepPlan] -> IM.IntMap ClassId -> [ IM.IntMap ClassId ]
   go _idxs [] subst = pure subst
   go idxs (l:ls) subst = do
      newSubst <- iterKeys (_varMappings query !!! x) (idxs !!! x)
      let
        nextIndexLevel ixKey  = case getHM (_varMappings query !!! ixKey) newSubst (idxs !!! ixKey) of
          Nothing -> Nothing
          Just newIndex -> Just (ixKey,newIndex)
      case traverse nextIndexLevel (VU.toList $ affectedIds l) of
         Just m' -> go (IM.fromList m' <> idxs) ls (newSubst <> subst)
         Nothing -> empty
     where
       x = bestSource l idxs
bestSource :: HasCallStack => StepPlan -> IM.IntMap HM -> Int
bestSource sp indices 
  | VU.null (sourceCandidates sp) = error "bestSource: No source candidates"
  | otherwise = VU.minimumOn (\idx -> hmSize (indices !!! idx)) (sourceCandidates sp)
genQueryPlan :: (E.Language l) => AllTuples l -> [(Pattern l, Pattern l)] -> (VarMap, QueryPlan l)
genQueryPlan db pats
  | null constraints = (varMap, AllClasses (IS.fromList $ IM.elems varMap)) -- Contains no NonVariablePattern
  | otherwise = (varMap, qPlan)
  where
    qPlan = planQuery db constraints
    (constraints, varMap) = egraphConstraints $ normalizePattern pats

data Indices f = Indices{ allClasses :: VU.Vector Int, allIndices :: HM.HashMap (IndexPlan f) HM } 
buildIndices :: E.Language f => S.Set (IndexPlan f) -> AllTuples f -> Indices f
buildIndices s db 
  | trace (show s) False = undefined
  | otherwise = Indices (dbClasses db) $ HM.fromList $ do
   ix <- S.toList s
   pure (ix, buildIndex ix db)




type VarMap = IM.IntMap PId
planQueries :: (MonadState (E.EGraph ana lang) m, L.Language lang, A.Analysis ana lang) => AllTuples lang -> IM.IntMap (R.Rewrite ana lang) -> IM.IntMap (Applier m, QueryPlan lang)
planQueries db = IM.map (toQ [])
  where
    toQ acc (p R.:| cond ) = toQ (cond : acc) p
    toQ acc (lhs R.:= rhs) = (toApplier lhs rhs acc varMap, qp)
      where (varMap, qp) = genQueryPlan db [ (_MAGIC_ROOT, lhs) ]

type Applier m = IM.IntMap ClassId -> m Score
toApplier :: (MonadState (E.EGraph ana lang) m, Monad m, L.Language lang, A.Analysis ana lang) => Pattern lang -> Pattern lang -> [R.RewriteCondition ana lang] -> VarMap -> Applier m
toApplier lhs rhs conditions varToCompact = \compactToClass -> do
    let subst = IM.map (compactToClass !!!) varToCompact
        root = subst !!! _MAGIC_ROOT_INT
    eg <- get
    if and [cond subst eg |cond <- conditions] then do
      -- traceM ("Applying " ++ show root <> "@("<> show (mapPat (subst !!!)lhs)  ++ ") => " ++ show (mapPat (subst !!!)rhs))
      n <- resolveNode (subst !!!) rhs
      void $ state (E.merge root n)
      pure $ Score.fromSubst subst
    else pure mempty

mapPat :: (Functor lang)=> (P.Var -> ClassId) -> Pattern lang -> Pattern lang
mapPat f (VariablePattern i) = VariablePattern (f i)
mapPat f (NonVariablePattern r) = NonVariablePattern (fmap (mapPat f) r)

resolveNode :: (A.Analysis ana lang, E.Language lang, MonadState (E.EGraph ana lang) m)=> (P.Var -> ClassId) -> Pattern lang -> m ClassId
resolveNode f (VariablePattern v) = pure (f v)
resolveNode f (NonVariablePattern v) = state . (E.add . E.Node ) =<< traverse (resolveNode f) v
