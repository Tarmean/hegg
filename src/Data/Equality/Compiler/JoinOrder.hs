
{- Join plan:
  E-Matching is a select-project-join SQL query so we gotta do basic query optimization for performance.
  We are an in-memory DB so hash joins would make sense. Previous work advocated generic joins, so this implements Free Joins which generalize both! We flatten a query
 
      f(h(?A), h(?B), ?A)
 
  into an egraph:
 
      3 := Var("A")
      0 := f(1,2,3)
      1 := h(3)
      4 := Var("B")
      2 := h(4)

 
  This gives us three constraints and two variable mappings.
 
  For Constraints we flatten classid and arguments into flat tuples:
  - X: f[0,1,2,3]
  - Y: h[1,3]
  - Z: h[2,4]
  Var Mappings: {3: "A", 4: "B", 0: "$root"}
 
  We split the constraints into a sequence which yields indices. E.g. if the sequence is:
 
  [[1,2], [3], [0], [4]]
 
  This would give the Indices:
  - X: HashMap (Idx1, Idx2) (HashMap Idx3 (HashMap Idx0 ()))
  - Y: HashMap Idx1 (HashMap Idx3 ())
  - Z: HashMap Idx2 (HashMap Idx4 ())
  and code (? skips current loop iteration on missing map entry):
 
  for (v1, v2) in idxX.keys():
      let idxX = idxX.get((v1,v2))?
      let idxY = idxY.get((v1))?
      let idxZ = idxY.get((v2))?
      -- here we can dynamically loop over the smaller index
      for (v3) in [idxX,idxY].minimum().keys():
        let idxX = idxX.get((v3))?
        let idxY = idxY.get((v3))?
        for v0 in idxX.keys():
          let idxX = idxX.get((v0))?
          for v4 in idxZ.keys():
            let idxZ = idxZ.get((v4))?
            yield {"A": v3, "B": v4, "$root": v0} 

Depending on the sequence and indexes we can do either hash joins, generic joins, or something in between.(:*:)

This would mean building multiple indices for each query!!!!!
To amortize this, we try to always use the same join order (naively smallest relation first) and share indices for all rewrite rules to amortize.
 -}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
module Data.Equality.Compiler.JoinOrder where
import Data.Equality.Compiler.Index
import Data.Equality.Compiler.PlanStep
import qualified Data.Equality.Graph as E
import Data.Foldable (minimumBy, toList)
import Data.Ord (comparing)
import qualified Data.IntSet as IS
import qualified Data.Vector as V
import qualified Data.IntMap as IM
import qualified Data.Set as S
import qualified Data.Map as M
import qualified Data.Vector.Unboxed as VU
import GHC.Generics (Generic)
import Data.Hashable (Hashable)
import GHC.Stack (HasCallStack)
import Data.Equality.Compiler.Utils ((!!!))

planQuery :: (E.Language f) => AllTuples f -> [Constraint f PId] -> QueryPlan f
planQuery tupleData cstrs
  | null metas = error ("Null metadata " <> show (cstrs, metas))
  | otherwise = toQueryPlan (IM.map varBinding metas) $ toSlices $ getQueryOrder metas
  where metas = metadatas tupleData cstrs

ruleSize :: (E.Language f) => AllTuples f -> Constraint f PId -> Int
ruleSize at (_ := cstr) = storageSize $ lookupStorage (E.operator $ E.Node cstr) at

smallestChoice :: (HasCallStack, E.Language f) => [ Metadata f ] -> Metadata f
smallestChoice [] = error "Nullary join, no constraints"
smallestChoice xs = minimumBy (comparing tableSize) xs

data Metadata f = Metadata { constraintId :: Int, theConstraint :: Constraint f PId, tableSize :: Int, usedSet :: IS.IntSet }
deriving instance Eq (f Int) => Eq (Metadata f)
deriving instance Ord (f Int) => Ord (Metadata f)
deriving instance Show (f Int) => Show (Metadata f)
toMetadata :: E.Language f => AllTuples f -> Constraint f PId -> Int -> Metadata f
toMetadata storage constraint constrId  = Metadata constrId constraint (ruleSize storage constraint) (learnedVars constraint)
isCovered :: IS.IntSet -> Metadata f -> Bool
isCovered seen m = IS.null (usedSet m `IS.difference` seen)
isReachable :: IS.IntSet -> Metadata f -> Bool
isReachable l r = not $ IS.null (l `IS.intersection` usedSet r )

data Slice f = Slice { sliceConstraint :: Metadata f, selectedVars :: IS.IntSet }
deriving instance Eq (f Int) => Eq (Slice f)
deriving instance Ord (f Int) => Ord (Slice f)
deriving instance Show (f Int) => Show (Slice f)

getQueryOrder :: forall f. (E.Language f) => IM.IntMap (Metadata f) -> [Metadata f]
getQueryOrder im0 = useNext (smallestChoice (IM.elems im0)) mempty mempty im0
  where
    useNext m q seen im = go (m:q) (IS.union (learnedVars (theConstraint m)) seen) (IM.delete (constraintId m) im)
    go q learned missing
      | IM.null missing = reverse q
      | otherwise = useNext (smallestChoice $ IM.elems missing :: Metadata f) q learned missing

byContent :: Ord (f Int) => [Metadata f] -> IM.IntMap (S.Set (Metadata f))
byContent ls = IM.fromListWith (<>) [ (lv, S.singleton l) | l <- ls, lv <- IS.toList (usedSet l) ]
toSlices :: Ord (f Int) => [Metadata f] -> [ [ Slice f ]]
toSlices [] = []
toSlices md
  -- TODO: Splitting the first slice if it is very large could help, moving from hashjoin into generic join
 -- | firstLarge && isSplittable = slice 
  = go md mempty
  where
    by = byContent md
    go (x:xs) seen
      | not(IS.null newVars) = slicesFor newVars : go xs (IS.union seen newVars)
      | otherwise = go xs seen
      where
        newVars = usedSet x `IS.difference` seen
    go [] _seen = []
    slicesFor newVars = map (slice newVars) (S.toList new)
      where
        new = foldMap (by !!!)  (IS.toList newVars)
    slice newVars x = Slice x (usedSet x `IS.intersection` newVars)


newtype RelevantConstraintIds = RelevantConstraintIds(VU.Vector Int) 
  deriving (Eq, Ord, Show)
  deriving Hashable via TupleSlice


relevantIds :: RelevantConstraintIds -> [Int]
relevantIds (RelevantConstraintIds v) = VU.toList v
data IndexPlan f = IPlan{ filtering :: FilterSet,
  operand :: E.Operator f, plan :: [RelevantConstraintIds]}
    deriving (Generic)
deriving instance E.Language f => Eq (IndexPlan f)
deriving instance E.Language f => Ord (IndexPlan f)
instance E.Language f => Hashable (IndexPlan f)
deriving instance (Show (f ()))=> Show(IndexPlan f)
instance Eq (f ()) => Semigroup (IndexPlan f) where
   IPlan filL a x <> IPlan filR b y
     | filL == filR && a == b =IPlan filL a (x <> y)
     | otherwise = error "Illegal indexplan merge"
getIndexes :: (E.Language f) => [ [ Slice f ] ] -> IM.IntMap (IndexPlan f)
getIndexes ls =  IM.fromListWith (flip (<>)) $ do
  ss<- ls
  s <- ss
  pure (constraintId $ sliceConstraint s, IPlan (constraintFilters $ theConstraint $ sliceConstraint s) (constraintOperator $ theConstraint $ sliceConstraint s) [selectedIdx s])

constraintFilters :: Foldable f => Constraint f PId -> FilterSet
constraintFilters cstr = FilterSet $ V.fromList $ filter (\s -> IS.size s > 1) $ M.elems m
  where
    m = M.fromListWith (<>) $ zip (toList cstr) (fmap IS.singleton [0..])

selectedIdx :: Foldable f => Slice f -> RelevantConstraintIds
selectedIdx s = RelevantConstraintIds $ VU.fromList $ IS.toAscList $ IS.map (vars !!!) (selectedVars s)
  where
    vars = IM.fromListWith (\ _ x -> x) $ zip (toList $ theConstraint $ sliceConstraint s) [0..]


metadatas :: E.Language f => AllTuples f -> [Constraint f PId] -> IM.IntMap (Metadata f)
metadatas allT = IM.fromList . zipWith f [0..] . fmap (toMetadata allT)
  where f i m = (i, m i)

-- | Map from constraintId to var binding
type VarBindings = IM.IntMap (Permutation ColumnSet VarSet)
data QueryPlan f = QPlan { _usedIndexes :: IM.IntMap (IndexPlan f), _varMappings :: VarBindings, _queryOrder :: [ StepPlan ] } | AllClasses IS.IntSet
usedIndexes :: QueryPlan f -> IM.IntMap (IndexPlan f)
usedIndexes (AllClasses{} ) = mempty
usedIndexes qp = _usedIndexes qp
deriving instance (Show (f ()))=> Show(QueryPlan f)
-- | At each step we iterate over the keys in one index and then get the nested index for each relevant index
-- sourceCandidates are a cover for the current step, i.e. yield ever variable we need 
-- affectedIds are contain some variable bound in the current step (and ever source candidate is also in affectedIds)
data StepPlan
    = StepPlan { sourceCandidates :: VU.Vector Int,
    affectedIds :: VU.Vector Int}
    deriving (Show)
toStepPlan :: [ Slice f ] -> StepPlan
toStepPlan s = StepPlan covering affected
  where
    allVars = foldMap selectedVars s
    covering = VU.fromList $ map (constraintId . sliceConstraint) $ filter (\r -> allVars == selectedVars r) s
    affected = VU.fromList $ map (constraintId . sliceConstraint) s

toQueryPlan :: E.Language f => VarBindings -> [[ Slice f ]] -> QueryPlan f
toQueryPlan varBindings slices = QPlan indexes varBindings vars
  where
    indexes = getIndexes slices
    vars = fmap toStepPlan slices

varBinding :: Foldable f => Metadata f -> Permutation ColumnSet VarSet
varBinding = Permutation . VU.fromList . toList . theConstraint


buildIndex :: (E.Language f) => IndexPlan f -> AllTuples f -> HM
buildIndex ip db = groupStorage (ColumnSet . VU.fromList . relevantIds <$> plan ip) (filtered base)
  where
   base = lookupStorage (operand ip) db
   filtered
     | V.null (unFilterSet $ filtering ip) = id
     | otherwise = filterStorage (filtering ip)
