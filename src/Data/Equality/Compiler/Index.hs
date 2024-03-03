{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
module Data.Equality.Compiler.Index where
import qualified Data.Vector.Unboxed as VU
import GHC.Stack (HasCallStack)
import qualified Data.HashMap.Lazy as HM
import qualified Data.Equality.Graph as E
import qualified Data.Foldable as F
import qualified Data.Set as S
import qualified Data.IntMap as IM
import GHC.Base (build)
import Data.Coerce (coerce, Coercible)
import Data.Hashable (Hashable (hashWithSalt))
import qualified Data.IntSet as IS
import qualified Data.Vector as V
import Data.Kind (Type)
import Data.Equality.Compiler.PlanStep (FilterSet (..))



newtype Tuple = Tuple {unTuple :: VU.Vector TupleId}
  deriving (Eq, Ord, Show)
newtype TupleSlice = TupleSlice { unTupleSlice :: VU.Vector TupleId}
  deriving (Eq, Ord, Show)
instance Hashable TupleSlice where
  hashWithSalt salt (TupleSlice sl) = hashWithSalt salt (VU.toList sl)
newtype Columns = Columns (VU.Vector TupleId)
  deriving (Eq, Ord, Show)
type RelationId = Int
type TupleId = Int
type ColumnId = Int

data Storage = Storage {
   tuples :: {-# UNPACK #-}!(VU.Vector TupleId),
   tupleSize :: !Int
}
  deriving (Eq, Ord)
instance Show Storage where
   show = ("Storage.fromList"<> ) . show . iterAll
storageSize :: Storage -> Int
storageSize st = VU.length (tuples st) `div` tupleSize st
lookupTuple :: HasCallStack => Int -> Storage -> Tuple
lookupTuple idx s = Tuple (VU.slice left (tupleSize s) (tuples s))
  where
    left = idx * tupleSize s
iterAll :: Storage -> [Tuple]
iterAll (Storage s siz) = build $ \cons nil -> 
  let
    len = VU.length s
    go i
      | i >= len = nil
      | otherwise = cons (Tuple (VU.slice i siz s)) (go (i+siz))
   in go 0

filterTuple :: FilterSet -> Tuple -> Bool
filterTuple vecs t = and $ do
    v <- V.toList (unFilterSet vecs)
    pure $ allEqual (IS.toList v)
  where
    allEqual (x:xs) = all (\o -> tix x == tix o) xs
    allEqual [] = error "Empty tuple set in filterTuple"
    tix i = unTuple t VU.! i
filterStorage :: FilterSet -> Storage -> Storage
filterStorage vecs s = Storage (VU.concat $ coerce $ filter (filterTuple vecs) $ iterAll s) (tupleSize s)

data AllTuples f = AllTuples {
   dbTuples :: HM.HashMap (E.Operator f) Storage,
   dbClasses :: VU.Vector Int
}
deriving instance (Show (f ())) => Show (AllTuples f)
toAllTuples :: (E.Language lang) => E.ClassIdMap (E.EClass ana lang) -> AllTuples lang
toAllTuples ec = flip AllTuples (VU.fromList $ IM.keys ec) $ HM.mapWithKey toStorage $ HM.fromListWith (<>) $ do
    (cid, cls) <- IM.toList ec
    f <- S.toList (E.eClassNodes cls)
    pure (E.operator f, [ VU.fromList (cid : F.toList (E.unNode f)) ])
    where
      toStorage (E.Operator k) v = Storage (VU.concat v) (length k + 1)
lookupStorage :: E.Language f => E.Operator f -> AllTuples f -> Storage
lookupStorage eop (AllTuples m _) = case HM.lookup eop m of
    Nothing -> Storage mempty 1
    Just x -> x

newtype Permutation (a::Type) (b::Type) = Permutation (VU.Vector Int)
  deriving (Eq, Ord, Show)
appPerm :: (Coercible a (VU.Vector Int),Coercible (VU.Vector Int) b) => Permutation a b -> a -> b
appPerm (Permutation p) a = coerce $ VU.backpermute p  (coerce a)


newtype ColumnSet = ColumnSet { unColumnSet :: VU.Vector Int}
  deriving (Eq, Ord, Show)
newtype VarSet = VarSet { unVarSet :: VU.Vector Int}
  deriving (Eq, Ord, Show)

-- FIXME!!!: These indexes could be polymorphic typeclass dicts.
-- We really only need the basic iter+lookup operations.
-- - For leafs, iter doesn't need the hashmap grouping (except for deduping maybe) and can be implemented with a simple vector 
-- - We often have query plans [[0],[1],[2]] and [[0],[1,2]]. We could only build the first and implement lookup/iteration on top of it
-- - We may want to extend to e.g. b-trees at some point, where "get" encodes a range query
-- - For seminaive evaluation we may want to encode lazy union where getHM perm a (x,y) = (getHM perm a x, getHM perm a y), iterKeys perm var (x,y) = iterKeys perm var x <> iterKeys perm var y
data HM = HM {
    -- flatStorage :: Storage,
    groupedChildren :: HM.HashMap TupleSlice HM,
    columnSet :: !ColumnSet
}
  deriving (Eq, Ord, Show)

-- | Could avoid building the hashmap for leaf nodes which dont have duplicate keys
iterKeys :: Permutation ColumnSet VarSet -> HM -> [ IM.IntMap E.ClassId ]
iterKeys perm hm = do
    let varSet = appPerm perm (columnSet hm)
    k <- HM.keys (groupedChildren hm)
    pure $ IM.fromList $ VU.toList $ VU.zipWith (,) (unVarSet varSet) (unTupleSlice k)

getHM :: Permutation ColumnSet VarSet -> IM.IntMap E.ClassId -> HM -> Maybe HM
getHM perm vars hm = HM.lookup vec (groupedChildren hm)
  where
    vec = TupleSlice $ VU.map (vars IM.!) $ unVarSet (appPerm perm (columnSet hm))

-- | FIXME: Computing the hashmap for iteration/size is pretty inefficient, it is like an extra distinct in SQL
-- | We could avoid this by using a different data structure for leaf nodes
hmSize :: HM -> Int
hmSize = HM.size . groupedChildren

-- | FIXME!!!!: This probably is the most performance sensitive piece
-- in the query code and it concats lists atm
-- Do this with unboxed mutable hashmaps from vector-hashtables. Still requires mutable vecs, grow-vector?
groupChildren :: Storage -> ColumnSet -> (Storage -> HM) -> HM.HashMap TupleSlice HM
groupChildren stor columns cont = HM.map (cont . toStorage) $ HM.fromListWith (<>) $ do
    let keyGetter = pickSlice columns
    slice <- iterAll stor
    pure (keyGetter slice, [slice])
  where toStorage ls = Storage (VU.concat (coerce ls)) (tupleSize stor)

groupStorage :: [ColumnSet] ->  Storage -> HM
groupStorage (x:xs) stor = HM nested x 
  where
    nested = groupChildren stor x (groupStorage xs)
groupStorage [] _stor = HM mempty (ColumnSet VU.empty) 

pickSlice :: ColumnSet -> Tuple -> TupleSlice
pickSlice (ColumnSet cs) (Tuple tup) = TupleSlice (VU.backpermute tup cs)



-- allTuplesTest :: AllTuples []
-- allTuplesTest = AllTuples (HM.fromList [(l 2, Storage (VU.fromList [0,1,2,3,4,5]) 3), (l 3, Storage (VU.fromList [0,1,2,3,4,5]) 3)])
-- l i = E.Operator $ replicate i ()
-- testIndex = groupStorage  (fmap (ColumnSet . VU.fromList ) [[1], [0 ,2]]) (lookupStorage (l 3 ) allTuplesTest)
