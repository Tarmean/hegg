{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveFoldable #-}
module Data.Equality.Compiler.PlanStep  where

import Data.Foldable (toList)
import qualified Data.IntSet as IS
import qualified Data.Equality.Graph.Nodes as E
import qualified Data.Vector as V
import Data.Hashable
type PId = Int
data Constraint f x = x := f x
  deriving (Eq, Show, Ord, Foldable)

learnedVars :: Foldable f => Constraint f PId -> IS.IntSet
learnedVars ls = IS.fromList (toList ls)
constraintOperator :: Traversable f => Constraint f PId -> E.Operator f
constraintOperator (_ := r) = E.operator (E.Node r)

newtype FilterSet = FilterSet { unFilterSet :: V.Vector IS.IntSet}
  deriving (Eq, Ord, Show)
instance Hashable FilterSet where
   hashWithSalt salt (FilterSet ls) = hashWithSalt salt (V.toList ls)
