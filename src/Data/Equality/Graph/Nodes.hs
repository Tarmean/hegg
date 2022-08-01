{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveTraversable #-}
{-|

Definition of e-nodes, instances and some operations on them.

Additionally, defines the 'Operator' of an e-node as the language functor
parametrised over @()@.

-}
module Data.Equality.Graph.Nodes where

import Data.Functor.Classes
import Data.Foldable

import Data.Kind

import Data.Hashable
import Data.Hashable.Lifted

import Control.Monad (void)

import qualified Data.HashMap.Strict as HMS

import Data.Equality.Graph.Classes.Id

-- | E-node
--
-- An E-node is a function symbol paired with a list of children e-classes.
-- 
-- We define an e-node to be the base functor of some recursive data type
-- parametrized over ClassId, i.e. all recursive fields are rather e-class ids.
--
-- When @l@ is an expression-like data type, @ENode l = l ClassId@ means every
-- recursive field (so, every argument passed to this expr) is a 'ClassId'
-- rather than an explicit expression
newtype ENode l = Node { unNode :: l ClassId }

hashNode :: Hashable1 l => ENode l -> Int
hashNode = hash
{-# INLINE hashNode #-}

-- | Operator
--
-- An operator is solely the function symbol part of the e-node, that is,
-- children e-classes are ignored.
newtype Operator l = Operator { unOperator :: l () }

-- | Get the children class ids of an e-node
children :: Traversable l => ENode l -> [ClassId]
children = toList . unNode
{-# INLINE children #-}

-- | Get the operator (function symbol) of an e-node
operator :: Traversable l => ENode l -> Operator l
operator = Operator . void . unNode
{-# INLINE operator #-}

instance Eq1 l => (Eq (ENode l)) where
    (==) (Node a) (Node b) = liftEq (==) a b
    {-# INLINE (==) #-}

instance Ord1 l => (Ord (ENode l)) where
    compare (Node a) (Node b) = liftCompare compare a b
    {-# INLINE compare #-}

instance Show1 l => (Show (ENode l)) where
    showsPrec p (Node l) = liftShowsPrec showsPrec showList p l

instance Hashable1 l => Hashable (ENode l) where
  hashWithSalt i (Node l) = liftHashWithSalt hashWithSalt i l
  {-# INLINE hashWithSalt #-}

instance Eq1 l => (Eq (Operator l)) where
    (==) (Operator a) (Operator b) = liftEq (\_ _ -> True) a b
    {-# INLINE (==) #-}

instance Ord1 l => (Ord (Operator l)) where
    compare (Operator a) (Operator b) = liftCompare (\_ _ -> EQ) a b
    {-# INLINE compare #-}

instance Show1 l => (Show (Operator l)) where
    showsPrec p (Operator l) = liftShowsPrec (const . const $ showString "") (const $ showString "") p l

-- * Node Map

data NodeMap (l :: Type -> Type) a = NodeMap { unNodeMap :: HMS.HashMap (ENode l) a, sizeNodeMap :: {-# UNPACK #-} !Int }
  deriving (Show, Functor, Foldable, Traversable)

instance (Eq1 l, Hashable1 l) => Semigroup (NodeMap l a) where
  NodeMap m1 s1 <> NodeMap m2 s2 = NodeMap (m1 <> m2) (s1 + s2)

instance (Eq1 l, Hashable1 l) => Monoid (NodeMap l a) where
  mempty = NodeMap mempty 0



insertNM :: Hashable1 l => ENode l -> a -> NodeMap l a -> NodeMap l a
insertNM e v (NodeMap m s) = NodeMap (HMS.insert e v m) (s+1)
{-# SCC insertNM #-}

lookupNM :: Hashable1 l => ENode l -> NodeMap l a -> Maybe a
lookupNM e = HMS.lookup e . unNodeMap
{-# SCC lookupNM #-}

deleteNM :: Hashable1 l => ENode l -> NodeMap l a -> NodeMap l a
deleteNM e (NodeMap m s) = NodeMap (HMS.delete e m) (s-1)
{-# SCC deleteNM #-}

insertLookupNM :: Hashable1 l => ENode l -> a -> NodeMap l a -> (Maybe a, NodeMap l a)
insertLookupNM e v (NodeMap m s) = (HMS.lookup e m, NodeMap (HMS.insert e v m) (s+1))
{-# SCC insertLookupNM #-}

foldlWithKeyNM' :: Hashable1 l => (b -> ENode l -> a -> b) -> b -> NodeMap l a -> b 
foldlWithKeyNM' f b = HMS.foldlWithKey' f b . unNodeMap
{-# SCC foldlWithKeyNM' #-}

foldrWithKeyNM' :: Hashable1 l => (ENode l -> a -> b -> b) -> b -> NodeMap l a -> b 
foldrWithKeyNM' f b = HMS.foldrWithKey' f b . unNodeMap
{-# SCC foldrWithKeyNM' #-}

sizeNM :: NodeMap l a -> Int
sizeNM = sizeNodeMap
{-# INLINE sizeNM #-}

traverseWithKeyNM :: Applicative t => (ENode l -> a -> t b) -> NodeMap l a -> t (NodeMap l b) 
traverseWithKeyNM f (NodeMap m s) = (`NodeMap` s) <$> HMS.traverseWithKey f m
{-# SCC traverseWithKeyNM #-}

-- * Node Set

-- newtype NodeSet l a = NodeSet { unNodeSet :: IM.IntMap (a, ENode l) }
--   deriving (Semigroup, Monoid)

-- insertNS :: Hashable1 l => ENode l -> NodeSet l -> NodeSet l
-- insertNS v = NodeSet . IM.insert (hashNode v) v . unNodeSet
