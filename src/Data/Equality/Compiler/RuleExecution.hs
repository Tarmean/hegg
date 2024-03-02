{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveTraversable #-}
module Data.Equality.Compiler.RuleExecution where
import qualified Data.Equality.Graph.Internal as Eg
import qualified Data.IntMap.Strict as IM
import Data.Equality.Graph (ClassId, ENode (..), EGraph)
import Data.Equality.Compiler.PlanStep
import Control.Monad.State
import Data.Equality.Compiler.RuleOrdering
import GHC.Stack (HasCallStack)
import Control.Monad (when, forM)
import qualified Data.Set as S
import Data.Kind (Type)
import Data.Foldable (forM_, Foldable (toList))
import qualified Data.Equality.Graph.Nodes as NM
import Data.Equality.Graph.Lens

type VMEnv = IM.IntMap ClassId

type M m = MonadState VMEnv m
getId :: M m => Reg -> m (Maybe ClassId)
getId r = gets (IM.lookup r)
assertGetId :: (M m, HasCallStack) => Reg -> m ClassId
assertGetId r = gets (IM.findWithDefault (error $ "assertGetId unset reg: " <> show r) r)

upsert :: Reg -> ClassId -> IM.IntMap ClassId -> (Bool, IM.IntMap ClassId)
upsert r cl = IM.alterF step r
  where
    step Nothing = (True, Just cl)
    step (Just cr)
      | cl == cr = (True, Just cr)
      | otherwise = (False, Just cr)

unify :: M m => Reg -> ClassId -> m () -> m ()
unify r c cont = do
    old <- get
    let (isValid, new) = upsert r c old
    when isValid $ do
      put new
      cont

getPrefix :: (Traversable f, M m) => Int -> f Reg -> m (f ClassId)
getPrefix prefLen f = flip evalStateT prefLen $
    forM f $ \reg -> get >>= \case
    0 -> pure (-1)
    _ -> modify (subtract 1) >> lift (assertGetId reg)

getPrefixHigh :: Functor f => f Reg -> f Reg
getPrefixHigh = fmap step
  where
    step i
      | i < 0 = maxBound
      | otherwise = i

getSlice :: Ord x => x -> x -> S.Set x -> S.Set x
getSlice low high full = betweenLowHigh
  where
     (_, aboveLow) = S.split low full
     (betweenLowHigh, _) = S.split high aboveLow
data SP ana f = SP VMEnv (EGraph ana f)
newtype VM m ana (f :: Type -> Type) = VM { unVM :: (VMEnv -> m ()) -> StateT VMEnv m () }
instance (MonadState (EGraph ana f) m, Traversable f, Ord (f ClassId)) => VMPlan f (VM m ana f) where
    searchSpan prefLen root pat cont = VM $ \fin -> do
      rid <- assertGetId root
      prefix <- getPrefix prefLen pat
      candidates <- lift $ gets (^._class rid . _nodes)
      let
          -- rebuilding a set just to stream it is a bit wasteful, could be faster with intmap internals
          slice = getSlice (Node prefix) (Node $ getPrefixHigh prefix) candidates
      let patList = drop prefLen $ toList pat
      forM_ slice $ \match -> do
          let
            matchList = drop prefLen $ toList (unNode match)
          foldr (uncurry unify) (unVM cont fin) (zip matchList patList)
    scanClasses reg cont = VM $ \fin -> do
        eg <- lift (gets Eg.classes)
        forM_ (IM.keys eg) $ \k -> unify reg k (unVM cont fin)
    lookupHash pat reg cont = VM $ \fin ->  do
        node <- traverse assertGetId pat
        memo <- lift $ gets (^._memo)
        case NM.lookupNM (Node node) memo of
          Nothing -> pure ()
          Just match -> unify reg match (unVM cont fin)
    yieldOut = VM $ \fin ->  do
       s <- get
       lift $ fin s

data VmAst f = SearchSpan Int Int (f Int) (VmAst f)
    | ScanClasses Int (VmAst f)
    | LookupHash (f Int) Int (VmAst f)
    | YieldOut
    | Done
deriving instance (Show (f Int)) => Show (VmAst f)
deriving instance (Eq (f Int)) => Eq (VmAst f)
deriving instance (Ord (f Int)) => Ord (VmAst f)
instance VMPlan f (VmAst f) where
    searchSpan = SearchSpan
    scanClasses = ScanClasses
    lookupHash = LookupHash
    yieldOut = YieldOut

data FExpr a = Plus a a | Const String | Tuple [a]
  deriving (Eq, Ord, Show, Traversable, Foldable, Functor)
test,test2 :: VmAst FExpr
test = greedyPlan (S.fromList [0 := Const "1",  3 := Plus 0 1, 3 := Const "1"])
test2 = greedyPlan (S.fromList [0 := Tuple [1,5,3], 1 := Tuple [1,2,4], 4 := Tuple [1,2]])
-- >>> test
