{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
module Data.Equality.Compiler.RuleCompilation where
import qualified Data.Equality.Graph.Internal as Eg
import qualified Data.Equality.Graph as E
import Data.Equality.Compiler.PlanStep (PId, Constraint)
import qualified Data.Equality.Compiler.PlanStep as C
import qualified Data.IntMap as IM
import Data.Equality.Matching.Database (Var)
import Data.Equality.Matching.Pattern
import Data.Equality.Graph.Internal
import qualified Data.Set as S
import Data.Equality.Graph (eClassNodes, ENode (..))
import Control.Monad.State.Strict
import Data.Monoid (Endo(..))
import Data.Bifunctor (first)
import Data.Hashable (Hashable)
import GHC.Generics (Generic)
import Data.Foldable (forM_)


_MAGIC_ROOT :: Pattern l
_MAGIC_ROOT = "magic_pat_root"
_MAGIC_ROOT_INT :: Int
_MAGIC_ROOT_INT = case _MAGIC_ROOT of
  VariablePattern p -> p
  _ -> error "Impossible"


normalizePattern :: forall lang. (E.Language lang) => [(Pattern lang, Pattern lang)] -> EGraph () (OrVar lang)
normalizePattern pats = E.rebuild $ flip execState  E.emptyEGraph $ do
    forM_ pats $ \(l,r) -> do
        a <- go l
        b <- go r
        state (E.merge a b)
  where
    go (VariablePattern v) = state $ E.add (Node (AVar @lang @PId v))
    go (NonVariablePattern e) = state . E.add . Node . ALang  =<< traverse go e

egraphConstraints :: EGraph ana (OrVar lang) -> ([Constraint lang PId], IM.IntMap PId)
egraphConstraints eg = first (`appEndo` []) $ mconcat $ do
   (pid, nodes) <- IM.toList (Eg.classes eg)
   Node nod <- S.toList (eClassNodes nodes)
   case nod of
     AVar var -> pure (mempty, IM.singleton var pid)
     ALang expr -> pure (Endo (pid C.:= expr:), mempty)

data OrVar f a = AVar Var | ALang (f a)
  deriving (Eq, Ord, Show, Traversable, Foldable, Functor, Hashable, Generic)
