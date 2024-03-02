{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TypeApplications #-}
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

egraphConstraints :: EGraph ana (OrVar lang) -> ([Constraint lang PId], IM.IntMap Var)
egraphConstraints eg = first (`appEndo` []) $ mconcat $ do
   (cls, nodes) <- IM.toList (Eg.classes eg)
   Node nod <- S.toList (eClassNodes nodes)
   case nod of
     AVar var -> pure (mempty, IM.singleton cls var)
     ALang expr -> pure (Endo (cls C.:= expr:), mempty)


data OrVar f a = AVar Var | ALang (f a)
  deriving (Eq, Ord, Show, Traversable, Foldable, Functor)

normalizeRewrite :: forall lang. (E.Language lang) => Pattern lang -> Pattern lang -> EGraph () (OrVar lang)
normalizeRewrite l r = E.rebuild $ execState (go l *> go r) E.emptyEGraph
  where
  go (VariablePattern v) = state $ E.add (Node (AVar @lang @PId v))
  go (NonVariablePattern e) = state . E.add . Node . ALang  =<< traverse go e

