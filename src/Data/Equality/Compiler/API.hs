{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MonoLocalBinds #-}
module Data.Equality.Compiler.API where
import qualified Data.Equality.Matching.Database as R
import Control.Monad.State
import qualified Data.Equality.Graph as E
import qualified Data.Equality.Matching as P
import Data.Equality.Saturation (RewriteCondition)
import Control.Monad (when)
import Data.Equality.Compiler.QueryExecution (resolveNode, resolveNode)
import qualified Data.IntMap as IM
import qualified Data.Equality.Analysis as A
import Data.Hashable (Hashable)
import Data.Equality.Compiler.RuleCompilation (_MAGIC_ROOT)
import qualified Data.Equality.Graph.Monad as EM
import Data.Functor (void)



data Equation f = Equation (P.Pattern f) (P.Pattern f)
deriving instance (forall a. Eq (f a)) => Eq (Equation f)
deriving instance (forall a. Show (f a)) => Show (Equation f)
deriving instance (forall a. Ord (f a)) => Ord (Equation f)
(.=) :: P.Pattern f -> P.Pattern f -> Equation f
(.=) = Equation
data Rule f m = Rule { ruleLhs :: [Equation f], ruleRhs :: R.Subst -> m () }
type OnMatch m = R.Subst -> m ()

(.|) :: (MonadState (E.EGraph ana lang) m) => OnMatch m -> RewriteCondition ana lang -> OnMatch m
(.|) onMatch cond subst = do
   eg <- get
   when (cond subst eg) $ onMatch subst
chain :: Applicative m => [OnMatch m] -> OnMatch m
chain = foldr (liftA2 (*>)) (const (pure ()))

(~) :: (A.Analysis ana lang, E.Language lang, MonadState (E.EGraph ana lang) m) => P.Pattern lang -> P.Pattern lang -> OnMatch m
(~) l r subst = do  
  ln <- resolveNode (subst IM.!) l
  rn <- resolveNode (subst IM.!) r
  _ <- state $ E.merge ln rn
  pure ()

forEachMatch :: (MonadState (E.EGraph ana lang) m, E.Language lang, A.Analysis ana lang) => [Equation lang] -> ((P.Pattern lang -> m E.ClassId) -> m ()) -> Rule lang m
forEachMatch eqs onMatch = Rule eqs $ \subst -> onMatch (resolveNode (subst IM.!))

foo :: (MonadState (E.EGraph ana l) m, E.Language l, A.Analysis ana l) => P.Pattern l -> P.Pattern l -> Rule l m
foo lhs rhs = Rule ["_MAGIC_ROOT" .= lhs] ("_MAGIC_ROOT" ~ rhs)

    
(.==) :: (MonadState (E.EGraph ana l) m, E.Language l, A.Analysis ana l) => P.Pattern l -> P.Pattern l -> Rule l m
(.==) lhs rhs = forEachMatch ["_MAGIC_ROOT" .= lhs] $ \toNode -> do
    l <- toNode "_MAGIC_ROOT"
    r <- toNode rhs
    void $ state $ E.merge l r




