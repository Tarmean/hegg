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
import qualified Data.IntMap as IM
import qualified Data.Equality.Analysis as A
import Data.Functor (void)
import Data.Equality.Saturation.Scheduler (Score)
import qualified Data.Equality.Saturation.Scheduler as Score

type RewriteCondition anl lang = R.Subst -> E.EGraph anl lang -> Bool


data Equation f = Equation (P.Pattern f) (P.Pattern f)
deriving instance (forall a. Eq (f a)) => Eq (Equation f)
deriving instance (forall a. Show (f a)) => Show (Equation f)
deriving instance (forall a. Ord (f a)) => Ord (Equation f)
{-# INLINE (.=) #-}
(.=) :: P.Pattern f -> P.Pattern f -> Equation f
(.=) = Equation
data Rule f m = Rule { ruleLhs :: [Equation f], ruleRhs :: R.Subst -> m Score }
type OnMatch m = R.Subst -> m Score.Score

{-# INLINE (.|) #-}
(.|) :: (MonadState (E.EGraph ana lang) m) => Rule f m -> RewriteCondition ana lang -> Rule f m
(.|) (Rule l r) cond = Rule l $ \subst -> do
   eg <- get
   if cond subst eg then r subst
   else pure mempty
chain :: Applicative m => [OnMatch m] -> OnMatch m
chain = foldr (liftA2 (liftA2 (<>))) (const (pure mempty))

{-# INLINE (~) #-}
(~) :: (A.Analysis ana lang, E.Language lang, MonadState (E.EGraph ana lang) m) => P.Pattern lang -> P.Pattern lang -> OnMatch m
(~) l r subst = do  
  ln <- resolveNode (subst IM.!) l
  rn <- resolveNode (subst IM.!) r
  _ <- state $ E.merge ln rn
  pure (Score.fromSubst subst)

{-# INLINE forEachMatch #-}
forEachMatch :: (MonadState (E.EGraph ana lang) m, E.Language lang, A.Analysis ana lang) => [Equation lang] -> ((P.Pattern lang -> m E.ClassId) -> m ()) -> Rule lang m
forEachMatch eqs onMatch = Rule eqs $ \subst -> Score.fromSubst subst <$ onMatch (resolveNode (subst IM.!))

foo :: (MonadState (E.EGraph ana l) m, E.Language l, A.Analysis ana l) => P.Pattern l -> P.Pattern l -> Rule l m
foo lhs rhs = Rule ["_MAGIC_ROOT" .= lhs] ("_MAGIC_ROOT" ~ rhs)

    
{-# INLINE (.==) #-}
(.==) :: (MonadState (E.EGraph ana l) m, E.Language l, A.Analysis ana l) => P.Pattern l -> P.Pattern l -> Rule l m
(.==) lhs rhs = forEachMatch ["_MAGIC_ROOT" .= lhs] $ \toNode -> do
    l <- toNode "_MAGIC_ROOT"
    r <- toNode rhs
    void $ state $ E.merge l r




resolveNode :: (A.Analysis ana lang, E.Language lang, MonadState (E.EGraph ana lang) m)=> (R.Var -> E.ClassId) -> P.Pattern lang -> m E.ClassId
resolveNode f (P.VariablePattern v) = pure (f v)
resolveNode f (P.NonVariablePattern v) = state . (E.add . E.Node ) =<< traverse (resolveNode f) v
