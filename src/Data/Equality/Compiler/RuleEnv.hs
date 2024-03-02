-- | Add Hashmap lookups into the query plan whenever possible
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.Equality.Compiler.RuleEnv where
import Data.Equality.Compiler.PlanStep
import qualified Data.IntMap as IM
import Control.Monad.State
import qualified Data.IntSet as IS
import qualified Data.IntMap as M
import Control.Monad (forM_, when)
import Control.Monad.Writer (MonadWriter(..), runWriter)
import Data.Foldable (Foldable(toList))
import qualified Data.Set as S
import Data.Coerce (coerce)

-- | One variable watch list scheme:
-- Each rule requires some set of vars to be known before we can execute it
-- When a rule cannot be executed yet, there is at least one unknown input var.
-- We insert the rule in a map using this var as key.
-- When the var is learned, we pop the blocked rules and re-insert them, which re-checks their preconditions and either blocks on another var or returns them for execution
newtype Rule f = R { constraintFor :: Constraint f PId}
deriving instance Eq (f PId) =>  Eq (Rule f)
deriving instance Ord (f PId) =>  Ord (Rule f)
deriving instance Show (f PId) =>  Show (Rule f)
type M f m = (MonadState (RuleEnv f) m, MonadWriter [ Rule f ] m) 
data RuleEnv f = RuleEnv { rulesPending :: IM.IntMap [Rule f], ruleKnownVars :: IS.IntSet, missingConstraints :: S.Set (Constraint f PId) }
deriving instance Eq (f PId) =>  Eq (RuleEnv f)
deriving instance Ord (f PId) =>  Ord (RuleEnv f)
deriving instance Show (f PId) =>  Show (RuleEnv f)

-- | Add rules that triggers as soon as we have matched all required pattern vars, e.g. get a cid by congruence hashmap lookup or check a user-supplied predicate
makeEnv :: (Ord (f PId), Foldable f) => S.Set (Constraint f PId) -> (RuleEnv f, [Rule f])
makeEnv inp = runEnv $ do
    modify (\s -> s { missingConstraints = S.union (missingConstraints s) inp } )
    fixpoint (mapM_ (insertRule . R) inp)
    where runEnv = runWriter . flip execStateT (RuleEnv mempty mempty mempty)
-- | Mark a tuple as known, possibly firing rules
addMatched :: (Foldable f, Ord (f PId)) => [Constraint f PId] -> RuleEnv f -> (RuleEnv f, [Rule f])
addMatched inp renv =  runWriter $ flip execStateT renv $ do
  modify (\s -> s { missingConstraints = S.difference (missingConstraints s) (S.fromList inp) } )
  markKnown inp

-- | Mark variable as known and process all rules. When these unblock new rules, process them recursively
-- Doing this in batches is a bit more efficient for the same reason that batching in e-graphs is efficient - we have more cascades and don't have to re-check the same rule within a batch
markKnown :: (Foldable f, M f m, Ord (f PId)) => [Constraint f PId] -> m ()
markKnown [] =  pure ()
markKnown learned = fixpoint $ markKnown1 (foldMap learnedVars learned)

fixpoint :: (Foldable f, M f m, Ord (f PId)) => m () -> m ()
fixpoint m = do
    (_,is1) <- listen m
    markKnown (coerce is1)

isKnown :: (M f m) => PId -> m Bool
isKnown pid = gets (IS.member pid . ruleKnownVars)

insertRule :: (Ord (f PId), Foldable f, MonadState (RuleEnv f) m, MonadWriter [ Rule f ] m) => Rule f -> m ()
insertRule r@(R (_ := args)) = do
    isWanted <- gets (S.member (constraintFor r). missingConstraints)
    when isWanted $ go (toList args)
  where
  queueRule x Nothing = Just [x]
  queueRule x (Just ls) = Just (x:ls)

  go (x:xs) = isKnown x >>= \case
    True -> go xs
    False -> do
      modify (\env -> env { rulesPending = IM.alter (queueRule r) x (rulesPending env) })
  go [] = do
      modify (\env -> env { missingConstraints = S.delete (constraintFor r) (missingConstraints env) })
      tell [r]


-- | Get rules queued for this variable
popSet :: (M f m) => PId -> m [Rule f]
popSet pid = do
    s <- gets (M.findWithDefault [] pid . rulesPending)
    modify $ \env -> env { rulesPending = IM.delete pid (rulesPending env) }
    pure s



-- | a single batch of markKnown. Note that we mark all newly learned vars before processing any rules, which is where the efficiency win comes from
markKnown1 :: (Foldable f, M f m, Ord (f PId)) => IS.IntSet -> m ()
markKnown1 newKnown = do
    modify $ \env -> env { ruleKnownVars = IS.union newKnown (ruleKnownVars env) }
    forM_ (IS.toList newKnown) $ \learned -> do
        newRules <- popSet learned
        mapM_ insertRule newRules
