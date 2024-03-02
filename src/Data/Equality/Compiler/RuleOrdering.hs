{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.Equality.Compiler.RuleOrdering where

import Data.Equality.Compiler.PlanStep
import qualified Data.Set as S
import qualified Data.IntSet as IS
import Data.Foldable (Foldable(toList))
import Data.Equality.Compiler.RuleEnv

-- | VM Instructions to do egraph search.
-- Usually tagless final so we skip an intermediary ADT.
-- This matches constraints of the form eid := expr
class VMPlan f r | r -> f  where
   -- | iterate over all egraph classes to search eid. Store eid in Reg
   scanClasses :: Reg -> r -> r
   -- | iterate over all nodes in the Reg class that match some pattern.
   -- Some of the pattern arguments will be set registers, at least one will be unset (otherwise this would be a lookupHash)
   -- We use the prefix of set registers to fast-forward through the collection and do a linear scan from there.
   -- Set registers are used for filtering, unset registers are set.
   searchSpan :: Int -- ^ prefix len
              -> Reg -- ^ eclass of expression
              -> f Reg -- ^ Search pattern
              -> r -> r
   -- | Hash lookup from congruence hashmap. If register is unset, set it. Otherwise compare and fail if different
   lookupHash :: f Reg -> Reg -> r -> r
   yieldOut :: r


greedyPlan :: (Foldable f, Ord (f PId), VMPlan f r) => S.Set (Constraint f PId) -> r
greedyPlan ls0 = addRules groundRules (go env0)
  where
    -- ground rules do hash lookups of subterms without variables
    (env0, groundRules) = makeEnv ls0
    go env
      | S.null (missingConstraints env) = yieldOut
      | otherwise = addJoin next (go (newEnv next))
      where next = maximum $ map (rateCandidate env) $ S.toList $ missingConstraints env


data Rating f = Rating { joinEfficiency :: Int, ruleTriggers :: Int, newPrefixes :: Int, joined :: Constraint f PId, firedRules :: [ Rule f ], newEnv :: RuleEnv f, prefixLen :: Int, joinSourceKnown :: Bool}
deriving instance Eq (f PId) =>  Eq (Rating f)
deriving instance Ord (f PId) =>  Ord (Rating f)
deriving instance Show (f PId) =>  Show (Rating f)

-- | Rate next join. 
-- - Prefer cheap/low-branching joins, 
-- - then prefer joins which enable hash lookups afterwar
-- - then prefer joins with scan+filter
rateCandidate :: (Foldable f, Ord (f PId)) => RuleEnv f -> Constraint f PId -> Rating f
rateCandidate env c = Rating joinCost (length triggers) maxNewPrefixLen c triggers env' prefLen sourceKnown
  where
    (joinCost, sourceKnown, prefLen) = estJoinCost env c
    (env', triggers) = addMatched [c] env

    maxNewPrefixLen
      | S.null (missingConstraints env') = 100
      | otherwise = maximum $ [ joinCost | con <- S.toList (missingConstraints env'), let (joinCost, _, _) = estJoinCost env' con ]
      

-- | Estimates cost of join, higher is better
estJoinCost :: Foldable f => RuleEnv f -> Constraint f PId -> (Int, Bool, Int)
estJoinCost env (cid := args) = (joinCost, sourceKnown, count)
  where
    sourceKnown = isKnownVar cid
    joinCost
      | sourceKnown && count >= 2 = 3 -- Known class, long enough prefix for binary search
      | sourceKnown && count == 1 = 2
      | sourceKnown = 1
      | isKnownVar cid = 1
      | otherwise = 0
    count = length (takeWhile isKnownVar (toList args))
    isKnownVar v = IS.member v (ruleKnownVars env)

type Reg = Int -- PId or -1 if missing




addJoin :: (VMPlan f r) => Rating f -> r -> r
addJoin Rating{prefixLen = knownPrefix, newPrefixes = maxNewPrefixLen, joined = joinedId := pat, firedRules = newRules, newEnv=env, joinSourceKnown = sourceKnown}
  = addScan  -- If the parent class is unknown iterate over all classes
  . searchSpan knownPrefix joinedId pat  -- then search all values matching the 
  . addRules newRules -- then do hash lookups and custom filtering
  where
    addScan
      | sourceKnown = id
      | otherwise = scanClasses joinedId

addRules :: VMPlan f t => [Rule f] -> t -> t
addRules [] cont = cont
addRules (R (kr := kargs):rs) cont = lookupHash kargs kr (addRules rs cont)




