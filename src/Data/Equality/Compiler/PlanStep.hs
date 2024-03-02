{-|
Generate the next matching candidates, given some partially known pattern
For each candidate, produce a new state and stats like:
    - How many variables are already known (matchable using index)
    - How many other subexpressions become ground, so we can validate them with hash joins?
    - Are there locally known variables? We can't use the index but can filter while linearly scanning, e.g.: 
        - a+a has lower branching factor than a+b
        - a+f(a) means we can validate f(a) with a hash lookup, this is better
          than just an existential join because the second argument of `+` must
          be consistent with the result
    - How many new variables would we learn

This is essentially greedy SQL query planning, i.e. not very good. But
it must be sufficient, we don't have table statistics to work with most of
the time
-}



{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
module Data.Equality.Compiler.PlanStep  where

import Data.Foldable (toList)
import qualified Data.IntSet as IS
{-
 [NOTE: Pattern Matching]
 We represent patterns as a list of constraints `PId := f PId`. We search substitutions `ClassId := f ClassId` such that for each `cid := expr` we have `cid == lookupNM expr (memo egraph)`.

In words, expr is in the egraph and maps to the class cid in the hashmap.

The pattern `?a + (?b * ?a)` would translate to 

    [?a = 1, ?b = 3]
    0 := +(1, 2)
    2 := *(3, 1)

Note that the patterns have the same structure as an E-Graph.

There are many CS areas which solve the exact problem of E-Matching (without the congruence closure)

- Subgraph Isomorphisms
- Select-Project-Join queries in SQL 
- Non-recursive Datalog

Bad news: these problems are all NP-Hard, but usally tractable.
We mostly go with the QuickSI algorithm but with some congurence-closure specific optimizations.


### Algorithm:

Each step solves one constraint, either by looping over the database tuples or using a hashmap lookup.
We can see constraints as nodes in a graph, and common IDs as edges between them. QuickSI is greedy, starting with the cheapest node and always following the cheapest edge by some cost heuristic. This gives us a naive but servicable join-ordering in an sql query plan.

Subgraph Isomorphism literature found that this is usually fastest of the Non-Indexing approaches, and that pairwise joins are faster than worst-case-optimal joins in many cases.

- If an expression is ground, e.g. has no unmatched variables, we can retrieve it from the hashmap

Some subexpressions start ground, e.g. `+(Const 1, Const 1)`. In this case we could retrieve the constants from the E-Graph when compiling the pattern to avoid the repeatedd hashmap lookup whenever we run the rule. It only happens once per E-Graph iteration, though, and mutating the egraph during pattern compilation seems annoying.

### 


- We know the variable and can use it to speed up matching, e.g. using an index or the natural sorting if we know some prefix
- We don't know the variable at all and must record it
- We learn the variable while matching the curent sub-expression
  - because the variable occurs multiple times, `a+a`: check the second variable for equality directly after the match
  - because some sub-expression becomes resolvable, `a+b` but `a == f(b)`: check a's consistency after the match
-}


type PId = Int
data Constraint f x = x := f x
  deriving (Eq, Show, Ord)

learnedVars :: Foldable f => Constraint f PId -> IS.IntSet
learnedVars (l := r) = IS.fromList (l : toList r)
