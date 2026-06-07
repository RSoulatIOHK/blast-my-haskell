import Lean
import Blaster

-- Auto-generated from examples/FibComplex.hs via the spike pipeline.
-- The Haskell source has 4 explicit pattern equations, a guard, a where-clause
-- aux, and a local let-binding two shared subexpressions. GHC's desugarer
-- inlined the where + lets, leaving two arithmetic recurrences (one standard,
-- one using fib n = 2*fib(n-2) + fib(n-3)).

namespace Spike.FibComplexFromShim

def fib (ds_3124 : Int) : Int :=
  (let ds_3127 := ds_3124
(match ds_3127 with
| 0 => (1 : Int)
| 1 => (1 : Int)
| 2 => (2 : Int)
| 3 => (3 : Int)
| _ => (match (((fun a b => decide (a ≤ b))) (ds_3124)) ((5 : Int)) with
| Bool.false => (((· + ·)) ((((· * ·)) ((2 : Int))) ((fib) ((((· - ·)) (ds_3124)) ((2 : Int)))))) ((fib) ((((· - ·)) (ds_3124)) ((3 : Int))))
| Bool.true => (((· + ·)) ((fib) ((((· - ·)) (ds_3124)) ((1 : Int))))) ((fib) ((((· - ·)) (ds_3124)) ((2 : Int)))))))
decreasing_by all_goals sorry

#blaster [ fib 0 = 1 ]
#blaster [ fib 2 = 2 ]
#blaster [ fib 4 = 5 ]
#blaster [ fib 6 = 13 ]

end Spike.FibComplexFromShim
