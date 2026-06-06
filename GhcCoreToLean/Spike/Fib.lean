import Lean
import Blaster

def fib (n : Int) : Int :=
  match n with
  | 0 => 1
  | 1 => 1
  | _ => fib (n - 1) + fib (n - 2)
decreasing_by all_goals sorry

#blaster [ fib 0 = 1 ]
#blaster [ ∀ (n : Nat), n > 1 → fib n = fib (n - 1) + fib (n - 2) ]
