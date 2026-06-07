import Lean
import Blaster

def fib (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | 1 => 1
  | _ => fib (n - 1) + fib (n - 2)
decreasing_by all_goals sorry

#blaster [ fib 0 = 1 ]
#blaster [ ∀ (n : Nat), n > 1 → fib n = fib (n - 1) + fib (n - 2) ]
#blaster [ ∀ (n : Nat), n > 2 → fib n = 2 * fib (n - 2) + fib (n - 3) ]
#blaster [ ∀ (n : Nat), n > 3 → fib n = 3 * fib (n - 3) + 2 * fib (n - 4) ]
#blaster [ ∀ (n : Nat), n > 4 → fib n = 5 * fib (n - 4) + 3 * fib (n - 5) ]
-- #blaster [ ∀ (n k : Nat), k > 0 → n > k → fib n = fib (k) * fib (n - k) + fib (k - 1) * fib (n - k - 1) ]
