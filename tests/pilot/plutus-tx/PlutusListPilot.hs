{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE Strict #-}

module PlutusListPilot where

import Prelude hiding (reverse)

-- Source-exact definitions from PlutusTx.List at the pinned commit.
revAppend :: forall a. [a] -> [a] -> [a]
revAppend = rev
  where
    rev :: [a] -> [a] -> [a]
    rev [] a = a
    rev (x : xs) a = rev xs (x : a)
{-# INLINEABLE revAppend #-}

reverse :: [a] -> [a]
reverse l = revAppend l []
{-# INLINEABLE reverse #-}

revAppendInt :: [Int] -> [Int] -> [Int]
revAppendInt = revAppend

reverseInt :: [Int] -> [Int]
reverseInt = reverse

{- @lean
theorem rev_append_spec {α : Type} (xs ys : List α) :
    revAppend xs ys = xs.reverse ++ ys := by
  induction xs generalizing ys with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
      change revAppend xs (x :: ys) = xs.reverse ++ x :: ys
      exact ih (x :: ys)

theorem reverse_model {α : Type} (xs : List α) :
    reverse xs = xs.reverse := by
  simpa [reverse] using rev_append_spec xs []

theorem reverse_involutive {α : Type} (xs : List α) :
    reverse (reverse xs) = xs := by
  simp [reverse_model]

theorem reverse_length {α : Type} (xs : List α) :
    (reverse xs).length = xs.length := by
  simp [reverse_model]

-- Structural induction follows the generated Core helper; Blaster closes the
-- list-length arithmetic. The explicit SMT trust policy audits this axiom.
theorem rev_append_length {α : Type} (xs ys : List α) :
    (revAppend xs ys).length = xs.length + ys.length := by
  unfold revAppend
  fun_induction revAppend.rev_2136 xs ys <;> simp_all <;> blaster (timeout: 5)
-}
