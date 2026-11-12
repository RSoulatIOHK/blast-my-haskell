import Lean
import Blaster
import GhcCoreToLean.Audit
import GhcCoreToLean.Generated.PlutusTx.List

namespace PlutusTx.List

theorem package_rev_append_spec {α : Type} (xs ys : List α) :
    revAppend xs ys = xs.reverse ++ ys := by
  induction xs generalizing ys with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
      change revAppend xs (x :: ys) = xs.reverse ++ x :: ys
      exact ih (x :: ys)

theorem package_reverse_model {α : Type} (xs : List α) :
    reverse xs = xs.reverse := by
  simpa [reverse] using package_rev_append_spec xs []

theorem package_reverse_involutive {α : Type} (xs : List α) :
    reverse (reverse xs) = xs := by
  simp [package_reverse_model]

theorem package_reverse_length {α : Type} (xs : List α) :
    (reverse xs).length = xs.length := by
  simp [package_reverse_model]

theorem package_rev_append_length {α : Type} (xs ys : List α) :
    (revAppend xs ys).length = ys.length + xs.length := by
  rw [package_rev_append_spec, List.length_append, List.length_reverse]
  blaster (timeout: 5)

end PlutusTx.List

#ghc_audit
