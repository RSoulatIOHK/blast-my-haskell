import Lean
import Blaster
import GhcCoreToLean.Audit
import GhcCoreToLean.Generated.Data.List.Ordered

namespace Data.List.Ordered

-- These laws target Core dumped by the pinned Cabal package build, not the
-- copied OrderedPilot slice. The import gate resolves the generated helper
-- IDs in this proof file against the freshly produced package model.
theorem package_merge_length {α : Type} (cmp : α → α → Ordering)
    (xs ys : List α) :
    (mergeBy cmp xs ys).length = xs.length + ys.length := by
  unfold mergeBy
  fun_induction mergeBy.loop_4577 cmp xs ys <;> simp_all <;> blaster (timeout: 5)

theorem package_union_membership {α : Type} (cmp : α → α → Ordering)
    (heq : ∀ x y, cmp x y = Ordering.eq → x = y)
    (v : α) (xs ys : List α) :
    v ∈ unionBy cmp xs ys ↔ v ∈ xs ∨ v ∈ ys := by
  unfold unionBy
  fun_induction unionBy.loop_4841 cmp xs ys <;>
    simp_all [or_assoc, or_left_comm, or_comm]
  case case2 x xs y ys h ih =>
    have hxy := heq x y h
    simp_all

end Data.List.Ordered

#ghc_audit
