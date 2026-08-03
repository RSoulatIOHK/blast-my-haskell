/-! # Haskell runtime support helpers

Named Lean images for `base` functions whose faithful translation is too
complex for a readable inline lambda in `Maps.lean` (spec: 2026-07-24
coverage-roadmap §"runtime support module"). Generated files import this
module unconditionally; helpers are ordinary defs, `#guard`-tested in
`Tests/Unit.lean`, and stable named symbols for Blaster to unfold. -/

namespace Hs

/-- Haskell `[lo .. hi]` (`GHC.Enum.enumFromTo` at `Int`): the ascending run
    `lo, lo+1, …, hi`. Empty when `hi < lo`.

    Note on the `(i : Nat)` binder + `(i : Int)` cast: `List.range` yields a
    `List Nat`, so the `binop%` elaborator resolves `i : Int` from the
    arithmetic and then rejects the `List Nat` argument. Annotating the binder
    and casting explicitly is a purely mechanical fix — the arithmetic is
    unchanged. -/
def enumFromTo (lo hi : Int) : List Int :=
  (List.range (hi + 1 - lo).toNat).map (fun (i : Nat) => lo + (i : Int))

/-- Haskell `[a, b .. c]` (`GHC.Enum.enumFromThenTo` at `Int`), stride `b - a`.
    Faithful on every finite case (positive stride, negative stride, and the
    zero-stride `c < a` case, which GHC makes `[]`). The zero-stride `c ≥ a`
    case is an *infinite* list in Haskell — every total observation of it is
    ⊥ — so it lowers to `default` (= `[]`), the project's sound-bottom
    convention. The `(i : Nat)` binders below carry the same `(i : Int)` cast
    note as `enumFromTo`. -/
def enumFromThenTo (a b c : Int) : List Int :=
  let d := b - a
  -- Counts divide MAGNITUDES as `Nat` (count = ⌊span / |stride|⌋ + 1), never
  -- `(c - a) / d` as `Int`: Lean v4.24's `/` on `Int` is `Int.ediv`, and in
  -- the negative-stride branch both operands are ≤ 0, where ediv rounds AWAY
  -- from zero ((-5) / (-2) = 3, not 2). That overshoots: `[10, 8 .. 5]` would
  -- give `[10, 8, 6, 4]`. On Nat magnitudes every division convention agrees.
  if d > 0 then
    if a > c then []
    else (List.range ((c - a).toNat / d.toNat + 1)).map (fun (i : Nat) => a + d * (i : Int))
  else if d < 0 then
    if a < c then []
    else (List.range ((a - c).toNat / (-d).toNat + 1)).map (fun (i : Nat) => a + d * (i : Int))
  else
    default

/-- Haskell `splitAt n xs = (take n xs, drop n xs)`; negative `n` acts as 0
    (`Int.toNat` clamps, matching GHC). -/
def splitAt (n : Int) (xs : List α) : List α × List α :=
  (xs.take n.toNat, xs.drop n.toNat)

end Hs
