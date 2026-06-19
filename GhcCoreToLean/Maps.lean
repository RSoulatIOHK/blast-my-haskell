import GhcCoreToLean.AST

namespace GHCCore.Maps

/-- GHC global Id / class method names → Lean term to splice into emitted source.
    Both fully-qualified GHC names and bare operator forms are accepted. -/
def valueMap : String → Option String
  | "GHC.Num.+"     | "+"  => some "(· + ·)"
  | "GHC.Num.-"     | "-"  => some "(· - ·)"
  | "GHC.Num.*"     | "*"  => some "(· * ·)"
  | "GHC.Num.negate"| "negate" => some "Neg.neg"
  | "GHC.Num.abs"   | "abs" => some "(fun a => if a < 0 then -a else a)"
  -- Integral division. Haskell `quot`/`rem` truncate toward zero (Lean
  -- `Int.tdiv`/`Int.tmod`); `div`/`mod` floor (Lean `Int.fdiv`/`Int.fmod`).
  | "GHC.Real.quot" | "quot" => some "Int.tdiv"
  | "GHC.Real.rem"  | "rem"  => some "Int.tmod"
  | "GHC.Real.div"  | "div"  => some "Int.fdiv"
  | "GHC.Real.mod"  | "mod"  => some "Int.fmod"
  -- Haskell's comparison operators return `Bool`. Lean 4's `≤`/`<`/etc. return
  -- `Prop`, so we wrap them in `decide` to get Bool back. `==` is already Bool
  -- via the `BEq` instance, so it does not need wrapping.
  | "GHC.Classes.=="| "==" => some "(· == ·)"
  | "GHC.Classes./="| "/=" => some "(fun a b => !(a == b))"
  | "GHC.Classes.<" | "<"  => some "(fun a b => decide (a < b))"
  | "GHC.Classes.<=" | "<=" => some "(fun a b => decide (a ≤ b))"
  | "GHC.Classes.>" | ">"  => some "(fun a b => decide (a > b))"
  | "GHC.Classes.>=" | ">=" => some "(fun a b => decide (a ≥ b))"
  -- Prelude `min`/`max` (Ord methods) → Lean's. Only the *qualified* Prelude
  -- names are mapped, never bare `min`/`max`: a user's own `min`/`max` def is a
  -- bare Core name and must keep resolving to that local def, not be hijacked.
  | "GHC.Classes.min" => some "Min.min"
  | "GHC.Classes.max" => some "Max.max"
  -- Bottoms. Applied forms are collapsed to `sorry` in Emit (spine-head
  -- check); this covers the rare bare/unapplied reference.
  | "GHC.Err.error" | "error"
  | "GHC.Err.errorWithoutStackTrace" | "errorWithoutStackTrace"
  | "GHC.Err.undefined" | "undefined" => some "sorry"
  | "GHC.Base.id"          => some "id"
  | "GHC.Base.."           => some "Function.comp"
  -- GHC's True/False are data constructors used in value positions. Map them
  -- to Lean's Bool literals so dict-method bodies like `$c/=` compile.
  | "GHC.Types.True"       => some "true"
  | "GHC.Types.False"      => some "false"
  -- List library (total). Haskell `++`/`map`/… map directly to Lean `List.*`.
  -- `foldr`/`foldl` are eta-wrapped so their Haskell arg order (f, z, xs) is
  -- pinned explicitly. As with `min`/`max` above, bare *alphabetic* forms are
  -- intentionally omitted: a user's own top-level `map`/`filter`/`length`/… def
  -- is a bare Core name and must keep resolving to that local def, not be
  -- hijacked here. Core qualifies these names anyway, so nothing is lost. Bare
  -- *operator* forms (`++`, `&&`, …) stay, since users can't shadow them.
  | "GHC.Base.++"      | "++"      => some "List.append"
  | "GHC.Base.map"                => some "List.map"
  | "GHC.List.filter"             => some "List.filter"
  | "GHC.List.reverse"            => some "List.reverse"
  -- Foldable methods (post-FTP). The desugarer resolves these through
  -- `Data.Foldable.*` on `[a]`, NOT `GHC.List.*` — include both forms so the
  -- mapping fires regardless of which name appears.
  -- Haskell `length` returns `Int`; Lean `List.length` returns `Nat`. Coerce
  -- to `Int` (like `gcd`/`lcm`) so it composes with Int arithmetic.
  | "Data.Foldable.length" | "GHC.List.length"  => some "(fun xs => (List.length xs : Int))"
  | "Data.Foldable.null"   | "GHC.List.null"    => some "List.isEmpty"
  | "Data.Foldable.foldr"  | "GHC.List.foldr"   => some "(fun f z xs => List.foldr f z xs)"
  | "Data.Foldable.foldl"  | "GHC.List.foldl"   => some "(fun f z xs => List.foldl f z xs)"
  -- Boolean / Prelude combinators.
  | "GHC.Classes.&&"   | "&&"      => some "(· && ·)"
  | "GHC.Classes.||"   | "||"      => some "(· || ·)"
  | "GHC.Classes.not"             => some "not"
  | "GHC.Base.const"              => some "(Function.const _)"
  | "GHC.Base.flip"               => some "(fun f a b => f b a)"
  | "GHC.Base.$"       | "$"       => some "(fun f x => f x)"
  | "GHC.Base.otherwise"          => some "true"
  -- Tuple projections. Qualified only (a user could define `fst`/`snd`); the
  -- desugarer resolves these through `Data.Tuple.*`.
  | "Data.Tuple.fst"              => some "Prod.fst"
  | "Data.Tuple.snd"              => some "Prod.snd"
  -- Num / Integral / Ord completion. Qualified names only (no bare alphabetic
  -- forms), so a user's own `signum`/`divMod`/… top-level def is not hijacked.
  -- Integer/Int are both Lean `Int`, so the coercion methods are identities.
  | "GHC.Num.fromInteger"   => some "id"
  | "GHC.Real.toInteger"    => some "id"
  | "GHC.Real.fromIntegral" => some "id"
  | "GHC.Num.signum"        => some "(fun a => if a < 0 then -1 else if a > 0 then 1 else 0)"
  -- divMod floors (fdiv/fmod); quotRem truncates (tdiv/tmod). Returns a pair.
  | "GHC.Real.divMod"       => some "(fun a b => (Int.fdiv a b, Int.fmod a b))"
  | "GHC.Real.quotRem"      => some "(fun a b => (Int.tdiv a b, Int.tmod a b))"
  -- Lean `Int.gcd`/`Int.lcm` return `Nat`; Haskell returns the numeric type.
  | "GHC.Real.gcd"          => some "(fun a b => (Int.gcd a b : Int))"
  | "GHC.Real.lcm"          => some "(fun a b => (Int.lcm a b : Int))"
  | "GHC.Classes.compare"   => some "compare"
  | _                      => none

/-- GHC type constructor name + args → Lean type expression (as a string,
    with arg strings already emitted). Returns `none` when the ctor is opaque. -/
def typeConMap : String → List String → Option String
  | "Int",     []     => some "Int"
  | "Int#",    []     => some "Int"
  | "GHC.Prim.Int#", [] => some "Int"
  | "Integer", []     => some "Int"
  | "Word",    []     => some "Nat"
  | "Word#",   []     => some "Nat"
  | "GHC.Prim.Word#", [] => some "Nat"
  | "Bool",    []     => some "Bool"
  | "Char",    []     => some "Char"
  | "Char#",   []     => some "Char"
  | "GHC.Prim.Char#", [] => some "Char"
  | "()",      []     => some "Unit"
  | "List",    [a]    => some s!"List {a}"
  | "[]",      [a]    => some s!"List {a}"
  | "Maybe",   [a]    => some s!"Option {a}"
  | "Either",  [a, b] => some s!"Sum {a} {b}"
  -- Tuples. Lean's `×` is right-nested: `a × b × c = a × (b × c)`. Both the
  -- bare GHC tycon `(,)` (what the shim emits inside `tyConOpaque`) and any
  -- qualified form resolve here.
  | "(,)",   [a, b]    => some s!"({a} × {b})"
  | "GHC.Tuple.(,)", [a, b] => some s!"({a} × {b})"
  | "(,,)",  [a, b, c] => some s!"({a} × {b} × {c})"
  | "GHC.Tuple.(,,)", [a, b, c] => some s!"({a} × {b} × {c})"
  | "Ordering", []    => some "Ordering"
  | _,         _      => none

/-- GHC data constructor → Lean constructor reference. Both bare and
    module-qualified forms are accepted (Core delivers `GHC.Maybe.Just` etc.). -/
def dataConMap : String → Option String
  | "Just"    | "GHC.Maybe.Just"    => some "Option.some"
  | "Nothing" | "GHC.Maybe.Nothing" => some "Option.none"
  | ":"       => some "List.cons"
  | "[]"      => some "List.nil"
  | "True"    => some "Bool.true"
  | "False"   => some "Bool.false"
  | "()"      => some "Unit.unit"
  -- 2-tuple construction → `Prod.mk a b`. Both the bare pattern-position name
  -- `(,)` and the qualified value-position name `GHC.Tuple.(,)` resolve here.
  -- NOTE: 3-tuple construction is intentionally NOT mapped: `Prod.mk` is binary,
  -- and `emitExpr` left-applies, so `(,,) a b c` would emit `((Prod.mk a) b) c`,
  -- which is ill-typed. Tracked as a follow-up (see TupleBasics report). The
  -- type (`a × b × c`) and pattern (`(x, y, z)`) paths DO support 3-tuples.
  | "(,)"     | "GHC.Tuple.(,)" => some "Prod.mk"
  -- Ordering constructors. Core delivers the qualified `GHC.Types.*` forms
  -- (confirmed via Generated/NumOrd.lean); bare forms kept as a hedge.
  | "LT" | "GHC.Types.LT" => some "Ordering.lt"
  | "EQ" | "GHC.Types.EQ" => some "Ordering.eq"
  | "GT" | "GHC.Types.GT" => some "Ordering.gt"
  | _         => none

/-- Transparent unwrapping data constructors: I#, W#, C# (and module-qualified variants).
    Boxing GHC's unboxed primitives. Treated as identity by Lower. -/
def isUnwrappingDataCon : String → Bool
  | "I#" | "GHC.Types.I#"
  | "W#" | "GHC.Types.W#"
  | "C#" | "GHC.Types.C#" => true
  | _                     => false

end GHCCore.Maps

