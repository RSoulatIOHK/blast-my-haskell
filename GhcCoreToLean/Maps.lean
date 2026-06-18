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
  -- pinned explicitly.
  | "GHC.Base.++"      | "++"      => some "List.append"
  | "GHC.Base.map"     | "map"     => some "List.map"
  | "GHC.List.filter"  | "filter"  => some "List.filter"
  | "GHC.List.reverse" | "reverse" => some "List.reverse"
  -- Foldable methods (post-FTP). The desugarer resolves these through
  -- `Data.Foldable.*` on `[a]`, NOT `GHC.List.*` — include both forms so the
  -- mapping fires regardless of which name appears.
  | "Data.Foldable.length" | "GHC.List.length" | "length"  => some "List.length"
  | "Data.Foldable.null"   | "GHC.List.null"   | "null"    => some "List.isEmpty"
  | "Data.Foldable.foldr"  | "GHC.List.foldr"  | "foldr"   => some "(fun f z xs => List.foldr f z xs)"
  | "Data.Foldable.foldl"  | "GHC.List.foldl"  | "foldl"   => some "(fun f z xs => List.foldl f z xs)"
  -- Boolean / Prelude combinators.
  | "GHC.Classes.&&"   | "&&"      => some "(· && ·)"
  | "GHC.Classes.||"   | "||"      => some "(· || ·)"
  | "GHC.Classes.not"  | "not"     => some "not"
  | "GHC.Base.const"   | "const"   => some "(Function.const _)"
  | "GHC.Base.flip"    | "flip"    => some "(fun f a b => f b a)"
  | "GHC.Base.$"       | "$"       => some "(fun f x => f x)"
  | "GHC.Base.otherwise" | "otherwise" => some "true"
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
  | _         => none

/-- Transparent unwrapping data constructors: I#, W#, C# (and module-qualified variants).
    Boxing GHC's unboxed primitives. Treated as identity by Lower. -/
def isUnwrappingDataCon : String → Bool
  | "I#" | "GHC.Types.I#"
  | "W#" | "GHC.Types.W#"
  | "C#" | "GHC.Types.C#" => true
  | _                     => false

end GHCCore.Maps

