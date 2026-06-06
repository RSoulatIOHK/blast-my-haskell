import GhcCoreToLean.AST

namespace GHCCore.Maps

/-- GHC global Id / class method names → Lean term to splice into emitted source.
    Both fully-qualified GHC names and bare operator forms are accepted. -/
def valueMap : String → Option String
  | "GHC.Num.+"     | "+"  => some "(· + ·)"
  | "GHC.Num.-"     | "-"  => some "(· - ·)"
  | "GHC.Num.*"     | "*"  => some "(· * ·)"
  | "GHC.Classes.=="| "==" => some "(· == ·)"
  | "GHC.Classes./="| "/=" => some "(fun a b => a != b)"
  | "GHC.Classes.<" | "<"  => some "(· < ·)"
  | "GHC.Classes.<=" | "<=" => some "(· ≤ ·)"
  | "GHC.Classes.>" | ">"  => some "(· > ·)"
  | "GHC.Classes.>=" | ">=" => some "(· ≥ ·)"
  | "GHC.Base.id"          => some "id"
  | "GHC.Base.."           => some "Function.comp"
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

/-- GHC data constructor → Lean constructor reference. -/
def dataConMap : String → Option String
  | "Just"    => some "Option.some"
  | "Nothing" => some "Option.none"
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

