import GhcCoreToLean.AST
import GhcCoreToLean.Maps

namespace GHCCore.Lower
open GHCCore.Maps

private def exactIntTyCon := "$GhcCoreToLean.Int64"

private def machineIntValueName (exact : Bool) (n : Name) : Name :=
  if !exact then n else match n with
  | "GHC.Base.ord" => "$GhcCoreToLean.ordInt64"
  | "Data.Foldable.length" | "GHC.List.length" => "$GhcCoreToLean.lengthInt64"
  | "GHC.List.take" => "$GhcCoreToLean.takeInt64"
  | "GHC.List.drop" => "$GhcCoreToLean.dropInt64"
  | "GHC.List.splitAt" => "$GhcCoreToLean.splitAtInt64"
  | "GHC.List.replicate" => "$GhcCoreToLean.replicateInt64"
  | _ => n

private def isMachineIntType : GHCType → Bool
  | .tyCon n [] => ["Int", "Int#", "GHC.Prim.Int#"].contains n
  | _ => false

private def machineIntOverloadedName (exact : Bool) (n : Name) (t : GHCType) : Name :=
  let base := machineIntValueName exact n
  if !exact || !isMachineIntType t then base else match n with
  | "GHC.Real.quot" => "$GhcCoreToLean.quotInt64"
  | "GHC.Real.rem" => "$GhcCoreToLean.remInt64"
  | "GHC.Real.div" => "$GhcCoreToLean.divInt64"
  | "GHC.Real.mod" => "$GhcCoreToLean.modInt64"
  | "GHC.Real.divMod" => "$GhcCoreToLean.divModInt64"
  | "GHC.Real.quotRem" => "$GhcCoreToLean.quotRemInt64"
  | "GHC.Real.gcd" => "$GhcCoreToLean.gcdInt64"
  | "GHC.Real.lcm" => "$GhcCoreToLean.lcmInt64"
  | "GHC.Enum.enumFromTo" => "$GhcCoreToLean.enumFromToInt64"
  | "GHC.Num.fromInteger" => "$GhcCoreToLean.fromIntegerInt64"
  | "GHC.Real.toInteger" => "$GhcCoreToLean.toIntegerInt64"
  | _ => base

private def machineIntFromIntegralName (exact : Bool) (n : Name)
    (src dst : GHCType) : Name :=
  let base := machineIntValueName exact n
  if !exact || n != "GHC.Real.fromIntegral" then base
  else if isMachineIntType src && !isMachineIntType dst then
    "$GhcCoreToLean.int64ToInteger"
  else if !isMachineIntType src && isMachineIntType dst then
    "$GhcCoreToLean.integerToInt64"
  else base

/- Select the representation of a GHC machine `Int` before ordinary Core
    lowering. Conservative mode uses Lean's wrapping `Int64`; approximate mode
    deliberately retains the historical unbounded `Int` model. `Integer` and
    `LitInteger` are untouched in both modes. -/
mutual
  private partial def machineIntType (exact : Bool) : GHCType → GHCType
    | .tyVar n => .tyVar n
    | .tyApp f a => .tyApp (machineIntType exact f) (machineIntType exact a)
    | .tyFun a b => .tyFun (machineIntType exact a) (machineIntType exact b)
    | .forAll n t => .forAll n (machineIntType exact t)
    | .tyCon n args =>
      let n' := if exact && ["Int", "Int#", "GHC.Prim.Int#"].contains n
        then exactIntTyCon else n
      .tyCon n' (args.map (machineIntType exact))
    | .tyLit l => .tyLit l

  private partial def machineIntVar (exact : Bool) (v : Var) : Var :=
    { v with name := machineIntValueName exact v.name, ty := machineIntType exact v.ty }

  private partial def machineIntLiteral (exact : Bool) : Literal → Literal
    | .litMachineInt n => if exact then .litMachineInt n else .litInt n
    | l => l

  private partial def machineIntExpr (exact : Bool) : Expr → Expr
    | .app (.app (.var v) (.type_ src)) (.type_ dst) =>
      let v' := machineIntVar exact v
      let v' := { v' with name := machineIntFromIntegralName exact v.name src dst }
      .app (.app (.var v') (.type_ (machineIntType exact src)))
        (.type_ (machineIntType exact dst))
    | .app (.var v) (.type_ t) =>
      let v' := machineIntVar exact v
      let v' := { v' with name := machineIntOverloadedName exact v.name t }
      .app (.var v') (.type_ (machineIntType exact t))
    | .var v => .var (machineIntVar exact v)
    | .lit l => .lit (machineIntLiteral exact l)
    | .app f a => .app (machineIntExpr exact f) (machineIntExpr exact a)
    | .lam v e => .lam (machineIntVar exact v) (machineIntExpr exact e)
    | .let_ b e => .let_ (machineIntBind exact b) (machineIntExpr exact e)
    | .case_ e v t alts =>
      .case_ (machineIntExpr exact e) (machineIntVar exact v) (machineIntType exact t)
        (alts.map (machineIntAlt exact))
    | .cast e => .cast (machineIntExpr exact e)
    | .type_ t => .type_ (machineIntType exact t)
    | .coercion => .coercion
    | .tick e => .tick (machineIntExpr exact e)

  private partial def machineIntBind (exact : Bool) : Bind → Bind
    | .nonRec v e => .nonRec (machineIntVar exact v) (machineIntExpr exact e)
    | .rec_ pairs => .rec_ (pairs.map fun (v, e) =>
        (machineIntVar exact v, machineIntExpr exact e))

  private partial def machineIntAlt (exact : Bool) : Alt → Alt
    | .mk c vs rhs =>
      let c' := match c with
        | .litAlt l => .litAlt (machineIntLiteral exact l)
        | other => other
      .mk c' (vs.map (machineIntVar exact)) (machineIntExpr exact rhs)
end

private def machineIntDataDecl (exact : Bool) (d : DataDecl) : DataDecl :=
  { d with ctors := d.ctors.map fun c =>
      { c with fields := c.fields.map fun f => { f with ty := machineIntType exact f.ty } } }

/-- Apply the selected machine-`Int` model consistently to Core and declaration
    metadata. This runs after conservative safety checks, which inspect the
    original GHC names. -/
def machineInts (exact : Bool) (p : Program) : Program :=
  { binds := p.binds.map (machineIntBind exact)
    rawBinds := p.rawBinds.map (machineIntBind exact)
    typeDecls := p.typeDecls.map (machineIntDataDecl exact)
    instances := p.instances.map fun i =>
      { i with headTypes := i.headTypes.map (machineIntType exact) }
    classDecls := p.classDecls.map fun c =>
      { c with methods := c.methods.map fun m =>
          { m with ty := machineIntType exact m.ty } } }

private def isTypeOrDictArg : Expr → Bool
  | .type_ _  => true
  -- A coercion in argument position is a proof term with no Lean image and no
  -- runtime content; it erases exactly like a type or dict argument.
  | .coercion => true
  | .var v    => match v.role with | .dict => true | _ => false
  | _         => false

private def isTypeOrDictBinder (v : Var) : Bool :=
  match v.role with
  | .tyVar | .dict => true
  | .id            => false

/-- True iff the expression is a reference to an unwrapping data constructor
    (I#, W#, C#, etc.) in applied position. -/
private def isUnwrappingCtorRef : Expr → Bool
  | .var v => isUnwrappingDataCon v.name
  | _      => false

mutual
  partial def lowerExpr : Expr → Expr
    | .app f a =>
      -- Type-app erasure: `f @T` → `f`
      -- Dict-app erasure:  `f $dEqInt` → `f`
      if isTypeOrDictArg a then lowerExpr f
      -- Unwrapping ctor erasure in App position: `I# x` → `x`
      else if isUnwrappingCtorRef f then lowerExpr a
      else .app (lowerExpr f) (lowerExpr a)
    | .lam v body =>
      if isTypeOrDictBinder v then lowerExpr body
      else .lam v (lowerExpr body)
    | .let_ b body =>
      -- Dict/type let-bindings are erased like dict/type args. GHC floats the
      -- `HasCallStack` dict (`$dIP`) to a top-level `let`; once the `error`
      -- that used it collapses to `sorry`, the binding is dead and references
      -- call-stack primitives with no Lean image, so it must be dropped.
      match b with
      | .nonRec v _ => if isTypeOrDictBinder v then lowerExpr body
                       else .let_ (lowerBind b) (lowerExpr body)
      | _           => .let_ (lowerBind b) (lowerExpr body)
    | .case_ scr cb ty alts =>
      -- Unwrapping ctor in single-alt Case: `case x of cb { I# y -> body }` → `let y := x; body`
      match alts with
      | [.mk (.dataCon name) [b] rhs] =>
        if isUnwrappingDataCon name then
          .let_ (.nonRec b (lowerExpr scr)) (lowerExpr rhs)
        else
          let alts' := alts.map fun
            | .mk c bs r => Alt.mk c bs (lowerExpr r)
          .case_ (lowerExpr scr) cb ty alts'
      | _ =>
        let alts' := alts.map fun
          | .mk c bs r => Alt.mk c bs (lowerExpr r)
        .case_ (lowerExpr scr) cb ty alts'
    | .cast e => lowerExpr e
    | .tick e => lowerExpr e
    | other   => other

  partial def lowerBind : Bind → Bind
    | .nonRec v e => .nonRec v (lowerExpr e)
    | .rec_ pairs => .rec_ (pairs.map fun (v, e) => (v, lowerExpr e))
end

def lowerProgram (p : CoreProgram) : CoreProgram :=
  p.map lowerBind

end GHCCore.Lower
