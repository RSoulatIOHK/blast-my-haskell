import GhcCoreToLean.AST
import GhcCoreToLean.Maps

namespace GHCCore.Lower
open GHCCore.Maps

private def isTypeOrDictArg : Expr → Bool
  | .type_ _ => true
  | .var v   => match v.role with | .dict => true | _ => false
  | _        => false

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
