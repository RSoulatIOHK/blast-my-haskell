import GhcCoreToLean.AST
import GhcCoreToLean.Lower
import GhcCoreToLean.Emit

namespace GHCCore.Spike

open GHCCore

private def intTy     : GHCType := .tyCon "Int" []
private def intHashTy : GHCType := .tyCon "Int#" []
private def fibFunTy  : GHCType := .tyFun intTy intTy

private def vFib    : Var := { name := "fib",    unique := 1,   ty := fibFunTy,  role := .id }
private def vDs     : Var := { name := "ds",     unique := 2,   ty := intTy,     role := .id }
private def vWild   : Var := { name := "wild",   unique := 4,   ty := intTy,     role := .id }
private def vDsI    : Var := { name := "ds_inner", unique := 3, ty := intHashTy, role := .id }
private def vDsO    : Var := { name := "ds_outer", unique := 5, ty := intHashTy, role := .id }

private def vNumP   : Var := { name := "GHC.Num.+", unique := 100, ty := intTy, role := .id }
private def vNumM   : Var := { name := "GHC.Num.-", unique := 101, ty := intTy, role := .id }
private def vIHash  : Var := { name := "I#",        unique := 200, ty := intTy, role := .id }
private def vDict   : Var := { name := "$fNumInt",  unique := 50,  ty := intTy, role := .dict }

private def lit (n : Int) : Expr := .lit (.litInt n)

/-- (·) is left-associative App: applyAll f [a, b, c] = (((f a) b) c). -/
private def applyAll (f : Expr) (args : List Expr) : Expr :=
  args.foldl Expr.app f

/-- `GHC.Num.+ @Int $fNumInt a b` ; dict + type arg present, will be lowered away. -/
private def addInt (a b : Expr) : Expr :=
  applyAll (.var vNumP) [.type_ intTy, .var vDict, a, b]

private def subInt (a b : Expr) : Expr :=
  applyAll (.var vNumM) [.type_ intTy, .var vDict, a, b]

/-- I# applied to an Int# literal; should be lowered to the bare literal. -/
private def boxInt (n : Int) : Expr := .app (.var vIHash) (lit n)

/-- Recursive call: `fib expr`. -/
private def callFib (e : Expr) : Expr := .app (.var vFib) e

/-- Body matches the pass-0000 Core for fib:
    λ ds → case ds of wild {
             I# ds_inner →
               case ds_inner of ds_outer {
                 DEFAULT → +(fib (ds_inner - I# 1#)) (fib (ds_inner - I# 2#))
                 0# → I# 1#
                 1# → I# 1#
               }
           } -/
private def fibBody : Expr :=
  .lam vDs (
    .case_ (.var vDs) vWild intTy [
      .mk (.dataCon "I#") [vDsI] (
        .case_ (.var vDsI) vDsO intHashTy [
          .mk .default [] (
            addInt
              (callFib (subInt (.var vDsI) (boxInt 1)))
              (callFib (subInt (.var vDsI) (boxInt 2)))
          ),
          .mk (.litAlt (.litInt 0)) [] (boxInt 1),
          .mk (.litAlt (.litInt 1)) [] (boxInt 1)
        ]
      )
    ]
  )

private def fibProgram : CoreProgram := [.rec_ [(vFib, fibBody)]]

private def lowered : CoreProgram := Lower.lowerProgram fibProgram

private def emitted : String := Emit.emitProgram lowered

/-- Run with `#eval` to see what the pipeline emits for fib. -/
def showEmitted : IO Unit := IO.println emitted

#eval showEmitted

end GHCCore.Spike
