import GhcCoreToLean.Safety

open GHCCore

private def binding (ty : GHCType) (body : Expr) : Program :=
  { binds := [.nonRec { name := "test", unique := 1, ty, role := .id } body],
    typeDecls := [], instances := [] }

-- Integer literals are mathematical integers. Machine Int is now admitted and
-- selected as exact `Int64` by Lower; the other machine types remain refused.
#guard (Safety.check (binding (.tyCon "Integer" []) (.lit (.litInt 1)))).isEmpty
#guard (Safety.check (binding (.tyCon "Int" []) (.lit (.litMachineInt 1)))).isEmpty
#guard !(Safety.check (binding
  (.tyFun (.tyCon "List" [.tyCon "Word" []]) (.tyCon "Integer" []))
  (.lit (.litInt 1)))).isEmpty
#guard Safety.usesType "Int" {
  binds := [], instances := [],
  typeDecls := [{ name := "Hidden", kind := "data", ctors := [
    { name := "Hidden", fields := [{ name := "counter", ty := .tyCon "Int" [] }] }] }] }

-- Check references before dictionary/type erasure, including a producer used
-- as a first-class value and a partial operation hidden in a local binding.
#guard (Safety.check (binding (.tyVar "a") (.var {
  name := "GHC.Enum.enumFromThenTo", unique := 2, ty := .tyVar "a", role := .id }))).any
    (·.code == "potentially-infinite")
#guard (Safety.check (binding (.tyCon "Integer" []) (.let_
  (.nonRec { name := "helper", unique := 3, ty := .tyVar "a", role := .id }
    (.var { name := "GHC.List.head", unique := 4, ty := .tyVar "a", role := .id }))
  (.lit (.litInt 1))))).any (·.code == "partial-operation")

private def lcmVar : Var :=
  { name := "GHC.Real.lcm", unique := 5, ty := .tyVar "a", role := .id }

private def intVar : Var :=
  { name := "x", unique := 6, ty := .tyCon "Int" [], role := .id }

private def apply2 (f a b : Expr) : Expr := .app (.app f a) b

-- Dynamic `lcm` is partial for machine Int: its internal quotient can evaluate
-- minBound / -1. A fixed even second argument rules that case out.
#guard (Safety.check (binding (.tyCon "Int" [])
  (apply2 (.var lcmVar) (.var intVar) (.lit (.litMachineInt 3))))).any
    (·.code == "partial-operation")
#guard (Safety.check (binding (.tyCon "Int" [])
  (apply2 (.var lcmVar) (.var intVar) (.lit (.litMachineInt 2))))).isEmpty
#guard (Safety.check (binding (.tyCon "Int" []) (.var lcmVar))).any
    (·.code == "partial-operation")
