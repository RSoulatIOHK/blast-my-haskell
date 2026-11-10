import GhcCoreToLean.AST

namespace GHCCore.Select

/- Collect variable uniques referenced by a Core expression. Only uniques
    belonging to top-level bindings participate in the closure below. -/
mutual
  private partial def refs : Expr → List Unique
    | .var v => [v.unique]
    | .app f a => refs f ++ refs a
    | .lam _ body | .cast body | .tick body => refs body
    | .let_ b body => bindRefs b ++ refs body
    | .case_ scr _ _ alts =>
        refs scr ++ alts.flatMap (fun (.mk _ _ rhs) => refs rhs)
    | _ => []

  private partial def bindRefs : Bind → List Unique
    | .nonRec _ rhs => refs rhs
    | .rec_ pairs => pairs.flatMap (fun (_, rhs) => refs rhs)
end

private def topPairs (binds : CoreProgram) : List (Var × Expr) :=
  binds.flatMap fun
    | .nonRec v rhs => [(v, rhs)]
    | .rec_ pairs => pairs

private partial def closure (pairs : List (Var × Expr))
    (pending visited : List Unique) : List Unique :=
  match pending with
  | [] => visited
  | id :: rest =>
      if visited.contains id then closure pairs rest visited
      else
        match pairs.find? (fun (v, _) => v.unique == id) with
        | none => closure pairs rest (id :: visited)
        | some (_, rhs) => closure pairs (refs rhs ++ rest) (id :: visited)

/-- Retain named roots and the transitive top-level Core bindings they use.
    Root names must identify exactly one binding. The caller must separately
    validate local type, class, and instance metadata before using a slice. -/
def selectRoots (binds : CoreProgram) (roots : List Name) : Except String CoreProgram := do
  if roots.isEmpty then throw "At least one Core root is required"
  let pairs := topPairs binds
  let mut ids : List Unique := []
  for name in roots do
    let found := pairs.filter (fun (v, _) => v.name == name)
    match found with
    | [(v, _)] => ids := v.unique :: ids
    | [] => throw s!"Unknown Core root: {name}"
    | _ => throw s!"Ambiguous Core root: {name}"
  let selected := closure pairs ids []
  return binds.filterMap fun
    | .nonRec v rhs =>
        if selected.contains v.unique then some (.nonRec v rhs) else none
    | .rec_ group =>
        let kept := group.filter (fun (v, _) => selected.contains v.unique)
        if kept.isEmpty then none else some (.rec_ kept)

end GHCCore.Select
