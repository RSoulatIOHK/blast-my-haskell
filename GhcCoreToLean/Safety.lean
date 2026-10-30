import GhcCoreToLean.AST

namespace GHCCore.Safety

/-- Conservative exclusions for known semantic approximations. These checks
    deliberately over-reject; passing them is not a soundness theorem. -/
structure Issue where
  code : String
  owner : String
  detail : String
deriving Inhabited, Repr

private def machineTypes : List String :=
  ["Word", "Word#", "Float", "Float#", "Double", "Double#",
   "Int8", "Int16", "Int32", "Int64", "Word8", "Word16", "Word32", "Word64"]

private def baseName (n : String) : String := (n.splitOn ".").getLast!

private partial def typeUses (wanted : String) : GHCType → Bool
  | .tyCon n args => baseName n == wanted || args.any (typeUses wanted)
  | .tyApp a b | .tyFun a b => typeUses wanted a || typeUses wanted b
  | .forAll _ t => typeUses wanted t
  | _ => false

mutual
  private partial def exprUsesType (wanted : String) : Expr → Bool
    | .var v => typeUses wanted v.ty
    | .app f a => exprUsesType wanted f || exprUsesType wanted a
    | .lam v e => typeUses wanted v.ty || exprUsesType wanted e
    | .let_ b e => bindUsesType wanted b || exprUsesType wanted e
    | .case_ e v t alts => exprUsesType wanted e || typeUses wanted v.ty || typeUses wanted t ||
        alts.any (fun (.mk _ vs rhs) => vs.any (fun v => typeUses wanted v.ty) || exprUsesType wanted rhs)
    | .cast e | .tick e => exprUsesType wanted e
    | .type_ t => typeUses wanted t
    | _ => false

  private partial def bindUsesType (wanted : String) : Bind → Bool
    | .nonRec v e => typeUses wanted v.ty || exprUsesType wanted e
    | .rec_ pairs => pairs.any (fun (v, e) => typeUses wanted v.ty || exprUsesType wanted e)
end

/-- Whether a program's Core or declaration metadata mentions a type constructor
    by basename. Used to select the machine-`Int` spelling in user specs. -/
def usesType (wanted : String) (p : Program) : Bool :=
  p.binds.any (bindUsesType wanted) ||
  p.typeDecls.any (fun d => d.ctors.any (fun c => c.fields.any (fun f => typeUses wanted f.ty))) ||
  p.classDecls.any (fun c => c.methods.any (fun m => typeUses wanted m.ty)) ||
  p.instances.any (fun i => i.headTypes.any (typeUses wanted))

private partial def typeIssues (owner : String) : GHCType → List Issue
  | .tyCon n args =>
    (if machineTypes.contains (baseName n) then
      [{ code := "machine-number", owner,
         detail := s!"{n} is not modeled with its Haskell machine semantics" }] else [])
      ++ args.flatMap (typeIssues owner)
  | .tyApp a b | .tyFun a b => typeIssues owner a ++ typeIssues owner b
  | .forAll _ t => typeIssues owner t
  | _ => []

private def operationIssues (owner n : String) : List Issue :=
  if ["GHC.Enum.enumFromThenTo", "GHC.Enum.enumFrom", "GHC.Enum.enumFromThen",
      "GHC.List.iterate", "GHC.List.repeat", "GHC.List.cycle"].contains n then
    [{ code := "potentially-infinite", owner,
       detail := s!"{n} requires a finite-observation model or a proved finiteness condition" }]
  else if ["GHC.Err.error", "error", "GHC.Err.errorWithoutStackTrace",
      "errorWithoutStackTrace", "GHC.Err.undefined", "undefined", "GHC.List.head",
      "GHC.List.last", "GHC.List.tail", "GHC.List.init", "GHC.List.!!",
      "Data.Maybe.fromJust", "Data.Foldable.maximum", "Data.Foldable.minimum",
      "GHC.List.maximum", "GHC.List.minimum"].contains n then
    [{ code := "partial-operation", owner,
       detail := s!"{n} requires a checked domain condition; its total Lean image is insufficient" }]
  else []

private def divisionNames : List String :=
  ["GHC.Real.div", "GHC.Real.mod", "GHC.Real.quot", "GHC.Real.rem",
   "GHC.Real.divMod", "GHC.Real.quotRem"]

private def lcmNames : List String := ["GHC.Real.lcm", "lcm"]

private partial def appSpine (e : Expr) (args : List Expr := []) : Expr × List Expr :=
  match e with
  | .app f a => appSpine f (a :: args)
  | head => (head, args)

private def isErasedArg : Expr → Bool
  | .type_ _ | .coercion => true
  | .var v => v.role == .dict
  | _ => false

private partial def machineLiteral (e : Expr) : Option Int :=
  match e with
  | .lit (.litMachineInt n) => some n
  | .app f arg =>
    match f with
    | .var v => if ["GHC.Types.I#", "I#"].contains v.name then machineLiteral arg else none
    | _ =>
      let (head, args) := appSpine e
      match head with
      | .var op =>
        if ["GHC.Num.negate", "negate"].contains op.name then
          match args.filter (fun a => !isErasedArg a) with
          | [value] => (machineLiteral value).map (-·)
          | _ => none
        else none
      | _ => none
  | _ => none

private def divisionIssue (owner : String) (e : Expr) : List Issue :=
  let (head, args) := appSpine e
  match head with
  | .var v =>
    if !divisionNames.contains v.name then [] else
      let runtimeArgs := args.filter (fun a => !isErasedArg a)
      match runtimeArgs.reverse with
      | divisor :: numerator :: _ =>
        match machineLiteral divisor with
        | some 0 => [Issue.mk "partial-operation" owner
            "division has a statically zero divisor"]
        | some (-1) =>
          match machineLiteral numerator with
          | some n => if n == -9223372036854775808 then
              [Issue.mk "partial-operation" owner
                "division overflows on minBound divided by -1"]
            else []
          | none => [Issue.mk "partial-operation" owner
              "division with divisor -1 may overflow at minBound"]
        | some _ => []
        | none => [Issue.mk "partial-operation" owner
            "division has a dynamic divisor; prove or specialize it as nonzero"]
      | _ => [Issue.mk "partial-operation" owner
          "division is used without a statically checked divisor"]
  | _ => []

/-- `base` implements `lcm a b` using `a quot gcd a b`. On a fixed-width
    `Int`, that internal quotient can raise arithmetic overflow even though the
    surrounding multiplication and absolute value wrap. An even second
    argument guarantees that `gcd minBound b` cannot be `-1`; a statically
    non-minimum first argument is also safe. The deliberately narrow test keeps
    conservative mode honest until exceptions are modeled explicitly. -/
private def lcmIssue (owner : String) (e : Expr) : List Issue :=
  let (head, args) := appSpine e
  match head with
  | .var v =>
    if !lcmNames.contains v.name then [] else
      let runtimeArgs := args.filter (fun a => !isErasedArg a)
      match runtimeArgs with
      | first :: second :: _ =>
        match machineLiteral first, machineLiteral second with
        | some a, _ =>
          if a != -9223372036854775808 then []
          else match machineLiteral second with
            | some b => if b % 2 == 0 then [] else
                [Issue.mk "partial-operation" owner
                  "lcm may overflow in its internal minBound quotient"]
            | none => [Issue.mk "partial-operation" owner
                "lcm may overflow in its internal minBound quotient"]
        | none, some b => if b % 2 == 0 then [] else
            [Issue.mk "partial-operation" owner
              "lcm with a dynamic first argument may overflow internally"]
        | none, none => [Issue.mk "partial-operation" owner
            "lcm with dynamic arguments may overflow internally"]
      | _ => [Issue.mk "partial-operation" owner
          "lcm is used without statically checked arguments"]
  | _ => []

mutual
  private partial def exprIssues (owner : String) (asAppHead : Bool := false) : Expr → List Issue
    | .var v => typeIssues owner v.ty ++ operationIssues owner v.name
        ++ (if !asAppHead && divisionNames.contains v.name then divisionIssue owner (.var v) else [])
        ++ (if !asAppHead && lcmNames.contains v.name then lcmIssue owner (.var v) else [])
    | e@(.app f a) => (if asAppHead then [] else divisionIssue owner e ++ lcmIssue owner e)
        ++ exprIssues owner true f ++ exprIssues owner false a
    | .lam v e => typeIssues owner v.ty ++ exprIssues owner false e
    | .let_ b e => bindIssues b ++ exprIssues owner false e
    | .case_ e v t alts => exprIssues owner false e ++ typeIssues owner v.ty
        ++ typeIssues owner t ++ alts.flatMap (fun (.mk _ vs rhs) =>
          vs.flatMap (fun v => typeIssues owner v.ty) ++ exprIssues owner false rhs)
    | .cast e | .tick e => exprIssues owner false e
    | .type_ t => typeIssues owner t
    | _ => []

  private partial def bindIssues : Bind → List Issue
    | .nonRec v e => typeIssues v.name v.ty ++ exprIssues v.name false e
    | .rec_ pairs => pairs.flatMap (fun (v, e) =>
        typeIssues v.name v.ty ++ exprIssues v.name false e)
end

def check (p : Program) : List Issue :=
  let issues := p.binds.flatMap bindIssues
    ++ p.typeDecls.flatMap (fun d => d.ctors.flatMap (fun c =>
      c.fields.flatMap (fun f => typeIssues s!"{d.name}.{f.name}" f.ty)))
    ++ p.instances.flatMap (fun i => i.headTypes.flatMap (typeIssues i.dfunName))
    ++ p.classDecls.flatMap (fun c => c.methods.flatMap (fun m =>
      typeIssues s!"{c.name}.{m.name}" m.ty))
  issues.foldl (fun acc i =>
    if acc.any (fun j => j.code == i.code && j.owner == i.owner && j.detail == i.detail)
    then acc else acc ++ [i]) []

end GHCCore.Safety
