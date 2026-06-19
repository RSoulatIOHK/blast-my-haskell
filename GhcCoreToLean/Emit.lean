import GhcCoreToLean.AST
import GhcCoreToLean.Maps

namespace GHCCore.Emit
open GHCCore.Maps

/-! ## Name sanitization -/

private def leanKeywords : List String :=
  ["match", "let", "fun", "def", "if", "then", "else", "by", "where", "with",
   "do", "return", "have", "show", "from", "type", "sort", "Prop", "Type"]

private def isLeanIdChar (c : Char) : Bool :=
  c.isAlphanum || c = '_' || c = '\''

private def sanitizeChar : Char → String
  | '$' => "_dollar_"
  | '#' => "_hash_"
  | '.' => "_dot_"
  | '=' => "_eq_"
  | '/' => "_slash_"
  | '+' => "_plus_"
  | '-' => "_minus_"
  | '*' => "_star_"
  | '<' => "_lt_"
  | '>' => "_gt_"
  | '!' => "_bang_"
  | '?' => "_q_"
  | '\'' => "'"
  | c   => if isLeanIdChar c then String.singleton c else "_"

def sanitize (s : String) : String :=
  let mapped := s.foldl (fun acc c => acc ++ sanitizeChar c) ""
  if leanKeywords.contains mapped then s!"«{mapped}»" else mapped

/-- Type-variable identifier. GHC names bound type-variable *occurrences* with
    synthetic names like `_v3537` (the readable forall binder name `b` is on the
    `ForAll` node, not the occurrences). We emit occurrences and their implicit
    binders through this single function so both sides match, and we avoid a
    leading underscore so the result is an ordinary identifier. -/
def tyVarId (n : String) : String :=
  let s := sanitize n
  if s.startsWith "_" then "t" ++ s else s

/-- A local binder is emitted as `<sanitize>_<unique>` so multiple GHC
    binders that happen to share a name (e.g. `ds` rebound by nested
    case-alts) get distinct Lean identifiers. -/
def localId (v : Var) : String :=
  s!"{sanitize v.name}_{v.unique}"

/-- Render a module-qualified GHC name (e.g. `Ratio.addRatio`) as a Lean
    qualified identifier, sanitizing each dotted component. A reference into a
    transpiled dependency resolves against that module's `namespace`. -/
def qualifyName (n : Name) : String :=
  String.intercalate "." ((n.splitOn ".").map sanitize)

/-- For a Var reference: bare name if it's a known top-level binding,
    `<name>_<unique>` otherwise. Top-level names are resolved against
    a set of names collected from the program. -/
def refId (topNames : List Name) (v : Var) : String :=
  if topNames.contains v.name then sanitize v.name
  -- A module-qualified name that isn't a local top-level binder is an external
  -- reference (into an imported dependency); emit it qualified, not as a
  -- unique-suffixed local id. Builtins were already resolved upstream (valueMap
  -- / dataConMap), so a surviving dotted name is a cross-module user ref.
  else if v.name.contains '.' then qualifyName v.name
  else localId v

/-! ## Recursion detection -/

mutual
  partial def occursInExpr (n : Name) : Expr → Bool
    | .var v       => v.name == n
    | .lit _       => false
    | .app f a     => occursInExpr n f || occursInExpr n a
    | .lam _ b     => occursInExpr n b
    | .let_ bnd b  => occursInBind n bnd || occursInExpr n b
    | .case_ s _ _ alts =>
      occursInExpr n s || alts.any (fun (.mk _ _ r) => occursInExpr n r)
    | .cast e      => occursInExpr n e
    | .tick e      => occursInExpr n e
    | .type_ _     => false

  partial def occursInBind (n : Name) : Bind → Bool
    | .nonRec _ e => occursInExpr n e
    | .rec_ pairs => pairs.any (fun (_, e) => occursInExpr n e)
end

/-! ## Type emission -/

partial def emitType : GHCType → String
  | .tyVar n         => tyVarId n
  | .tyFun a r       => s!"({emitType a} → {emitType r})"
  | .tyApp f x       => s!"({emitType f} {emitType x})"
  | .forAll v b      => s!"(∀ ({v} : Type), {emitType b})"
  | .tyCon name args =>
    let argStrs := args.map emitType
    match typeConMap name argStrs with
    | some lean => lean
    | none      =>
      let argSpaced := String.intercalate " " (argStrs.map (s!"({·})"))
      if args.isEmpty then s!"(GHCCore.tyConOpaque \"{name}\")"
      else s!"((GHCCore.tyConOpaque \"{name}\") {argSpaced})"
  | .tyLit (.nat n)  => toString n
  | .tyLit (.str s)  => s!"\"{s}\""

/-! ## Literal emission -/

def emitLiteral : Literal → String
  | .litInt n    => s!"({n} : Int)"
  | .litWord n   => s!"({n} : Nat)"
  | .litFloat f  => s!"({f} : Float)"
  | .litDouble f => s!"({f} : Float)"
  | .litString s => s!"\"{s}\""
  | .litChar c   => s!"'{c}'"
  | .litLabel l  => s!"GHCCore.foreignLabel \"{l}\""

def emitLiteralPattern : Literal → String
  | .litInt n    => toString n
  | .litWord n   => toString n
  | .litFloat f  => toString f
  | .litDouble f => toString f
  | .litString s => s!"\"{s}\""
  | .litChar c   => s!"'{c}'"
  | .litLabel _  => "_"

/-! ## Var emission -/

/-- Map a Var reference. Mapped value-map hits short-circuit; top-level
    refs use bare names; locals get unique-suffixed. -/
def emitVar (topNames : List Name) (v : Var) : String :=
  match valueMap v.name with
  | some lean => lean
  | none      =>
    -- A data constructor can appear in value position (e.g. `Just x`), not
    -- just in a pattern; resolve those through dataConMap as well.
    match dataConMap v.name with
    | some lean => lean
    | none      => refId topNames v

/-! ## Alts -/

/-- DEFAULT alt must come last in a Lean `match`. -/
def reorderAlts (alts : List Alt) : List Alt :=
  let (defaults, others) := alts.partition fun
    | .mk .default _ _ => true
    | _                => false
  others ++ defaults

def emitAltPattern (con : AltCon) (bndrs : List Var) : String :=
  match con with
  | .default      => "_"
  | .litAlt l     => emitLiteralPattern l
  | .dataCon name =>
    -- Tuple patterns use Lean's anonymous-tuple syntax `(x, y, …)`, which
    -- right-nests for any arity (so 3-tuples are fine here). The pattern-
    -- position ctor name is bare `(,)`/`(,,)`; qualified forms covered too.
    if name == "(,)" || name == "(,,)"
       || name == "GHC.Tuple.(,)" || name == "GHC.Tuple.(,,)" then
      let bs := String.intercalate ", " (bndrs.map localId)
      s!"({bs})"
    else
      let resolved := (dataConMap name).getD (sanitize name)
      if bndrs.isEmpty then resolved
      else
        let bs := String.intercalate " " (bndrs.map localId)
        s!"{resolved} {bs}"

/-! ## Bottoms (error / undefined) -/

/-- Haskell `error`/`undefined` are bottoms. GHC expands them with their
    `HasCallStack` machinery (`pushCallStack`, `SrcLoc`, `unpackCString#`, …),
    which has no Lean image. We collapse any application whose spine head is
    one of these to `default` — a *total, sound* bottom: unlike `sorry` it
    reduces to a concrete value, so it does not taint proofs that reduce
    through it. This needs `Inhabited` of the result type; data decls derive
    it, and `emitDefHeader` adds an `[Inhabited t]` binder when a body has a
    bottom whose type is a free type variable. -/
private def isBottomName : Name → Bool
  | "GHC.Err.error" | "error"
  | "GHC.Err.errorWithoutStackTrace" | "errorWithoutStackTrace"
  | "GHC.Err.undefined" | "undefined"
  -- Partial list functions: ⊥ on the empty list. Qualified names only — a
  -- user could define a *total* `head`/`tail`/`init`, and collapsing that to
  -- `default` would be an unsound silent miscompile. Core references these
  -- partials qualified, so the bare forms are never needed (cf. the bare-name
  -- rule for `valueMap`). The `!!` operator can't be user-shadowed harmfully,
  -- but is kept qualified for uniformity.
  | "GHC.List.head" | "GHC.List.tail"
  | "GHC.List.last" | "GHC.List.init"
  | "GHC.List.!!"
  -- Partial Maybe eliminator: ⊥ on Nothing.
  | "Data.Maybe.fromJust" => true
  | _ => false

private partial def appHeadName : Expr → Option Name
  | .var v   => some v.name
  | .app f _ => appHeadName f
  | .cast e  => appHeadName e
  | .tick e  => appHeadName e
  | _        => none

/-- Does any subexpression apply a bottom (`error`/`undefined`)? Used to decide
    whether a def's polymorphic result needs an `[Inhabited t]` binder so the
    emitted `default` elaborates. -/
private partial def exprHasBottom : Expr → Bool
  | .var _   => false
  | .lit _   => false
  | .app f a =>
    (match appHeadName f with | some n => isBottomName n | none => false)
      || exprHasBottom f || exprHasBottom a
  | .lam _ b => exprHasBottom b
  | .let_ b body =>
    (match b with
     | .nonRec _ e => exprHasBottom e
     | .rec_ ps    => ps.any (fun p => exprHasBottom p.2))
      || exprHasBottom body
  | .case_ scr _ _ alts =>
    exprHasBottom scr || alts.any (fun al => match al with | .mk _ _ r => exprHasBottom r)
  | .cast e  => exprHasBottom e
  | .tick e  => exprHasBottom e
  | _        => false

/-! ## Expr emission -/

mutual
  partial def emitExpr (top : List Name) : Expr → String
    | .var v   => emitVar top v
    | .lit l   => emitLiteral l
    | .app f a =>
      match appHeadName f with
      | some n => if isBottomName n then "default"
                  else s!"({emitExpr top f}) ({emitExpr top a})"
      | none   => s!"({emitExpr top f}) ({emitExpr top a})"
    | .lam v body =>
      s!"(fun {localId v} => {emitExpr top body})"
    | .let_ b body =>
      s!"({emitLet top b}\n{emitExpr top body})"
    | .case_ scr _cb _ty alts =>
      let alts'   := reorderAlts alts
      let altsStr := alts'.map (emitAlt top)
      let header  := s!"(match {emitExpr top scr} with"
      let body    := String.intercalate "\n" altsStr
      s!"{header}\n{body})"
    | .cast e  => emitExpr top e
    | .tick e  => emitExpr top e
    | .type_ _ => "(GHCCore.typeArg : GHCCore.GHCType)"

  partial def emitAlt (top : List Name) : Alt → String
    | .mk con bndrs rhs =>
      s!"| {emitAltPattern con bndrs} => {emitExpr top rhs}"

  partial def emitLet (top : List Name) : Bind → String
    | .nonRec v e =>
      s!"let {localId v} := {emitExpr top e}"
    | .rec_ pairs =>
      let lines := pairs.map fun (v, e) =>
        s!"  {localId v} := {emitExpr top e}"
      let body := String.intercalate "\n" lines
      s!"-- TODO: local Rec let unsupported, emitted as opaque\n{body}"
end

/-! ## Def-header construction -/

private partial def peelLams : Expr → List Var × Expr
  | .lam v body =>
    let (vs, b) := peelLams body
    (v :: vs, b)
  | other       => ([], other)

private partial def stripFunTys : Nat → GHCType → GHCType
  | 0,     t            => t
  | n+1, .tyFun _ r     => stripFunTys n r
  | n+1, .forAll _ body => stripFunTys (n+1) body
  | _,     t            => t

/-- Argument types taken from the def's *signature* (not the term-lambda
    binders). GHC alpha-renames type variables between a function's type and
    its lambda binders, so the binder type `(Int → Int → _v4550)` and the
    result type `_v3537` disagree even though both are the same variable `b`.
    Reading both from the signature keeps the names consistent so the implicit
    binder unifies them. Forall nodes are skipped without consuming an arg. -/
private partial def headerArgTys : List Var → GHCType → List GHCType
  | [],          _            => []
  | (a :: as), .forAll _ body => headerArgTys (a :: as) body
  | (_ :: as), .tyFun ta r    => ta :: headerArgTys as r
  | (a :: as), _              => a.ty :: headerArgTys as a.ty

/-- Free type variables appearing in a type, in first-occurrence order. -/
private partial def collectTyVars : GHCType → List Name
  | .tyVar n      => [n]
  | .tyApp f x    => collectTyVars f ++ collectTyVars x
  | .tyFun a r    => collectTyVars a ++ collectTyVars r
  | .forAll _ b   => collectTyVars b
  | .tyCon _ args => args.flatMap collectTyVars
  | .tyLit _      => []

private def dedup (xs : List Name) : List Name :=
  xs.foldl (init := []) fun acc x => if acc.contains x then acc else acc ++ [x]

/-- GHC class-method bindings are named `$c<op>` (e.g. `$c==`). With more than
    one instance of a class these collide after sanitization, so we suffix them
    with their unique (like a local). -/
private def isClassMethodName (n : Name) : Bool := n.startsWith "$c"

private def defNameId (v : Var) : String :=
  if isClassMethodName v.name then localId v else sanitize v.name

private def emitDefHeader (top : List Name) (v : Var) (args : List Var)
                          (resTy : GHCType) (rhsBody : Expr) (rec? : Bool) : String :=
  let name     := defNameId v
  let argTys   := headerArgTys args v.ty
  let argStrs  := (args.zip argTys).map (fun (a, t) => s!"({localId a} : {emitType t})")
  let argStr   := String.intercalate " " argStrs
  -- Implicit `{t : Type}` binders for every free type variable in the
  -- signature, so polymorphic defs (e.g. continuation glue) type-check.
  let tyvars   := dedup (collectTyVars v.ty)
  -- A body containing a bottom emits `default`; when the bottom's type is a
  -- free type variable, that needs an `[Inhabited t]` binder to elaborate.
  let needInhab := exprHasBottom rhsBody
  let implStr  := String.intercalate " " (tyvars.map (fun t =>
    let tv := tyVarId t
    if needInhab then s!"\{{tv} : Type} [Inhabited {tv}]"
    else s!"\{{tv} : Type}"))
  let binders  := String.intercalate " " (List.filter (· != "") [implStr, argStr])
  let resStr   := emitType resTy
  let body     := emitExpr top rhsBody
  let head     :=
    if binders.isEmpty then s!"def {name} : {resStr} :="
    else s!"def {name} {binders} : {resStr} :="
  let term     :=
    if rec? then "\ndecreasing_by all_goals sorry"
    else ""
  s!"{head}\n  {body}{term}"

/-! ## Top-level binds -/

private def emitBind (top : List Name) (b : Bind) : String :=
  match b with
  | .nonRec v e =>
    let (args, body) := peelLams e
    let resTy        := stripFunTys args.length v.ty
    let rec?         := occursInExpr v.name e
    emitDefHeader top v args resTy body rec?
  | .rec_ pairs =>
    match pairs with
    | [(v, e)] =>
      let (args, body) := peelLams e
      let resTy        := stripFunTys args.length v.ty
      let rec?         := occursInExpr v.name e
      emitDefHeader top v args resTy body rec?
    | _        =>
      let defs := pairs.map fun (v, e) =>
        let (args, body) := peelLams e
        let resTy        := stripFunTys args.length v.ty
        emitDefHeader top v args resTy body true
      let body := String.intercalate "\n" defs
      s!"mutual\n{body}\nend"

/-- Collect the names of every top-level binder in a program. -/
private def collectTopNames (p : CoreProgram) : List Name :=
  p.foldl (init := []) fun acc b => match b with
    | .nonRec v _ => v.name :: acc
    | .rec_ pairs => pairs.foldl (init := acc) fun acc (v, _) => v.name :: acc

def emitProgram (p : CoreProgram) : String :=
  let top      := collectTopNames p
  let bindStrs := p.map (emitBind top)
  String.intercalate "\n\n" bindStrs

/-- Like `emitProgram`, but extends the "top-level names" set with extra
    names that should NOT get a `_unique` suffix when emitted as Var refs.
    The intended use is to splice in user-declared data constructors so
    `App (Var Foo) ...` becomes `Foo a b`, not `Foo_3490`. -/
def emitProgramWith (p : CoreProgram) (extraTopNames : List Name) : String :=
  let top      := extraTopNames ++ collectTopNames p
  let bindStrs := p.map (emitBind top)
  String.intercalate "\n\n" bindStrs

/-! ## Data type declarations and instances -/

/-- Emit a Haskell `data T = …` declaration as a Lean `inductive`. Bare
    constructor uses are *not* brought into scope via `open T` — that makes
    `T` ambiguous between the type and the ctor in Lean's elaborator. The
    body post-passes rewrite Haskell-style refs to the qualified `T.C` form.
    Field selectors GHC auto-generates are emitted alongside as regular
    defs. -/
def emitDataDecl (d : DataDecl) : String :=
  let leanName := sanitize d.name
  let ctorLines := d.ctors.map fun c =>
    let argTys := c.fields.map (emitType ·.ty)
    let arrows := argTys.foldr (init := leanName) fun a acc => s!"{a} → {acc}"
    s!"  | {sanitize c.name} : {arrows}"
  let body := String.intercalate "\n" ctorLines
  -- `Inhabited` so emitted `default` bottoms whose result is this type elaborate.
  s!"inductive {leanName} where\n{body}\nderiving Repr, Inhabited"

private partial def firstValArgTy : GHCType → Option GHCType
  | .forAll _ b => firstValArgTy b
  | .tyFun a _  => some a
  | _           => none

/-- Find the `$c==` binding belonging to the instance whose head type matches,
    returning its emitted (unique-suffixed) def name. Multiple `Eq` instances
    each produce a `$c==` binding; they collide after sanitization, so the def
    names are unique-suffixed (see `defNameId`) and we disambiguate here by
    matching the method's first argument type against the instance head. -/
private def findEqMethod (binds : CoreProgram) (headTyStr : String) : Option String :=
  let matchesHead (v : Var) : Bool :=
    v.name == "$c==" &&
      (match firstValArgTy v.ty with
       | some t => emitType t == headTyStr
       | none   => false)
  binds.findSome? fun b => match b with
    | .nonRec v _ => if matchesHead v then some (localId v) else none
    | .rec_ pairs => (pairs.find? (fun (v, _) => matchesHead v)).map (fun (v, _) => localId v)

/-- Emit a Lean `instance` block. Only `Eq` → Lean `BEq` is wired for now.
    Returns `none` for classes we don't model (Show, Read, etc.) so the
    caller can skip them entirely. -/
def emitInstance (binds : CoreProgram) (i : Instance) : Option String :=
  let tyStr := i.headTypes.map emitType |> String.intercalate " "
  match i.className with
  | "Eq" =>
    match findEqMethod binds tyStr with
    | some methodRef => some s!"instance : BEq {tyStr} where\n  beq := {methodRef}"
    | none           => none
  | _ => none

/-- Build a user-data-constructor-name map from the typeDecls. This lets
    the Lean emitter rewrite `case x of CustomRatio …` patterns to use the
    Lean structure's `.mk` (or anonymous) form. -/
def userDataConMap (decls : List DataDecl) : Name → Option String := fun n =>
  decls.findSome? fun d =>
    d.ctors.findSome? fun c =>
      if c.name == n then
        if d.ctors.length == 1 && c.fields.all (·.name != "_") then
          -- Single-ctor structure → use .mk
          some s!"{sanitize d.name}.mk"
        else
          some (sanitize c.name)
      else none

/-- Rewrite occurrences of `(GHCCore.tyConOpaque "X")` to the bare name `X`
    for every user-declared type. The Core dump types user types as opaque
    (since the shim doesn't know the lakefile's type-ctor map); after the
    transpiler emits `inductive X where …`, opaque references should resolve
    to that inductive directly. -/
def resolveUserTypes (decls : List DataDecl) (src : String) : String :=
  decls.foldl (init := src) fun s d =>
    let needle := s!"(GHCCore.tyConOpaque \"{d.name}\")"
    let replacement := sanitize d.name
    s.replace needle replacement

/-- Qualify user-defined data constructors in any position where Lean's
    elaborator would otherwise be ambiguous (type vs. ctor under the same
    name). Three call-shapes are recognised:

      *  `| Ctor `                              ← alt-pattern
      *  `(Ctor)`                               ← App in transpiler-emitted style
      *  `Ctor (` (preceded by whitespace)      ← App in user `[lean| … |]` spec

    Type annotations like `(x : T)` or `→ T →` don't match any of these
    needles, so they remain `T` and resolve to the type. -/
def resolveUserCtors (decls : List DataDecl) (src : String) : String :=
  decls.foldl (init := src) fun s d =>
    d.ctors.foldl (init := s) fun s c =>
      let bareCtor := sanitize c.name
      let qualCtor := s!"{sanitize d.name}.{bareCtor}"
      let rules : List (String × String) :=
        [ (s!"| {bareCtor} ",  s!"| {qualCtor} ")
        , (s!"({bareCtor})",   s!"({qualCtor})")
        , (s!" {bareCtor} (",  s!" {qualCtor} (")
        , (s!"({bareCtor} (",  s!"({qualCtor} (") ]
      rules.foldl (init := s) fun s (needle, repl) => s.replace needle repl

/-- Rewrite `(GHCCore.tyConOpaque "T")` → `M.T` for each external type `T`
    declared in a transpiled dependency module `M` (built from the dependency
    `.decls.json`). Applied after `resolveUserTypes`, so locally-declared types
    are already bare; only imported types are rewritten, and genuinely unknown
    types stay opaque. -/
def resolveExternalTypes (extTypes : List (String × String)) (src : String) : String :=
  extTypes.foldl (init := src) fun s (tyName, modName) =>
    let needle      := s!"(GHCCore.tyConOpaque \"{tyName}\")"
    let replacement := s!"{modName}.{sanitize tyName}"
    s.replace needle replacement

/-- Apply the same name-resolution post-passes used on emitted bodies to a
    single user spec string: local types → bare, imported types → `M.T`,
    user ctors → `T.C`. -/
def resolveSpecText (typeDecls : List DataDecl) (extTypes : List (String × String))
    (s : String) : String :=
  resolveExternalTypes extTypes (resolveUserCtors typeDecls (resolveUserTypes typeDecls s))

/-- Top-level entry: emit a full Program (data decls, value defs, instances).
    The user-type and user-ctor post-passes are applied only to the
    value-binding / instance sections; the data declarations themselves
    must keep their original names. `extTypes` maps imported type names to
    their defining module so cross-module references resolve. -/
def emitFullProgram (extTypes : List (String × String)) (p : Program) : String :=
  -- User-declared ctors (e.g. `CustomRatio`) participate in the top-name
  -- set so App-position refs to them emit bare, not as `Name_<unique>`.
  let ctorNames : List Name :=
    p.typeDecls.flatMap fun d => d.ctors.map (·.name)
  let datas := p.typeDecls.map emitDataDecl
  let binds := emitProgramWith p.binds ctorNames
  let insts := p.instances.filterMap (emitInstance p.binds)
  let bodyRaw :=
    (if binds.isEmpty then "" else binds)
      ++ (if insts.isEmpty then "" else "\n\n" ++ String.intercalate "\n\n" insts)
  let bodyResolved := resolveUserTypes p.typeDecls bodyRaw
                    |> resolveUserCtors p.typeDecls
  let dataBlock :=
    if datas.isEmpty then "" else String.intercalate "\n\n" datas
  let sections := List.filter (· != "") [dataBlock, bodyResolved]
  -- External-type resolution runs over the whole output (data fields included);
  -- it only rewrites imported types, so local inductive names are untouched.
  resolveExternalTypes extTypes (String.intercalate "\n\n" sections)

end GHCCore.Emit
