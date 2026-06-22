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

/-- Map a Var reference. A class-method selector (in `methodMap`) emits
    `Class.method`; otherwise value-map hits short-circuit; top-level refs use
    bare names; locals get unique-suffixed. -/
def emitVar (methodMap : List (Name × Name)) (topNames : List Name) (v : Var) : String :=
  match methodMap.find? (·.1 == v.name) with
  | some (_, cls) => s!"{sanitize cls}.{sanitize v.name}"
  | none      =>
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
  | "GHC.Err.undefined" | "undefined" => true
  | _ => false

/-- Partial functions whose *faithful* `valueMap` image uses `default` on the
    ⊥ part of their domain (`head`/`last`/`!!`/`fromJust`). They are NOT bottoms
    — they do not collapse to `default` everywhere (that would be unsound on the
    defined domain, e.g. `head [1,2,3]`). But because their emitted term mentions
    `default`, a polymorphic def using one needs an `[Inhabited t]` binder, so
    `exprHasBottom` must see through to them. (`tail`→`List.tail` and
    `init`→`List.dropLast` are total with no `default`, so they're not listed.) -/
private def isPartialDefaultName : Name → Bool
  | "GHC.List.head" | "GHC.List.last" | "GHC.List.!!"
  | "Data.Maybe.fromJust" => true
  | _ => false

private partial def appHeadName : Expr → Option Name
  | .var v   => some v.name
  | .app f _ => appHeadName f
  | .cast e  => appHeadName e
  | .tick e  => appHeadName e
  | _        => none

/-- Does any subexpression emit a `default`? True for an applied bottom
    (`error`/`undefined`) or an applied partial whose faithful image uses
    `default` (`head`/`last`/`!!`/`fromJust`). Used to decide whether a def's
    polymorphic result needs an `[Inhabited t]` binder so the emitted `default`
    elaborates. -/
private partial def exprHasBottom : Expr → Bool
  | .var _   => false
  | .lit _   => false
  | .app f a =>
    (match appHeadName f with
     | some n => isBottomName n || isPartialDefaultName n
     | none   => false)
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

/-- Peel leading lambdas off an expression, returning the binders and body.
    Hoisted above the emission mutual block so `emitLet` can use it (the other
    `peelLams` lives after the block and is not visible here). -/
private partial def peelLamsLocal : Expr → List Var × Expr
  | .lam v body =>
    let (vs, b) := peelLamsLocal body
    (v :: vs, b)
  | other       => ([], other)

/-! ## Expr emission -/

mutual
  partial def emitExpr (mm : List (Name × Name)) (top : List Name) : Expr → String
    | .var v   => emitVar mm top v
    | .lit l   => emitLiteral l
    | .app f a =>
      match appHeadName f with
      | some n => if isBottomName n then "default"
                  else s!"({emitExpr mm top f}) ({emitExpr mm top a})"
      | none   => s!"({emitExpr mm top f}) ({emitExpr mm top a})"
    | .lam v body =>
      s!"(fun {localId v} => {emitExpr mm top body})"
    | .let_ b body =>
      s!"({emitLet mm top b}\n{emitExpr mm top body})"
    | .case_ scr cb _ty alts =>
      let alts'   := reorderAlts alts
      let altsStr := alts'.map (emitAlt mm top)
      let scrStr  := emitExpr mm top scr
      let body    := String.intercalate "\n" altsStr
      -- GHC binds the case binder to the scrutinee; alts may reference it.
      -- When used, bind it once and match *on the binder* — single evaluation
      -- of the scrutinee, matching Core's semantics. When unused, match the
      -- scrutinee directly.
      let usesCb  := alts.any (fun (.mk _ _ r) => occursInExpr cb.name r)
      if usesCb then
        s!"(let {localId cb} := {scrStr}\n(match {localId cb} with\n{body}))"
      else
        s!"(match {scrStr} with\n{body})"
    | .cast e  => emitExpr mm top e
    | .tick e  => emitExpr mm top e
    | .type_ _ => "(GHCCore.typeArg : GHCCore.GHCType)"

  partial def emitAlt (mm : List (Name × Name)) (top : List Name) : Alt → String
    | .mk con bndrs rhs =>
      s!"| {emitAltPattern con bndrs} => {emitExpr mm top rhs}"

  /-- Emit a single `let rec` binding: peel lambdas into parameters and emit
      `let rec {id} {params} := {body}`. (Lean's `let rec` has no `decreasing_by`,
      so only structurally-decreasing recursion elaborates; non-structural local
      rec is a documented follow-up.) -/
  partial def emitLetRecBinding (mm : List (Name × Name)) (top : List Name) (v : Var) (e : Expr) : String :=
    let (params, body) := peelLamsLocal e
    let paramStr := String.intercalate " " (params.map (fun p => s!"({localId p})"))
    let head := if paramStr.isEmpty then s!"let rec {localId v} :="
                else s!"let rec {localId v} {paramStr} :="
    s!"{head} {emitExpr mm top body}"

  partial def emitLet (mm : List (Name × Name)) (top : List Name) : Bind → String
    | .nonRec v e =>
      -- A `where`-style recursive helper can arrive tagged NonRec while its RHS
      -- references the binder. A plain Lean `let` can't self-reference, so route
      -- self-recursive NonRec bindings through `let rec` too.
      if occursInExpr v.name e then emitLetRecBinding mm top v e
      else s!"let {localId v} := {emitExpr mm top e}"
    | .rec_ pairs =>
      -- Local recursion → `let rec`. Multiple bindings emit as consecutive lines.
      String.intercalate "\n" (pairs.map (fun (v, e) => emitLetRecBinding mm top v e))
end

/-! ## Def-header construction -/

private partial def peelLams : Expr → List Var × Expr
  | .lam v body =>
    let (vs, b) := peelLams body
    (v :: vs, b)
  | other       => ([], other)

/-- Peel leading class-constraint arrows (`C t → …` where `C ∈ classNames`) off a
    def signature, returning the `[C t]` instance-implicit binder strings and the
    remaining (constraint-stripped) type. `∀`-binders are skipped (their tyvars
    are handled by `collectTyVars`). The term-level dict binder is already erased
    by `Lower`, so stripping the dict arrow from the *type* realigns the value
    args / result with the term binders. Stops at the first non-constraint arrow. -/
private partial def stripClassConstraints (classNames : List Name) : GHCType → List String × GHCType
  | .forAll _ b => stripClassConstraints classNames b
  | .tyFun (.tyCon c [.tyVar t]) r =>
    if classNames.contains c then
      let (cs, rest) := stripClassConstraints classNames r
      (s!"[{sanitize c} {tyVarId t}]" :: cs, rest)
    else ([], .tyFun (.tyCon c [.tyVar t]) r)
  | t => ([], t)

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

private def emitDefHeader (mm : List (Name × Name)) (classNames : List Name) (top : List Name)
                          (v : Var) (args : List Var)
                          (resTy : GHCType) (rhsBody : Expr) (rec? : Bool) : String :=
  let name     := defNameId v
  -- Strip class-constraint arrows (`C a =>`) from the signature → `[C a]`
  -- instance-implicit binders; the remaining type aligns with the term binders
  -- (the dict term-binder is already erased by Lower).
  let (constraints, strippedTy) := stripClassConstraints classNames v.ty
  let argTys   := headerArgTys args strippedTy
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
  let constraintStr := String.intercalate " " constraints
  let binders  := String.intercalate " " (List.filter (· != "") [implStr, constraintStr, argStr])
  let resStr   := emitType resTy
  let body     := emitExpr mm top rhsBody
  let head     :=
    if binders.isEmpty then s!"def {name} : {resStr} :="
    else s!"def {name} {binders} : {resStr} :="
  let term     :=
    if rec? then "\ndecreasing_by all_goals sorry"
    else ""
  s!"{head}\n  {body}{term}"

/-! ## Top-level binds -/

def emitBind (mm : List (Name × Name)) (classNames : List Name) (top : List Name) (b : Bind) : String :=
  -- Result type is computed from the constraint-stripped signature so the
  -- erased dict arrow isn't mistaken for a value arg.
  let resTyOf (v : Var) (nargs : Nat) : GHCType :=
    stripFunTys nargs (stripClassConstraints classNames v.ty).2
  match b with
  | .nonRec v e =>
    let (args, body) := peelLams e
    let resTy        := resTyOf v args.length
    let rec?         := occursInExpr v.name e
    emitDefHeader mm classNames top v args resTy body rec?
  | .rec_ pairs =>
    match pairs with
    | [(v, e)] =>
      let (args, body) := peelLams e
      let resTy        := resTyOf v args.length
      let rec?         := occursInExpr v.name e
      emitDefHeader mm classNames top v args resTy body rec?
    | _        =>
      let defs := pairs.map fun (v, e) =>
        let (args, body) := peelLams e
        let resTy        := resTyOf v args.length
        emitDefHeader mm classNames top v args resTy body true
      let body := String.intercalate "\n" defs
      s!"mutual\n{body}\nend"

/-- Collect the names of every top-level binder in a program. -/
private def collectTopNames (p : CoreProgram) : List Name :=
  p.foldl (init := []) fun acc b => match b with
    | .nonRec v _ => v.name :: acc
    | .rec_ pairs => pairs.foldl (init := acc) fun acc (v, _) => v.name :: acc

def emitProgram (mm : List (Name × Name)) (classNames : List Name) (p : CoreProgram) : String :=
  let top      := collectTopNames p
  let bindStrs := p.map (emitBind mm classNames top)
  String.intercalate "\n\n" bindStrs

/-- Like `emitProgram`, but extends the "top-level names" set with extra
    names that should NOT get a `_unique` suffix when emitted as Var refs.
    The intended use is to splice in user-declared data constructors so
    `App (Var Foo) ...` becomes `Foo a b`, not `Foo_3490`. -/
def emitProgramWith (mm : List (Name × Name)) (classNames : List Name) (p : CoreProgram) (extraTopNames : List Name) : String :=
  let top      := extraTopNames ++ collectTopNames p
  let bindStrs := p.map (emitBind mm classNames top)
  String.intercalate "\n\n" bindStrs

/-! ## Data type declarations and instances -/

/-- Emit a Haskell `data T = …` declaration as a Lean `inductive`. Bare
    constructor uses are *not* brought into scope via `open T` — that makes
    `T` ambiguous between the type and the ctor in Lean's elaborator. The
    body post-passes rewrite Haskell-style refs to the qualified `T.C` form.
    Field selectors GHC auto-generates are emitted alongside as regular
    defs. -/
def emitDataDecl (derivedEq hasOrd : Bool) (d : DataDecl) : String :=
  let leanName := sanitize d.name
  let ctorLines := d.ctors.map fun c =>
    let argTys := c.fields.map (emitType ·.ty)
    let arrows := argTys.foldr (init := leanName) fun a acc => s!"{a} → {acc}"
    s!"  | {sanitize c.name} : {arrows}"
  let body := String.intercalate "\n" ctorLines
  -- `Inhabited` so emitted `default` bottoms whose result is this type elaborate.
  -- A *derived* Eq/Ord (whose GHC `$c==`/`$ccompare` body uses untranslatable
  -- tag primops) is reconstructed structurally here via Lean `deriving`, which
  -- matches GHC's derived semantics. `Ord` additionally needs `LE`/`LT`/`Min`/
  -- `Max` (Lean's `Ord` doesn't supply them) so the transpiler's lowered
  -- `decide (a ≤ b)` / `Min.min` / … resolve.
  let derivs := "Repr, Inhabited"
    ++ (if derivedEq || hasOrd then ", DecidableEq" else "")
    ++ (if hasOrd then ", Ord" else "")
  let ordInsts :=
    if hasOrd then
      s!"\n\ninstance : LE {leanName} := leOfOrd\ninstance : LT {leanName} := ltOfOrd"
        ++ s!"\ninstance : Min {leanName} := minOfLe\ninstance : Max {leanName} := maxOfLe"
    else ""
  s!"inductive {leanName} where\n{body}\nderiving {derivs}{ordInsts}"

/-- Emit a single-parameter user class as a Lean `class`. -/
def emitClassDecl (c : ClassDecl) : String :=
  let methodLines := c.methods.map fun m =>
    s!"  {sanitize m.name} : {emitType m.ty}"
  s!"class {sanitize c.name} ({tyVarId c.tyVar} : Type) where\n" ++
    String.intercalate "\n" methodLines

private partial def firstValArgTy : GHCType → Option GHCType
  | .forAll _ b => firstValArgTy b
  | .tyFun a _  => some a
  | _           => none

/-- Does the expression reference a constructor-tag primop (`dataToTag#` /
    `tagToEnum#`)? Such a body is a GHC *derived* Eq/Ord we cannot translate —
    those types are routed through Lean `deriving` instead. Hand-written
    instances (e.g. Ratio's cross-multiply `==`) never use these primops, so
    they keep their normal body-translation. -/
private partial def usesTagPrim : Expr → Bool
  | .var v       => v.name.endsWith "dataToTag#" || v.name.endsWith "tagToEnum#"
  | .lit _       => false
  | .app f a     => usesTagPrim f || usesTagPrim a
  | .lam _ b     => usesTagPrim b
  | .let_ bnd b  =>
    (match bnd with
     | .nonRec _ e => usesTagPrim e
     | .rec_ ps    => ps.any (fun p => usesTagPrim p.2))
      || usesTagPrim b
  | .case_ s _ _ alts =>
    usesTagPrim s || alts.any (fun (.mk _ _ r) => usesTagPrim r)
  | .cast e      => usesTagPrim e
  | .tick e      => usesTagPrim e
  | .type_ _     => false

/-- Class-method binder names, by class. Used both to detect derived instances
    and to suppress their (untranslatable) method defs. -/
private def eqMethodNames  : List Name := ["$c==", "$c/="]
private def ordMethodNames : List Name := ["$ccompare", "$c<", "$c<=", "$c>", "$c>=", "$cmax", "$cmin"]

/-- Head-type string of a class-method `Var` (its first value argument's type,
    emitted), matching the strings `emitInstance`/`emitDataDecl` compare against. -/
private def methodHeadStr (v : Var) : Option String :=
  (firstValArgTy v.ty).map emitType

/-- Scan binds for *derived* Eq methods (`$c==`/`$c/=` whose body uses the tag
    primops `dataToTag#`/`tagToEnum#`) and return their head-type strings. Such
    Eq instances can't be body-translated and are routed through Lean
    `deriving DecidableEq` instead. Hand-written Eq (e.g. Ratio's cross-multiply
    `==`) never uses tag primops, so it keeps its body-translation. (Ord is
    handled by instance-existence, not this scan — see `emitFullProgram` — since
    a derived `compare` on a small enum is case-based and indistinguishable from
    a hand-written one.) -/
private def derivedEqTypes (binds : CoreProgram) : List String :=
  let step (acc : List String) (v : Var) (e : Expr) : List String :=
    if usesTagPrim e && eqMethodNames.contains v.name then
      match methodHeadStr v with | some hs => hs :: acc | none => acc
    else acc
  binds.foldl (init := []) fun acc b => match b with
    | .nonRec v e => step acc v e
    | .rec_ pairs => pairs.foldl (init := acc) (fun acc (v, e) => step acc v e)

/-- Names of `$c…` class-method `Var`s referenced anywhere in an expression. -/
private partial def collectCMethodRefs : Expr → List Name
  | .var v       => if v.name.startsWith "$c" then [v.name] else []
  | .app f a     => collectCMethodRefs f ++ collectCMethodRefs a
  | .lam _ b     => collectCMethodRefs b
  | .let_ bnd b  =>
    (match bnd with
     | .nonRec _ e => collectCMethodRefs e
     | .rec_ ps    => ps.flatMap (fun p => collectCMethodRefs p.2))
      ++ collectCMethodRefs b
  | .case_ s _ _ alts => collectCMethodRefs s ++ alts.flatMap (fun (.mk _ _ r) => collectCMethodRefs r)
  | .cast e      => collectCMethodRefs e
  | .tick e      => collectCMethodRefs e
  | _            => []

/-- Look up a top-level binding by name. -/
private def findBind (binds : CoreProgram) (n : Name) : Option (Var × Expr) :=
  binds.findSome? fun b => match b with
    | .nonRec v e => if v.name == n then some (v, e) else none
    | .rec_ pairs => pairs.find? (fun (v, _) => v.name == n)

/-- Replace every `tyCon headName []` occurrence with `tyVar tv` (generalize an
    instance-specialized method type back to the class-parameter form). -/
private partial def generalizeTy (headName tv : Name) : GHCType → GHCType
  | .tyCon n args => if n == headName && args.isEmpty then .tyVar tv
                     else .tyCon n (args.map (generalizeTy headName tv))
  | .tyApp f x    => .tyApp (generalizeTy headName tv f) (generalizeTy headName tv x)
  | .tyFun a r    => .tyFun (generalizeTy headName tv a) (generalizeTy headName tv r)
  | .forAll v b   => .forAll v (generalizeTy headName tv b)
  | t             => t

/-- Reconstruct `ClassDecl`s + a `(method, class)` map from the program's
    instance dict-builders (which reference their `$c<method>` bindings) and the
    `$c<method>` binding types (generalized to the class parameter). No GHC-plugin
    support is needed: the dfun (`$f…`) body names the instance's methods. -/
def reconstructClasses (binds : CoreProgram) (insts : List Instance)
    : List ClassDecl × List (Name × Name) :=
  let tv := "a"
  let perInstance (i : Instance) : Option (ClassDecl × List (Name × Name)) := do
    let (_, dfunRhs) ← findBind binds i.dfunName
    let headName ← match i.headTypes.head? with | some (.tyCon n _) => some n | _ => none
    let cmethods := (collectCMethodRefs dfunRhs).eraseDups
    let methods := cmethods.filterMap fun cm => do
      let (mv, _) ← findBind binds cm
      let mname := cm.drop 2   -- strip "$c"
      some ({ name := mname, ty := generalizeTy headName tv mv.ty } : ClassMethod)
    let pairs := methods.map (fun m => (m.name, i.className))
    some ({ name := i.className, tyVar := tv, methods }, pairs)
  let results := insts.filterMap perInstance
  let classes := results.foldl (init := ([] : List ClassDecl)) fun acc (cd, _) =>
    if acc.any (·.name == cd.name) then acc else acc ++ [cd]
  let methodMap := (results.flatMap (·.2)).eraseDups
  (classes, methodMap)

/-- Find the `$c<method>` binding belonging to the instance whose head type
    matches `headTyStr`, returning its emitted (unique-suffixed) def name.
    Generalizes the former `findEqMethod`: multiple instances of a class each
    produce a `$c<method>` binding that collides after sanitization, so we
    disambiguate by matching the method's first value-argument type against the
    instance head. -/
private def findClassMethod (binds : CoreProgram) (method : Name) (headTyStr : String) : Option String :=
  let matchesHead (v : Var) : Bool :=
    v.name == method &&
      (match firstValArgTy v.ty with
       | some t => emitType t == headTyStr
       | none   => false)
  binds.findSome? fun b => match b with
    | .nonRec v _ => if matchesHead v then some (localId v) else none
    | .rec_ pairs => (pairs.find? (fun (v, _) => matchesHead v)).map (fun (v, _) => localId v)

/-- Emit a user-class instance: for each class method, find the matching
    `$c<method>` binding for this instance's head type and wire it as a field.
    Returns `none` if any method can't be resolved (skip rather than emit broken). -/
def emitInstanceUser (classes : List ClassDecl) (binds : CoreProgram) (i : Instance) : Option String := do
  let cd ← classes.find? (·.name == i.className)
  let tyStr := i.headTypes.map emitType |> String.intercalate " "
  let fields := cd.methods.filterMap fun m =>
    match findClassMethod binds ("$c" ++ m.name) tyStr with
    | some ref => some s!"  {sanitize m.name} := {ref}"
    | none     => none
  if fields.length == cd.methods.length && !fields.isEmpty then
    some (s!"instance : {sanitize i.className} {tyStr} where\n" ++ String.intercalate "\n" fields)
  else none

/-- Emit a Lean `instance` block. `Eq` → Lean `BEq`, `Ord` → Lean `Ord` (the
    latter via `deriving` in the data block), and user classes via
    `emitInstanceUser`. Returns `none` for classes we don't model (Show, Read). -/
def emitInstance (classes : List ClassDecl) (derivedEq : List String) (binds : CoreProgram) (i : Instance) : Option String :=
  let tyStr := i.headTypes.map emitType |> String.intercalate " "
  match i.className with
  | "Eq" =>
    -- A *derived* Eq is handled by the type's `deriving DecidableEq` (its
    -- `$c==` body uses untranslatable tag primops); skip the body-translation.
    -- Hand-written Eq still translates to a `BEq` instance from its body.
    if derivedEq.contains tyStr then none
    else match findClassMethod binds "$c==" tyStr with
    | some methodRef => some s!"instance : BEq {tyStr} where\n  beq := {methodRef}"
    | none           => none
  | "Ord" =>
    -- Ord is reconstructed via `deriving Ord` + `leOfOrd`/… in the data block
    -- (emitted by `emitDataDecl`), so instances precede the binds that use
    -- `≤`/`<`/`min`/`max` (Lean instances are not forward-visible). Nothing to
    -- emit here. The GHC `$ccompare`/`$c<=`/… method defs are suppressed in
    -- `emitFullProgram`.
    none
  -- Show is deliberately not translated: GHC's `$cshowsPrec` body is string
  -- plumbing that rarely matches Lean's `ToString`, and emitted data decls
  -- already `derive Repr`, which Blaster uses to print counterexamples.
  -- Translating Show would risk a *wrong* printer; skipping is sound.
  | "Show" => none
  | _ => emitInstanceUser classes binds i

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
  -- Eq: detect *derived* Eq (tag-primop `$c==`) → route through `deriving
  -- DecidableEq` and suppress the untranslatable method defs; hand-written Eq
  -- keeps body-translation. Ord: any type with an Ord instance is reconstructed
  -- via `deriving Ord` + `leOfOrd`/… in the data block (so the instances precede
  -- the binds that use `≤`/`<`/`min`/`max` — Lean instances aren't forward-
  -- visible); its GHC `$ccompare`/`$c<=`/… method defs are all dead boilerplate
  -- and suppressed.
  let derivedEq : List String := derivedEqTypes p.binds
  let ordTypes  : List String :=
    p.instances.filterMap fun i =>
      if i.className == "Ord" then some (i.headTypes.map emitType |> String.intercalate " ") else none
  let headMatches (v : Var) (s : List String) : Bool :=
    match methodHeadStr v with | some hs => s.contains hs | none => false
  let isSuppressedMethod (v : Var) : Bool :=
    (eqMethodNames.contains v.name  && headMatches v derivedEq)
    || (ordMethodNames.contains v.name && headMatches v ordTypes)
  let keptBinds : CoreProgram := p.binds.filterMap fun b => match b with
    | .nonRec v e => if isSuppressedMethod v then none else some (.nonRec v e)
    | .rec_ pairs =>
      let kept := pairs.filter (fun (v, _) => !isSuppressedMethod v)
      if kept.isEmpty then none else some (.rec_ kept)
  -- Reconstruct user classes → class decls + method→class map (selector rewrite).
  let (userClasses, methodMap) := reconstructClasses p.binds p.instances
  let datas := p.typeDecls.map fun d =>
    let hs := emitType (.tyCon d.name [])
    emitDataDecl (derivedEq.contains hs) (ordTypes.contains hs) d
  let classNames := userClasses.map (·.name)
  let binds := emitProgramWith methodMap classNames keptBinds ctorNames
  let insts := p.instances.filterMap (emitInstance userClasses derivedEq p.binds)
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
