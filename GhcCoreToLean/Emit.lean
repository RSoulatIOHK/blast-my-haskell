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
    | .coercion    => false

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

/-- One `methodMap` entry: a class method's bare name, the class that declares
    it, and the uniques of program BINDERS that shadow that name.

    WHY THE SHADOW LIST. `emitVar` used to match a `Var` reference on the bare
    NAME alone, which is wrong for a locally-bound occurrence of that name. A
    parameter called `size` in a module declaring `class Sized a where size` is
    legal Haskell (GHC only warns, under `-Wname-shadowing`), and the reference to
    the PARAMETER emitted as `Sized.size` — type-correct and silently wrong.
    OBSERVED on `examples/haskell/TwoClassesDistinctMethods.hs` before this
    field existed:

        def applySizer (size_8942 : (Box → Int)) : Int :=
          (Sized.size) ((Box.Box) ((3 : Int)))

    which Lean accepted with only an `unused variable size_8942` warning, and
    whose property `∀ k, applySizer (fun _ => k) = k` blaster falsified with
    `k: 4` (the body is constantly `3`).

    UNIQUES ARE THE DISCRIMINATOR because they identify GHC `Id`s, and a class-op
    selector is never a BINDER in the dump — a class-op Id is not a top-level
    bind (see `reconstructClasses`) and cannot be a local binder. So a binder
    named `size` is necessarily a different Id from the selector `size`, and
    every reference sharing that binder's unique is a reference to the binder. On
    that fixture the selector reference carries `unique 8931` (and, being routed
    through the shim's external-name path, the placeholder type `_Unknown`) while
    the shadowing parameter carries `unique 8942` at both its binder and its
    reference.

    CAVEAT, stated because the comparison is not on the full unique: the shim
    records only the NUMBER part of ghc-dump's `Unique tag n`
    (`binderUniqueAsNat`, shim/Main.hs), so two `Id`s whose numbers agree under
    different tags compare equal here. Both would also have to be spelled with
    the same method name for it to matter, and the failure direction is a
    SUPPRESSED rewrite (a bare `size` that then resolves as a local id) rather
    than a spurious one. Pinned as a risk; not observed. -/
structure MethodRef where
  method     : Name
  cls        : Name
  /-- Uniques of binders named `method` anywhere in the emitted program; see the
      structure docstring. Filled by `attachMethodShadows`, which is why the
      default keeps hand-written test literals short. -/
  shadowedBy : List Unique := []
  /-- Emit matching occurrences as the BARE method name instead of
      `Class.method`. Set on exactly one derived map: the one used to translate a
      class's own DEFAULT-METHOD bodies into its Lean class body (M3 Task 4,
      `classDefaultBody`). Inside a `class C … where m : τ := <body>` the class
      name is not a constant yet, so a qualified sibling reference does not
      elaborate — PROBED, verbatim:

          class Greet2 (a : Type) where
            name2 : a → Int
            greet2 : a → Int := fun x => Greet2.name2 x + 1
          -- error: Invalid field `name2`: The environment does not contain
          --   `Function.name2`

      while the same body with a BARE `name2` elaborates and is picked up by an
      instance that omits the field. Dropping the map entry instead of flagging it
      would be unsound for an OPERATOR method (`==`): `emitVar` would fall through
      to `Maps.valueMap` and emit the builtin, silently ignoring the user's
      method. The flag keeps the match and only changes its spelling.

      CONDITIONAL, and loudly so: the rewrite needs a map ENTRY for the sibling,
      and the map is instance-driven (`reconstructClasses`). A sibling with no
      entry — a class whose default's siblings have no local instance, or whose
      `$c` bind `Main.lean` filtered — falls through to `refId` and emits
      `name_8929`, an unbound identifier inside the class body. MEASURED, pinned in
      `Tests/Unit.lean`. Synthesizing entries from `ClassDecl.methods` would fix
      the spelling and break something worse: `emitVar` is first-match, so
      synthesized entries with an empty `shadowedBy` would rewrite a LOCAL binder
      named like a method into the field — the silent-wrong `shadowedBy` exists to
      prevent. A correct version must attach shadows to them; deferred until a
      fixture needs it. -/
  bare       : Bool := false
deriving Repr, DecidableEq, Inhabited

/-- Map a Var reference. A class-method selector (in `methodMap`) emits
    `Class.method`; otherwise value-map hits short-circuit; top-level refs use
    bare names; locals get unique-suffixed.

    PRECEDENCE (`methodMap` before `valueMap`) is deliberate and load-bearing now
    that M1 registered BARE operator keys (`++`, `==`, `+`, …) next to the
    qualified ones, so the two key sets CAN overlap. This is the safe order:

    * `methodMap` keys are always BARE method names — `reconstructClasses` takes
      them from `$c<method>` binds (`cm.drop 2`) and the decl plugin from
      `occNameString`. A QUALIFIED `valueMap` key (`GHC.Base.++`) therefore
      cannot collide with one at all, which makes the order unobservable for
      every qualified name.
    * A BARE name in the dump belongs to the module being transpiled: the shim
      strips the module prefix only for the current module and leaves
      `GHC.Base.++` qualified (`convertExternalName`, shim/Main.hs). So when a
      bare `++` arrives in a module that declares a class method `++`, the user's
      method IS the referent and must win over the hedged bare `valueMap` key.

    What makes a bare-name match mean "the selector" is `MethodRef.shadowedBy`,
    which excludes locally-bound occurrences of the name; see that docstring.

    SHADOWING GATES `valueMap`, and the two tests are therefore SEQUENCED rather
    than conjoined. A name-match decides that the name belongs to the module (the
    bullet above); `shadowedBy` then decides only WHICH of the module's `Id`s it
    is — the selector or a local binder. Neither answer is ever the builtin, so a
    suppressed match must route to `refId`, not fall through.

    Folding the shadow test into the `find?` predicate — as this did until the
    cross-cell fixture existed — made a suppressed match indistinguishable from
    "no such method", so it fell into `valueMap`. For an ordinary method name that
    is harmless (`valueMap "size"` is `none`, so the fall-through reached `refId`
    anyway), which is why `TwoClassesDistinctMethods.hs` passed. For an OPERATOR
    method name it is not. OBSERVED on `examples/haskell/OperatorShadow.hs`, whose
    `applyEq`'s parameter is named `(==)` in a module declaring `class MyEq a where
    (==)`:

        def applyEq (_eq__eq__9645 : (Int → (Int → Bool))) (p_9646 : Int)
            (q_9647 : Int) : Bool :=
          (((· == ·)) (p_9646)) (q_9647)

    — the builtin, with the parameter unused; Lean accepted it (`BEq Int` is in
    scope) and blaster falsified `∀ p q, applyEq (fun _ _ => false) p q = false`
    with `p: 0, q: 0`.

    The sequencing also makes the `methodMap` lookup FIRST-MATCH-WINS on the name
    where the conjoined form would have kept searching for an unshadowed entry
    with the same name. That is unobservable: two entries sharing a `method`
    require two classes declaring it, which `sameMethodAmbiguities` refuses
    upstream (and GHC rejects outright within one module) — that refusal is the
    proof, not the sweep: no green-regression fixture HAS a duplicated `method`,
    so their byte-identical output measures the reorder's emission-neutrality
    generally and is silent on this shape specifically.

    `refId` (not `localId`) is the suppressed arm for safety, and degenerates to
    `localId` for every reachable case: a method name is bare, so `refId`'s
    qualified arm cannot fire, and its top-level arm cannot either — a top-level
    binder spelled like a method the module declares is a duplicate declaration
    that GHC rejects (see `TwoClassesSameMethod.hs`). -/
def emitVar (methodMap : List MethodRef) (topNames : List Name) (v : Var) : String :=
  match methodMap.find? (fun m => m.method == v.name) with
  | some m    => if m.shadowedBy.contains v.unique then refId topNames v
                 else if m.bare then sanitize v.name
                 else s!"{sanitize m.cls}.{sanitize v.name}"
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
    if name == "(,)" || name == "(,,)" || name == "(,,,)"
       || name == "GHC.Tuple.(,)" || name == "GHC.Tuple.(,,)"
       || name == "GHC.Tuple.(,,,)" then
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
    ⊥ part of their domain (`head`/`last`/`!!`/`fromJust`, and
    `maximum`/`minimum`, which are ⊥ only on `[]`). They are NOT bottoms
    — they do not collapse to `default` everywhere (that would be unsound on the
    defined domain, e.g. `head [1,2,3]`). But because their emitted term mentions
    `default`, a polymorphic def using one needs an `[Inhabited t]` binder, so
    `exprHasBottom` must see through to them. (`tail`→`List.tail` and
    `init`→`List.dropLast` are total with no `default`, so they're not listed.)
    Both members of each hedged name pair are listed: a one-sided registration
    would silently skip the binder for whichever key Core actually delivers. -/
private def isPartialDefaultName : Name → Bool
  | "GHC.List.head" | "GHC.List.last" | "GHC.List.!!"
  | "Data.Maybe.fromJust"
  | "Data.Foldable.maximum" | "GHC.List.maximum"
  | "Data.Foldable.minimum" | "GHC.List.minimum" => true
  | _ => false

private partial def appHeadName : Expr → Option Name
  | .var v   => some v.name
  | .app f _ => appHeadName f
  | .cast e  => appHeadName e
  | .tick e  => appHeadName e
  | _        => none

/-- Does any subexpression emit a `default`? True for an applied bottom
    (`error`/`undefined`) or an applied partial whose faithful image uses
    `default` (`head`/`last`/`!!`/`fromJust`/`maximum`/`minimum`). Used to
    decide whether a def's polymorphic result needs an `[Inhabited t]` binder so
    the emitted `default` elaborates. -/
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
  partial def emitExpr (mm : List MethodRef) (top : List Name) : Expr → String
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
    -- LOUD residue. `Lower` erases coercion arguments, and a coercion cannot
    -- occur in head position, so reaching here means an unhandled shape (e.g. a
    -- coercion *binder*, see the M2 Task 2 notes in Tests/Unit.lean). Like
    -- `GHCCore.typeArg`, this identifier is deliberately not defined anywhere:
    -- the generated file must fail to elaborate rather than pick some value.
    | .coercion => "GHCCore.coercionResidue"

  partial def emitAlt (mm : List MethodRef) (top : List Name) : Alt → String
    | .mk con bndrs rhs =>
      s!"| {emitAltPattern con bndrs} => {emitExpr mm top rhs}"

  /-- Emit a single `let rec` binding: peel lambdas into parameters and emit
      `let rec {id} {params} := {body}`. (Lean's `let rec` has no `decreasing_by`,
      so only structurally-decreasing recursion elaborates; non-structural local
      rec is a documented follow-up.) -/
  partial def emitLetRecBinding (mm : List MethodRef) (top : List Name) (v : Var) (e : Expr) : String :=
    let (params, body) := peelLamsLocal e
    let paramStr := String.intercalate " " (params.map (fun p => s!"({localId p})"))
    let head := if paramStr.isEmpty then s!"let rec {localId v} :="
                else s!"let rec {localId v} {paramStr} :="
    s!"{head} {emitExpr mm top body}"

  partial def emitLet (mm : List MethodRef) (top : List Name) : Bind → String
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

private def dedup (xs : List Name) : List Name :=
  xs.foldl (init := []) fun acc x => if acc.contains x then acc else acc ++ [x]

/-- Peel leading class-constraint arrows off a def signature, returning the
    instance-implicit binder strings and the remaining (constraint-stripped)
    type. `∀`-binders are skipped (their tyvars are handled by `collectTyVars`).
    The term-level dict binder is already erased by `Lower`, so stripping the
    dict arrow from the *type* realigns the value args / result with the term
    binders. Stops at the first non-constraint arrow.

    A constraint is recognised in two ways, user classes FIRST:
    * `C ∈ classNames` — a class the transpiler emits itself → `[C t]`.
    * `Maps.classConMap C` — a BUILTIN class with a Lean image → that map's
      binder templates, `{t}` filled in (`Eq a =>` ⇒ `[BEq t]`).
    Anything else is not a constraint as far as this function is concerned and
    stops the peel, which is what keeps an unmapped builtin (`Fractional a =>`)
    LOUD: the arrow stays, the first value binder gets the dictionary's type, and
    the generated file does not elaborate.

    Only a constraint whose argument is a bare type VARIABLE is peeled. A head
    like `Eq [a]` / `Eq Int` does not match the pattern and stays loud —
    unchanged from before this map existed, and not reachable from the fixtures
    (GHC passes no dictionary for a monomorphic signature).

    CONVERSE HAZARD — a tripwire, not a live bug. Recognition is by NAME in
    leading-argument position, with no check that the head is a CLASS at all. So a
    one-parameter user TYPE that happens to be named `Eq`/`Ord`/`Num` — e.g.
    `data Eq a = …` used as `f :: Eq a -> Bool` — would be peeled as a constraint
    and its real value argument deleted from the header. Unreachable today:
    parameterized user data types are unsupported (`DataDecl` carries no `tyVars`
    field, the decl plugin dumps no type parameters, and such a module already
    fails loudly at `lake build` — see the README limitation), so no program in
    which this could matter compiles in the first place. Named here so that
    whenever parameterized data types land, the peel is given a real "is this head
    a class?" test (plugin-sourced class names) instead of a name match — the
    failure mode would be a silently dropped argument, not a loud one.

    Both defects of M3 fact 3 live in the two callers of this function
    (`emitDefHeader`'s binder list and `emitBind`'s `resTyOf`), so the widening
    goes HERE rather than in a gate threaded to each: the callers cannot drift
    apart. Kept non-`private` so `Tests/Unit.lean` can guard it directly. -/
partial def stripClassConstraintsGo (classNames : List Name) : GHCType → List String × GHCType
  | .forAll _ b => stripClassConstraintsGo classNames b
  | .tyFun (.tyCon c [.tyVar t]) r =>
    let binders : Option (List String) :=
      if classNames.contains c then some [s!"[{sanitize c} {tyVarId t}]"]
      else (Maps.classConMap c).map (·.map (·.replace "{t}" (tyVarId t)))
    match binders with
    | some bs =>
      let (cs, rest) := stripClassConstraintsGo classNames r
      (bs ++ cs, rest)
    | none => ([], .tyFun (.tyCon c [.tyVar t]) r)
  | t => ([], t)

/-- `stripClassConstraintsGo` with the binder list deduplicated. An explicit
    `(Eq a, Ord a) => …` peels two constraints whose Lean images overlap (`Ord`'s
    set contains `[BEq t]`), and repeating an instance-implicit binder, while
    legal, is noise. First-occurrence order is preserved, so `LT` still precedes
    `DecidableLT`. Binders for DIFFERENT type variables are different strings and
    are never merged. -/
def stripClassConstraints (classNames : List Name) (t : GHCType) : List String × GHCType :=
  let (cs, rest) := stripClassConstraintsGo classNames t
  (dedup cs, rest)

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

/-- GHC class-method bindings are named `$c<op>` (e.g. `$c==`). With more than
    one instance of a class these collide after sanitization, so we suffix them
    with their unique (like a local). -/
private def isClassMethodName (n : Name) : Bool := n.startsWith "$c"

private def defNameId (v : Var) : String :=
  if isClassMethodName v.name then localId v else sanitize v.name

private def emitDefHeader (mm : List MethodRef) (classNames : List Name) (top : List Name)
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

def emitBind (mm : List MethodRef) (classNames : List Name) (top : List Name) (b : Bind) : String :=
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

def emitProgram (mm : List MethodRef) (classNames : List Name) (p : CoreProgram) : String :=
  let top      := collectTopNames p
  let bindStrs := p.map (emitBind mm classNames top)
  String.intercalate "\n\n" bindStrs

/-- Like `emitProgram`, but extends the "top-level names" set with extra
    names that should NOT get a `_unique` suffix when emitted as Var refs.
    The intended use is to splice in user-declared data constructors so
    `App (Var Foo) ...` becomes `Foo a b`, not `Foo_3490`. -/
def emitProgramWith (mm : List MethodRef) (classNames : List Name) (p : CoreProgram) (extraTopNames : List Name) : String :=
  let top      := extraTopNames ++ collectTopNames p
  let bindStrs := p.map (emitBind mm classNames top)
  String.intercalate "\n\n" bindStrs

/-- Keep the binds satisfying `keep`, PER PAIR: a `Rec` group is filtered
    member-wise and survives with whatever is left (dropped only when nothing is).
    Mirrors `Main.keepBinding`, which does the same for its own drop rules.

    Every bind classification in `emitFullProgram` goes through this, because
    reading a Rec group's HEAD binder and classifying the whole group by it is
    wrong in both directions. GHC puts an instance's dict-builder and its method
    binds in ONE Rec group whenever a method body needs the instance's own
    dictionary — OBSERVED on `DefaultMethods.hs` as
    `Rec group: ['$fGreetQuiet', '$cgreet']` (see the M3 Task 4 block in
    `GhcCoreToLean/Tests/Unit.lean`) — and the group's member order is GHC's, not
    ours:
    * head `$f…` (observed): the whole group classified as junk, so the `$c`
      method bind was DROPPED while the instance still referenced it —
      `error: Unknown identifier `_dollar_cgreet_9231``.
    * head `$c…` (not observed, and nothing forbids it): the whole group would
      classify as a method def, EMITTING the `$f` dict-builder — a body applying
      the dictionary constructor `C:Greet`, which has no Lean image.
    Per-pair filtering makes the outcome independent of that order. -/
def filterBinds (keep : Var → Expr → Bool) (binds : CoreProgram) : CoreProgram :=
  binds.filterMap fun b => match b with
    | .nonRec v e => if keep v e then some (.nonRec v e) else none
    | .rec_ pairs =>
      let kept := pairs.filter (fun (v, e) => keep v e)
      if kept.isEmpty then none else some (.rec_ kept)

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

/-- Emit a user class as a Lean `class`, one `(v : Type)` binder per type
    parameter. Single-parameter classes — the only ones supported end-to-end —
    are unchanged from v1 (`class Sized (a : Type) where …`).

    `c.supers` is deliberately NOT emitted yet: superclass emission (`extends`
    for a user parent, an instance-implicit field for a builtin one) is M3
    Task 5. Dropping it here is loud, not silent: the parent class's methods are
    still rewritten to `Parent.method` at their call sites, so a function with
    only the child constraint in scope fails to synthesize the parent instance.
    Observed on `SuperClass.hs` — see the `M3 Task 1` block in
    `GhcCoreToLean/Tests/Unit.lean`.

    `defaults` maps a METHOD NAME to the Lean term for its class-body `:=`
    default, translated from GHC's `$dm<method>` bind by `classDefaultBody` (M3
    Task 4). A method absent from the list emits without a default, exactly as
    before. Two ordering facts about Lean class bodies, both PROBED:

    * A default may reference only methods declared EARLIER in the same class
      body. `class Fwd (a : Type) where g : a → Int := fun x => f x + 1;
      f : a → Int` gives `error: Unknown identifier `f``. Method order here is
      GHC's `classOpItems` order, which is DECLARATION order (M3 Task 1's
      observation 1), so a Haskell class that declares a defaulted method before
      the method its default calls fails LOUD. The methods are deliberately NOT
      reordered to dodge it: no fixture has that shape, so the reorder would be
      unexercised code, and forward-reference-in-a-default is a shape whose only
      other possible arrangement (mutually-referential defaults) cannot be
      ordered at all.
    * A default that calls a method of ANOTHER class emits that call QUALIFIED
      (`Sized.size`), and class decls are emitted UNSORTED (see `mergeClassDecls`
      — sorting is M3 Task 5's job), so it is a forward reference whenever the
      other class comes later: loud, not silent. -/
def emitClassDecl (defaults : List (Name × String)) (c : ClassDecl) : String :=
  let methodLines := c.methods.map fun m =>
    let decl := s!"  {sanitize m.name} : {emitType m.ty}"
    match defaults.find? (·.1 == m.name) with
    | some (_, body) => s!"{decl} := {body}"
    | none           => decl
  let params := String.intercalate " " (c.tyVars.map fun tv => s!"({tyVarId tv} : Type)")
  s!"class {sanitize c.name} {params} where\n" ++
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
  | .coercion    => false

/-- Class-method binder names, by class. Used both to detect derived instances
    and to suppress their (untranslatable) method defs. -/
private def eqMethodNames  : List Name := ["$c==", "$c/="]
private def ordMethodNames : List Name := ["$ccompare", "$c<", "$c<=", "$c>", "$c>=", "$cmax", "$cmin"]

/-- Head-type string of a class-method `Var` (its first value argument's type,
    emitted), matching the strings `emitInstance`/`emitDataDecl` compare against. -/
private def methodHeadStr (v : Var) : Option String :=
  (firstValArgTy v.ty).map emitType

/-- Instance-head strings of the program's `Eq` instances, in the SAME spelling
    `emitInstance`/`emitDataDecl`/`methodHeadStr` use (pre-resolution, so a user
    type is still its `(GHCCore.tyConOpaque "T")` form). Shared by `isEqNeqBind`
    so the two sides of that comparison cannot drift apart. -/
def eqInstanceHeads (insts : List Instance) : List String :=
  insts.filterMap fun i =>
    if i.className == "Eq" then some (i.headTypes.map emitType |> String.intercalate " ")
    else none

/-- Is `v` the `/=` method bind of an `Eq` instance — i.e. the one GHC derives as
    `not ∘ (==)`, which `Main.lean` drops? Lean's `BEq`/`DecidableEq` supplies
    `bne` itself, and the dropped body would not even elaborate: it references the
    Eq DICT (observed in `/tmp/transpile-Ratio.json`, `$c/= = \eta eta -> case ==
    @CustomRatioSOP $fEqCustomRatioSOP eta eta of …`), and `$c…` defs are emitted
    BEFORE the instances they would need, which Lean does not see forward.

    The point of this predicate is the SCOPE of that drop. `Main.lean` used to
    drop every bind named `$c/=`, so a user class declaring `/=` (legal with
    `import Prelude hiding ((/=))`) lost its method — and then
    `emitInstanceUser`'s all-or-nothing test dropped the whole instance. Matching
    the `Eq` instance heads keeps that class's `$c/=` and still drops Eq's.

    RESIDUAL, un-fixtured: if a user class declaring `/=` has an instance at a
    type that ALSO has an `Eq` instance, both `$c/=` binds carry that head type
    (GHC gives them the same name and distinguishes them only by unique —
    `/tmp/transpile-Ratio.json` has two `$c/=`, uniques 12069 and 12087), so both
    are dropped and the user class's instance vanishes, loud at its use site. The
    precise fix is per-instance attribution through the dfun body's method refs
    (`collectCMethodRefs` carries the uniques); it is not done here because no
    fixture reaches it. -/
def isEqNeqBind (insts : List Instance) (v : Var) : Bool :=
  v.name == "$c/=" &&
    (match methodHeadStr v with
     | some hs => (eqInstanceHeads insts).contains hs
     | none    => false)

/-- The `$c` method binds of a `Show` instance, which `Main.lean` drops: their
    bodies are `showsPrec`/`showString`/`showParen` plumbing over GHC.Show
    internals with no Lean image, and `Show` itself is deliberately not
    translated (see `emitInstance`).

    The point of this predicate, like `isEqNeqBind`'s, is the SCOPE of the drop.
    `Main.lean` matched the PREFIX `$cshow`, which also ate the method of a user
    class declaring anything spelled `show…` — `showIt` (`$cshowIt`), `showAll`,
    `shows`. Those now survive; if such a method is genuinely untranslatable the
    failure is loud downstream rather than a silently missing instance field.
    `Show`'s own three class methods are exactly `showsPrec`, `show` and
    `showList`, so the exact-name list is complete for the derived case.

    RESIDUAL, un-fixtured (same shape as `isEqNeqBind`'s): a user class declaring
    a method literally named `show`/`showsPrec`/`showList` (legal under
    `import Prelude hiding (show)`) still loses that bind, because this test is
    keyed on the name alone — unlike `isEqNeqBind`, which can compare against the
    `Eq` instance HEADS, there is no `Show`-instance head list here (Show
    instances are dropped before they reach the emitter). It is no longer silent
    at the transpiler, though: the instance's method resolves to nothing, which is
    now reported by `unresolvedInstanceMethods`. -/
def isDerivedShowMethod (n : Name) : Bool :=
  n == "$cshow" || n == "$cshowsPrec" || n == "$cshowList"

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

/-- Every BINDER inside an expression, as `(name, unique)`: lambda binders, both
    `let` forms, the case binder, and pattern binders. The match is TOTAL (no
    catch-all) so that adding an `Expr` constructor cannot silently drop a binder
    kind: a missed kind would leave a shadowing occurrence looking like a class-op
    selector, which is exactly the silent-wrong `MethodRef.shadowedBy` closes. -/
private partial def exprBinders : Expr → List (Name × Unique)
  | .var _       => []
  | .lit _       => []
  | .app f a     => exprBinders f ++ exprBinders a
  | .lam v b     => (v.name, v.unique) :: exprBinders b
  | .let_ bnd b  =>
    (match bnd with
     | .nonRec v e => (v.name, v.unique) :: exprBinders e
     | .rec_ ps    => ps.flatMap (fun (v, e) => (v.name, v.unique) :: exprBinders e))
      ++ exprBinders b
  | .case_ s cb _ alts =>
    exprBinders s ++ [(cb.name, cb.unique)]
      ++ alts.flatMap (fun (.mk _ bs r) => bs.map (fun b => (b.name, b.unique)) ++ exprBinders r)
  | .cast e      => exprBinders e
  | .tick e      => exprBinders e
  | .type_ _     => []
  | .coercion    => []

/-- Every binder of a program: the top-level binders and every binder in their
    bodies. Top-level binders are included for completeness only — a top-level
    name cannot collide with a class method's (both are module-level names, so
    GHC rejects the module; see `examples/haskell/TwoClassesSameMethod.hs`). -/
private def programBinders (binds : CoreProgram) : List (Name × Unique) :=
  binds.flatMap fun b => match b with
    | .nonRec v e => (v.name, v.unique) :: exprBinders e
    | .rec_ pairs => pairs.flatMap (fun (v, e) => (v.name, v.unique) :: exprBinders e)

/-- Fill in `MethodRef.shadowedBy` from the binders of the program that is about
    to be emitted: for each method name, the uniques of every binder spelled the
    same. `emitVar` then rewrites only the occurrences that are NOT one of those
    binders' references. Pass the SAME binds that get emitted — a superset would
    only add uniques that no emitted reference mentions, but a subset would leave
    a shadowing occurrence unprotected. -/
def attachMethodShadows (binds : CoreProgram) (mm : List MethodRef) : List MethodRef :=
  let bs := programBinders binds
  mm.map fun m =>
    { m with shadowedBy :=
        (bs.filterMap (fun (n, u) => if n == m.method then some u else none)).eraseDups }

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

/-- Built-in classes handled elsewhere (Eq→BEq, Ord→deriving, Show skipped) or
    with no Lean image — never reconstructed as user classes. -/
private def builtinClasses : List Name :=
  ["Eq", "Ord", "Show", "Read", "Num", "Integral", "Real", "Fractional",
   "Floating", "Enum", "Bounded", "Functor", "Applicative", "Monad",
   "Foldable", "Traversable", "Semigroup", "Monoid"]

/-- Reconstruct `ClassDecl`s + the `MethodRef` map from the program's
    instance dict-builders (which reference their `$c<method>` bindings) and the
    `$c<method>` binding types (generalized to the class parameter). No GHC-plugin
    support is needed: the dfun (`$f…`) body names the instance's methods.

    This is the FALLBACK shape source since M3 Task 1 — the decl-plugin's
    `classDecls` channel is ground truth (see `mergeClassDecls`). What it is still
    the only source of is the method→class map, which is instance-driven by
    construction and drives the call-site `size` → `Sized.size` rewrite; and it is
    the whole story for a run with no decls sidecar (`ghc-core-shim` invoked
    without `--decls`), where `Program.classDecls` is empty.

    The `MethodRef`s come out with an EMPTY `shadowedBy` — this function sees the
    class shapes, not the bodies that will be emitted. `emitFullProgram` fills it
    via `attachMethodShadows`; a caller that skips that step gets the old
    name-only matching, which is the silent-wrong documented on `MethodRef`.

    Its structural limits are why the plugin channel exists: `tyVars` is always
    the single invented `"a"`, `supers` is always empty (a `$p` superclass
    selector is not a top-level bind, so nothing here can see one), and
    `hasDefault` is always `false` (a `$dm` bind is indistinguishable from an
    ordinary one). A class with no local instance produces nothing at all. -/
def reconstructClasses (binds : CoreProgram) (insts : List Instance)
    : List ClassDecl × List MethodRef :=
  let tv := "a"
  let perInstance (i : Instance) : Option (ClassDecl × List MethodRef) := do
    if builtinClasses.contains i.className then none else
    let (_, dfunRhs) ← findBind binds i.dfunName
    let headName ← match i.headTypes.head? with | some (.tyCon n _) => some n | _ => none
    let cmethods := (collectCMethodRefs dfunRhs).eraseDups
    let methods := cmethods.filterMap fun cm => do
      let (mv, _) ← findBind binds cm
      let mname := cm.drop 2   -- strip "$c"
      some ({ name := mname, ty := generalizeTy headName tv mv.ty } : ClassMethod)
    let refs := methods.map (fun m => ({ method := m.name, cls := i.className } : MethodRef))
    some ({ name := i.className, tyVars := [tv], supers := [], methods }, refs)
  let results := insts.filterMap perInstance
  let classes := results.foldl (init := ([] : List ClassDecl)) fun acc (cd, _) =>
    if acc.any (·.name == cd.name) then acc else acc ++ [cd]
  let methodMap := (results.flatMap (·.2)).eraseDups
  (classes, methodMap)

/-- Merge the two class-shape sources. The decl-plugin's `classDecls` (read out
    of GHC's own `Class` records) WIN by name over `reconstructClasses`' output,
    which is inferred from instance bodies and structurally cannot represent type
    parameters beyond one, superclasses, or defaults.

    Precedence is whole-record, not field-wise: the plugin's method list carries
    real method types (`ppMethodTy` renders type variables, which the data-field
    renderer cannot) in DECLARATION order, whereas the reconstruction's order is
    the dfun body's and its types come from head-abstracting an instance's
    specialized `$c` bind — the documented "primary correctness risk". On every
    fixture we have, both sources describe the same single-parameter class and
    agree exactly, which is the byte-identical-`UserClass.lean` regression this
    task gates on. Agreement is NOT guaranteed, though, and the one field where
    disagreeing has a behavioral consequence is `methods`.

    THE METHODS-DISAGREE PATH. After this merge `cd.methods` is the DECLARED
    method set (GHC's own `classOpItems`), which can strictly EXCEED the set
    `emitInstanceUser` can resolve to a `$c<method>` bind. Its all-or-nothing
    test (`fields.length == cd.methods.length`) then drops the WHOLE instance —
    silently as far as this program is concerned (`rc=0`, empty stderr); the
    loudness is Lean's `failed to synthesize` at the use site, the same posture
    as the other unsupported-class paths here, not a new guarantee.

    It is REACHABLE, not hypothetical. `Main.lean`'s `shouldDrop` removes binds
    before Emit ever sees them (`keepBinding` filters `prog.binds`), and two of
    its rules are not class-aware: `$c/=` is dropped UNCONDITIONALLY, so a user
    class that declares `/=` loses it and not merely `Eq`; and the `$cshow` test
    is a PREFIX, so a user method named `showIt` (`$cshowIt`) is eaten too.
    Neither has a fixture.

    Net loudness is nonetheless BETTER than before this channel existed — argued
    by construction, not measured. Pre-change `classDecls` was always empty, so
    `mergeClassDecls [] xs = xs` and `cd.methods` was BY CONSTRUCTION the
    resolvable set: `reconstructClasses` builds it by `findBind`-ing the very
    binds `shouldDrop` already filtered, so a dropped method was absent from the
    class AND from the instance. Output compiled, and the emitted class quietly
    misdescribed the Haskell one. Now the class carries the true method list and
    the instance vanishes instead, so any USE of it fails at Lean:
    wrong-and-quiet became incomplete-and-checkable.

    OWNERSHIP of the remaining sharp edges: M3 Task 2 makes the `$c/=` drop
    class-aware; M3 Task 4 replaces `emitInstanceUser`'s silent whole-instance
    skip with a per-method decision plus an `eprintln`, which is what removes the
    "silent at the transpiler" half above.

    ORDER is deliberately taken from the reconstruction, with plugin-only classes
    (those with no local instance, which the reconstruction never sees) appended.
    Emission puts class decls in the data block unsorted and Lean has no forward
    references, so class order is load-bearing once `extends` appears — sorting by
    superclass dependency is M3 Task 5's job, and reordering here before that
    exists would only churn output.

    `builtinClasses` are filtered defensively. The plugin dumps only the module's
    OWN class TyCons, so `Eq`/`Ord`/… cannot arrive through it unless a user
    declares a class of that name — which has no Lean image here (those names are
    routed to `BEq`/`deriving`) and must not be emitted as a user class. -/
def mergeClassDecls (fromPlugin : List ClassDecl) (fromCore : List ClassDecl)
    : List ClassDecl :=
  let plugin := fromPlugin.filter (fun c => !builtinClasses.contains c.name)
  let merged := fromCore.map fun cd =>
    match plugin.find? (·.name == cd.name) with
    | some p => p
    | none   => cd
  merged ++ plugin.filter (fun p => !fromCore.any (·.name == p.name))

/-! ### Same-named methods across classes

    `methodMap` is keyed by the BARE method name, so two classes declaring `size`
    would produce two entries and `emitVar`'s `find?` would take whichever the
    instance dump listed first — every call site in the module getting the same
    qualifier, with no diagnostic. `sameMethodAmbiguities` refuses that program
    instead (wired in `Main.lean`, before emission).

    WHAT IS ACTUALLY REACHABLE HERE, measured rather than assumed. Two classes of
    ONE module cannot share a method name at all: class methods are module-level
    names, so the second declaration is a duplicate and GHC rejects the module —
    `examples/haskell/TwoClassesSameMethod.hs` is that negative fixture, and it
    fails at `cabal build`, never reaching this code. The collision needs the two
    classes in DIFFERENT modules with this module instantiating both: then
    `reconstructClasses` rebuilds the imported class from its local instance's
    `$c` binds under its bare method name, next to the local class's entry.

    That path has no fixture because cross-module user classes are not supported
    end-to-end — an imported class's method reference arrives module-qualified
    (`A.size`, since the shim only strips the CURRENT module's prefix), misses the
    bare `methodMap` key entirely, and fails loud at `lake build`. So this guard
    is an unexercised tripwire whose only exercise is the `#guard`s in
    `GhcCoreToLean/Tests/Unit.lean`. It is not the removal of a live silent-wrong;
    the live one in this lookup was local-binder shadowing (see `MethodRef`). -/

/-- Method names declared by MORE THAN ONE class of the program's merged class
    set, each with its declaring classes in first-seen order.

    Computed on the MERGED set (plugin `classDecls` ∪ `reconstructClasses`), which
    is deliberately WIDER than the `methodMap` the rewrite uses (reconstruction
    only): the plugin channel also knows the methods of a class with no local
    instance, so an ambiguity is refused even when only one of the two classes has
    an entry in the map. Wider is the safe direction — the guard covers every
    ambiguity the map could have, and a class that is neither declared nor
    instantiated locally is not in either source, so no third module's classes can
    make this fire. -/
def sameMethodAmbiguities (p : Program) : List (Name × List Name) :=
  let classes := mergeClassDecls p.classDecls (reconstructClasses p.binds p.instances).1
  let pairs := classes.flatMap fun c => c.methods.map fun m => (m.name, c.name)
  ((pairs.map (·.1)).eraseDups).filterMap fun mname =>
    let cs := (pairs.filterMap (fun (m, c) => if m == mname then some c else none)).eraseDups
    if cs.length > 1 then some (mname, cs) else none

/-- The refusal message for one `sameMethodAmbiguities` entry. Names every
    declaring class, because which one the emitter would have picked is an
    artifact of dump order and the reader must not be invited to guess it. -/
def sameMethodAmbiguityError (mname : Name) (classes : List Name) : String :=
  s!"ambiguous class method `{mname}`: declared by {String.intercalate ", " (classes.map (s!"`{·}`"))}.\n" ++
  s!"  Call sites in Core reference a class method by its bare name, so the\n" ++
  s!"  transpiler cannot tell which class's `{mname}` a reference means and would\n" ++
  s!"  qualify EVERY one of them with whichever class the instance dump listed\n" ++
  s!"  first. That typechecks and is silently wrong (calls dispatch to the other\n" ++
  s!"  class's method), so transpilation is refused.\n" ++
  s!"  Remedy: rename one of the methods."

/-- Class methods that `emitVar` would resolve to a BUILTIN rather than to the
    user's method, as `(class, method)`: the method's bare name has a `valueMap`
    image — M1 registered bare operator keys (`/=`, `++`, `==`, …) beside the
    qualified ones — and the method→class map has NO entry for it, so a call site
    falls past `methodMap` into `valueMap`.

    This is the other half of `emitVar`'s precedence story. The order there
    (`methodMap` first) is correct whenever the map HAS the entry; what it cannot
    fix is a declared method MISSING from the map, because then nothing marks the
    name as the user's. Both sources of the merged class set know the method
    exists, so the situation is detectable here even though `emitVar` cannot see
    it.

    OBSERVED, and the reason this is a refusal rather than a note: a class
    declaring `(/=)` whose instance head also has an `Eq` instance loses its `$c/=`
    bind (`isEqNeqBind` matches on the head type, and GHC gives both binds that
    same head), so the map has no entry and

        def differs (a_9642 : Box) (b_9643 : Box) : Bool :=
          (((fun a b => !(a == b))) (a_9642)) (b_9643)

    was emitted — the BUILTIN inequality in place of the user's method, which
    typechecks because `deriving Eq` supplied `BEq Box`. Silently wrong for any
    class whose operator means something other than the builtin.

    USE-LEVEL, not declaration-level, and that conjunct is MEASURED. With no
    reference to the name there is no call site to emit wrongly, and refusing
    anyway would take away a module that used to transpile fine: a probe declaring
    `class Neq a where (/=)` with no instance and no use built CLEAN before this
    guard existed, whereas the same probe plus `allDiffer x y = x /= y` (still no
    instance) transpiled and then failed `lake build` with `failed to synthesize`
    — the builtin `!(a == b)` applied at a type variable with no `BEq` binder. So
    the referenced case was already broken and is merely refused EARLIER now,
    while the unreferenced case keeps working. This is the only guard here that
    refuses a program GHC accepts, which is why its edge is drawn tightly.

    The reference test is `occursInExpr`, i.e. any `Var` spelled with the method's
    name. A locally-bound occurrence of that name counts too (`shadowedBy` cannot
    help — there is no map entry to attach it to), so a module whose only `/=` is
    some local binder is refused as well: conservative in the safe direction, and
    unobserved. The names checked are only those with a `valueMap` image, so
    ordinary method names (`size`, `empty`, `insert`) cannot trip it. -/
def unmappedOperatorMethods (p : Program) : List (Name × Name) :=
  let (coreClasses, mapped) := reconstructClasses p.binds p.instances
  let classes := mergeClassDecls p.classDecls coreClasses
  classes.flatMap fun c =>
    c.methods.filterMap fun m =>
      if (valueMap m.name).isSome && !mapped.any (fun r => r.method == m.name)
         && p.binds.any (occursInBind m.name ·) then
        some (c.name, m.name)
      else none

/-- The refusal message for one `unmappedOperatorMethods` entry. -/
def unmappedOperatorMethodError (cls mname : Name) : String :=
  s!"class `{cls}` declares the method `{mname}`, which the transpiler cannot\n" ++
  s!"  distinguish from the builtin `{mname}`: no `$c{mname}` binding for it survives in\n" ++
  s!"  this module (either the class has no local instance here, or the binding was\n" ++
  s!"  filtered as an `Eq` method — see Main.lean's drop rules), so the method→class\n" ++
  s!"  map has no entry and every call site would emit the BUILTIN `{mname}` instead.\n" ++
  s!"  That typechecks whenever the builtin's own instances are in scope and is\n" ++
  s!"  silently wrong (the user's method body is never called), so transpilation is\n" ++
  s!"  refused.\n" ++
  s!"  Remedy: rename the method to a name with no builtin meaning, or drop the\n" ++
  s!"  conflicting `Eq`/`Ord` instance on the same type."

/-- Find the `$c<method>` binding belonging to the instance whose head type
    matches `headTyStr`, returning the whole bind. Multiple instances of a class
    each produce a `$c<method>` binding that collides after sanitization, so we
    disambiguate by matching the method's first value-argument type against the
    instance head. The RHS comes back too, because whether the bind is a
    default-method wrapper is a property of its body (`isDefaultWrapperBody`). -/
private def findClassMethodBind (binds : CoreProgram) (method : Name) (headTyStr : String)
    : Option (Var × Expr) :=
  let matchesHead (v : Var) : Bool :=
    v.name == method &&
      (match firstValArgTy v.ty with
       | some t => emitType t == headTyStr
       | none   => false)
  binds.findSome? fun b => match b with
    | .nonRec v e => if matchesHead v then some (v, e) else none
    | .rec_ pairs => pairs.find? (fun (v, _) => matchesHead v)

/-- The emitted (unique-suffixed) def name of that binding. -/
private def findClassMethod (binds : CoreProgram) (method : Name) (headTyStr : String) : Option String :=
  (findClassMethodBind binds method headTyStr).map (fun (v, _) => localId v)

/-! ### Default methods

    A Haskell class default (`class Greet a where name :: a -> Int;
    greet :: a -> Int; greet x = name x + 1`) reaches the transpiler as TWO
    things, both OBSERVED on `examples/haskell/DefaultMethods.hs` (spines quoted
    in the M3 Task 4 block of `GhcCoreToLean/Tests/Unit.lean`):

    * the class-shape channel's `hasDefault: true` for the method, and a
      top-level `$dm<method>` bind holding the default BODY, abstracted over the
      class parameter and its dictionary;
    * for each instance that RELIES on the default, a `$c<method>` bind that is
      nothing but a wrapper applying `$dm<method>` to that instance's type and
      dictionary — both of which `Lower` erases, leaving the bare reference.

    The Lean image is a class-body `:=` default plus an instance that OMITS the
    field. Emitting the `$dm` bind as an ordinary top-level def instead (what
    happened before this task) cannot work: it carries a `[Greet t]` binder, so
    the wrapper `$c<method>` that an instance's field would point at needs the
    very instance being defined — `failed to synthesize`, or a definitional cycle.

    ONE KEY drives all of it: `translatedDefaults`. A (class, method) pair in that
    list gets a class-body default, its `$dm` bind is suppressed from the emitted
    binds, and its wrapper `$c` binds are suppressed and their instance fields
    omitted. A pair NOT in the list keeps every pre-existing behaviour, so the
    no-plugin path (`classDecls` empty ⇒ `hasDefault` always false) degrades
    exactly as it did before, loudly. -/

/-- Is this `$c<method>` body just GHC's default-method wrapper? OBSERVED shape,
    post-`Lower`, verbatim from `DefaultMethods.hs`'s relying instance:

        ###   $cgreet#9231 [role=id]
        ###     type: (Quiet -> Int)
          App
            App
              Var $dmgreet#9094 [role=dict] : _Unknown
              Type Quiet
            Var $fGreetQuiet#9136 [role=dict] : _Unknown

    The `Type` argument and the dictionary argument are both erased by `Lower`,
    so what Emit sees is exactly `Var $dmgreet` — hence the single-`.var` test.
    Deliberately TIGHT: a wider test ("the body mentions `$dm<method>`") would
    tolerate an eta-expanded wrapper we have never seen, at the price of reading
    any mention as "the default applies", which is the silent-wrong direction. Any
    other shape falls through to being wired as an ordinary instance field, whose
    reference to the suppressed `$dm` def is a loud unknown identifier. -/
def isDefaultWrapperBody (method : Name) : Expr → Bool
  | .var v => v.name == "$dm" ++ method
  | _      => false

/-- THE key (see the section header): the (class, method) pairs this program
    turns into Lean class-body `:=` defaults. Both halves must hold — the class
    shape says the method has a default, AND the `$dm<method>` bind carrying the
    body is present in the program. Consumed by `classDefaultBody` (what to
    emit), `classifyInstanceMethod` (which instance fields to omit) and
    `emitFullProgram` (which binds to suppress), so those three cannot disagree
    about which defaults exist. -/
def translatedDefaults (binds : CoreProgram) (classes : List ClassDecl) : List (Name × Name) :=
  classes.flatMap fun c =>
    c.methods.filterMap fun m =>
      if m.hasDefault && (findBind binds ("$dm" ++ m.name)).isSome
      then some (c.name, m.name) else none

/-- The Lean term for one class-body default: the `$dm<method>` bind's body,
    emitted with `c`'s OWN methods spelled bare (`MethodRef.bare` — a qualified
    sibling reference does not elaborate inside a class body; see that field).
    `none` exactly when the `$dm` bind is absent, which `translatedDefaults` has
    already excluded for every pair emission asks about.

    `mm` must carry an entry for every sibling the body calls, or that call emits
    `<method>_<unique>` and the class body does not elaborate — loud, and the
    residual documented on `MethodRef.bare`. Everything else in a default body is
    ordinary: builtins go through `Maps.valueMap`, a call to another CLASS's method
    stays qualified (and is a forward reference whenever that class is emitted
    later, since class decls are unsorted until Task 5), and a call to a top-level
    user function is a forward reference always — the class block precedes every
    def. Only sibling methods, builtins and locals are safe there. -/
def classDefaultBody (mm : List MethodRef) (top : List Name) (binds : CoreProgram)
    (c : ClassDecl) (method : Name) : Option String :=
  let selfBare := mm.map fun r => if r.cls == c.name then { r with bare := true } else r
  (findBind binds ("$dm" ++ method)).map (fun (_, e) => emitExpr selfBare top e)

/-- Top-level `$dm<method>` binds whose binder ROLE says `dict`. Should be empty:
    the shim classifies `$dm` as `id` (see `shim/Main.hs`'s `binderRole`). A
    non-empty result means the dump's roles are the old heuristic's, under which
    `Lower.isTypeOrDictArg` silently ERASES a `$dm` reference in argument
    position; wired to a warning in `Main.lean`.

    Only top-level binders are scanned, which is sufficient: the shim resolves a
    `Var` reference through the binder it came from, so a reference's role is its
    binder's role. -/
def dmBindsMislabelledAsDicts (binds : CoreProgram) : List Name :=
  let bad (v : Var) : Bool := v.name.startsWith "$dm" && v.role == .dict
  binds.flatMap fun b => match b with
    | .nonRec v _ => if bad v then [v.name] else []
    | .rec_ pairs => pairs.filterMap (fun (v, _) => if bad v then some v.name else none)

/-- The warning for one `dmBindsMislabelledAsDicts` entry. -/
def dmDictRoleWarning (n : Name) : String :=
  s!"default-method binding `{n}` arrived with binder role `dict`. It is a method\n" ++
  s!"  BODY, not a dictionary — the shim's role heuristic (`$d`-prefixed ⇒ dict) must\n" ++
  s!"  exempt `$dm`, and this dump's does not. Consequence: a reference to `{n}` in\n" ++
  s!"  argument position is erased as a dictionary argument, silently dropping the\n" ++
  s!"  default's body from wherever it was passed. Rebuild the shim."

/-- How one class method of one instance is realized. -/
inductive MethodFate where
  /-- A `$c<method>` bind for this instance head → wire it as the field. -/
  | field (ref : String)
  /-- Omitted from the instance: the class body's `:=` default fills it. Either
      there is no `$c<method>` bind at all, or the one there is is GHC's wrapper
      around the same default. -/
  | fromDefault
  /-- No bind and no default. The instance is SKIPPED (an instance missing a
      field does not elaborate) and `unresolvedInstanceMethods` reports it. -/
  | unresolved
deriving Repr, DecidableEq, Inhabited

/-- The single decision procedure shared by `emitInstanceUser` (what to emit) and
    `unresolvedInstanceMethods` (what to warn about). Keeping it in one place is
    what stops the warning and the emission from drifting apart — a drift that
    would be silent in both directions (warn about an instance that emitted fine,
    or skip one with no diagnostic). -/
def classifyInstanceMethod (defaults : List (Name × Name)) (binds : CoreProgram)
    (cls : Name) (headTyStr : String) (m : ClassMethod) : MethodFate :=
  let defaulted := defaults.contains (cls, m.name)
  match findClassMethodBind binds ("$c" ++ m.name) headTyStr with
  | some (v, e) =>
    if defaulted && isDefaultWrapperBody m.name e then .fromDefault else .field (localId v)
  | none => if defaulted then .fromDefault else .unresolved

/-- Emit a user-class instance: for each class method, `classifyInstanceMethod`
    decides between wiring the `$c<method>` bind as a field, omitting the field so
    the class-body default fills it, and being unresolvable.

    PER-METHOD since M3 Task 4. The all-or-nothing test it replaces (`every`
    method must resolve to a `$c` bind) dropped the whole instance the moment one
    method came from a default. It also dropped it SILENTLY, which is the half
    this function cannot fix on its own — `unresolvedInstanceMethods` is the same
    decision run for its diagnostic, wired to an `eprintln` in `Main.lean`.

    A fieldless instance is legal Lean and is emitted as such (`instance : C T
    where` with nothing after it) — that is the shape for a class every one of
    whose methods is defaulted and unoverridden; PROBED. What is NOT emitted is an
    instance of a class with no methods at all: `cd.methods.isEmpty` keeps the old
    `none`, since such a class has no `$c` binds to have been dropped and nothing
    to say. -/
def emitInstanceUser (defaults : List (Name × Name)) (classes : List ClassDecl)
    (binds : CoreProgram) (i : Instance) : Option String := do
  let cd ← classes.find? (·.name == i.className)
  if cd.methods.isEmpty then none else
  let tyStr := i.headTypes.map emitType |> String.intercalate " "
  let fates := cd.methods.map fun m =>
    (m, classifyInstanceMethod defaults binds i.className tyStr m)
  if fates.any (fun (_, f) => f == .unresolved) then none else
  let fields := fates.filterMap fun (m, f) =>
    match f with
    | .field ref => some s!"  {sanitize m.name} := {ref}"
    | _          => none
  if fields.isEmpty then some s!"instance : {sanitize i.className} {tyStr} where"
  else some (s!"instance : {sanitize i.className} {tyStr} where\n"
               ++ String.intercalate "\n" fields)

/-- An instance head spelled the way the SOURCE spells it (`Quiet`,
    `(Int, Int)`-ish), for diagnostics only. `emitType`'s spelling is the emitter's
    pre-resolution `(GHCCore.tyConOpaque "Quiet")` needle, which is the right key
    for matching binds and the wrong thing to show a user. -/
private def headTypeNames (i : Instance) : Name :=
  let render : GHCType → Name
    | .tyCon n args => if args.isEmpty then n else s!"({n} …)"
    | .tyVar n      => n
    | _             => "?"
  String.intercalate " " (i.headTypes.map render)

/-- Instance methods that resolve to NOTHING — no `$c<method>` bind for the
    instance head and no translated class default — as
    `(class, head type, method)`. Each one costs the WHOLE instance
    (`emitInstanceUser` returns `none`; an instance missing a field does not
    elaborate), so this is the diagnostic for a skip that used to be silent.

    A WARNING, not a refusal: the consequence is a `failed to synthesize C T` at
    every use site, i.e. already loud at `lake build`; refusing here would newly
    reject modules that transpile today (an unused instance of a partially
    droppable class). Reachable shapes: a method whose bind `Main.lean`'s drop
    rules filtered (`$c/=` of an `Eq`-instance head, the three `$cshow…` names); a
    class-shape channel listing a method the Core reconstruction has no bind for
    (`mergeClassDecls`' methods-disagree path); and — the one this fires on today
    — a method whose type does not START with the class parameter, since
    `findClassMethodBind` attributes a `$c` bind to an instance by matching its
    FIRST value argument against the instance head. OBSERVED on
    `examples/haskell/SuperClass.hs`: `$cempty : Bag` (no argument at all) and
    `$cinsert : (Int -> (Bag -> Bag))` (first argument `Int`) both fail that
    match, which is exactly the instance Task 1 recorded as silently dropped.

    Builtin classes cannot appear here: `Eq`/`Ord`/`Show` instances never reach
    `emitInstanceUser`, and no `ClassDecl` is ever built for them
    (`reconstructClasses` and `mergeClassDecls` both filter `builtinClasses`), so
    the `find?` below fails and the instance contributes nothing. -/
def unresolvedInstanceMethods (p : Program) : List (Name × String × Name) :=
  let classes  := mergeClassDecls p.classDecls (reconstructClasses p.binds p.instances).1
  let defaults := translatedDefaults p.binds classes
  p.instances.flatMap fun i =>
    match classes.find? (·.name == i.className) with
    | none    => []
    | some cd =>
      let tyStr := i.headTypes.map emitType |> String.intercalate " "
      cd.methods.filterMap fun m =>
        if classifyInstanceMethod defaults p.binds i.className tyStr m == .unresolved
        then some (i.className, headTypeNames i, m.name) else none

/-- The warning for one `unresolvedInstanceMethods` entry. -/
def unresolvedInstanceMethodWarning (cls head mname : Name) : String :=
  s!"instance `{cls} {head}` is DROPPED: its method `{mname}` resolves to nothing —\n" ++
  s!"  no `$c{mname}` binding for that instance head survives in this module, and the\n" ++
  s!"  class declares no default body for it (or the default's `$dm{mname}` binding is\n" ++
  s!"  itself missing). A Lean instance cannot omit a field that has no default, so\n" ++
  s!"  the whole instance is skipped; every use of `{cls}`'s methods at `{head}` will\n" ++
  s!"  fail with `failed to synthesize {cls} {head}` at `lake build`.\n" ++
  s!"  Likely causes: `{mname}`'s type does not start with the class parameter (a\n" ++
  s!"  `$c` binding is matched to its instance by its FIRST value argument, so\n" ++
  s!"  `{mname} :: Int -> a -> a` or `{mname} :: a` cannot be attributed); the binding\n" ++
  s!"  was filtered as `Eq`/`Show` plumbing (see Main.lean's drop rules); or the\n" ++
  s!"  class-shape dump declares a method this module has no binding for."

/-- Emit a Lean `instance` block. `Eq` → Lean `BEq`, `Ord` → Lean `Ord` (the
    latter via `deriving` in the data block), and user classes via
    `emitInstanceUser`. Returns `none` for classes we don't model (Show, Read). -/
def emitInstance (defaults : List (Name × Name)) (classes : List ClassDecl)
    (derivedEq : List String) (binds : CoreProgram) (i : Instance) : Option String :=
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
  | _ => emitInstanceUser defaults classes binds i

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

/-! ## Name-resolution post-passes

Emitted text passes through an ORDERED pipeline of textual resolution passes.
Both the order and each pass's site list are load-bearing.

  1. `resolveUserTypes`      opaque local tycon → bare       — bodies, data block,
                                                               spec text (3 sites)
  2. `resolveNewtypes`       newtype → underlying type       — after 1, before 3,
                                                               SAME 3 sites
  3. `resolveUserCtors`      ctor in application position → `T.C`
                                                             — bodies + spec text
                                                               ONLY, never the
                                                               data block
  4. `resolveExternalTypes`  remaining opaque → `M.T`        — whole output, last;
                                                               requires 1 to have
                                                               run on EVERY section

Pass 1's three sites are, concretely: `emitFullProgram`'s `bodyResolved`
(bodies + instances), its `dataBlock`, and `resolveSpecText` (user `@lean` theorem
text). Passes 3 and 4 run at the first and third of those — pass 4 covering the
whole joined output rather than the body section alone. Pass 3 must never see the
data block: it would rewrite the inductive's own `| Ctor ` lines. Pass 4 must run
last, and pass 1 must have reached every section before it, or a local type still
spelled opaque gets rewritten to `M.T` for its OWN module `M`.

Newtype erasure (pass 2) adds two constraints of its own, both live:

* Passes 1 and 3 take `keptTypeDecls`, NOT `p.typeDecls`. Pass 1 on the full set
  would consume the `(GHCCore.tyConOpaque "Age")` needle and rewrite it to a bare
  `Age` that pass 2 can no longer see (and that no `inductive` declares).
* Newtypes stay IN `sortDataDecls`' input (dependency chains thread through them
  transitively, e.g. `Point` → `Wrapper`(newtype) → `Q`); they are filtered out
  only at the emission map — filtering before the sort loses the chain and
  reintroduces the forward-reference bug. Pass 2's substituted STRINGS are
  themselves pre-resolved (`newtypeSubsts`) for the same chain reason: a newtype
  wrapping a local type must not splice a needle back in after pass 1 has run.

IMPORTED newtypes are erased at pass 2 as well, from the manifest's `newtype`
channel (`extNts`) appended AFTER the local substitutions. Pass 2 is the only slot
that works: pass 1 is keyed off local decls (the client has none for an imported
type), and pass 4 would rewrite the needle to a `NewtypeBasic.Age` that does not
exist — so the erasure has to consume the needle before pass 4 sees it. Sound
because the published underlying string is module-independent by construction
(`newtypeExports`), and because instance MATCHING still happens on the opaque
spelling: `derivedEqTypes`/`ordTypes`/`findClassMethod` keys are built before any
of these passes run, so erasing `Age` → `Int` here cannot cross-match instances.
-/

/-- Rewrite occurrences of `(GHCCore.tyConOpaque "X")` to the bare name `X`
    for every user-declared type. The Core dump types user types as opaque
    (since the shim doesn't know the lakefile's type-ctor map); after the
    transpiler emits `inductive X where …`, opaque references should resolve
    to that inductive directly.

    Takes the KEPT decls (`keptTypeDecls`), not every `typeDecls` entry: an
    erased newtype must keep its opaque spelling through this pass so that
    `resolveNewtypes` (pass 2) still finds its needle. -/
def resolveUserTypes (decls : List DataDecl) (src : String) : String :=
  decls.foldl (init := src) fun s d =>
    let needle := s!"(GHCCore.tyConOpaque \"{d.name}\")"
    let replacement := sanitize d.name
    s.replace needle replacement

/-! ### Newtype erasure (pass 2)

A `newtype` has no Lean image at all: Core already identifies it with its
underlying type (GHC erases wrap/unwrap into `Cast`s that never reach the shim —
see the M2 Task 3 observation in `Tests/Unit.lean`), so the emitted VALUES are
plain identities and only the emitted TYPES still mention it. Erasing the type
makes those values typecheck.
-/

/-- Newtypes that erase, as (declared name, underlying type as `emitType` gives
    it — the single ctor's single field).

    A "newtype" with ≠1 ctor or ≠1 field is a MALFORMED dump (Haskell admits
    neither shape), so it is not erased: it is absent from this list and every
    consumer below therefore treats it exactly like a `data` decl — emitted as
    an `inductive`, its ctors qualified. That is loud downstream rather than
    silent, because GHC has already erased the value level: identity bodies
    against a surviving one-field-per-ctor inductive are type MISMATCHES. No
    `panic!`, no invented recovery. -/
def newtypeDecls (decls : List DataDecl) : List (Name × String) :=
  decls.filterMap fun d =>
    if d.kind != "newtype" then none
    else match d.ctors with
      | [c] => match c.fields with
        | [f] => some (d.name, emitType f.ty)
        | _   => none
      | _   => none

/-- The decls that keep a Lean image: everything except the newtypes
    `newtypeDecls` erases. THE key for every newtype suppression site
    (`resolveUserTypes`, `resolveUserCtors`, `ctorNames`, the `datas` emission
    map), so a malformed newtype is uniformly treated as data. -/
def keptTypeDecls (decls : List DataDecl) : List DataDecl :=
  let erased := (newtypeDecls decls).map (·.1)
  decls.filter fun d => !erased.contains d.name

/-- Wrap an underlying type string for substitution into the fully-bracketed
    hole a nullary opaque tycon leaves. `(GHCCore.tyConOpaque "Ages")` may sit in
    application-argument position (`List (GHCCore.tyConOpaque "Ages")`), so an
    unbracketed juxtaposition like `List Int` has to become `(List Int)` or
    `List List Int` results. Same rule (and the same closed set of `emitType`
    shapes) as `Maps.parenArg`. -/
private def newtypeArg (u : String) : String :=
  if u.contains ' ' && !u.startsWith "(" then s!"({u})" else u

/-- Rewrite `(GHCCore.tyConOpaque "N")` → the underlying type of newtype `N`.
    Runs AFTER `resolveUserTypes` (whose decl set excludes these newtypes, so
    the needle survives) and BEFORE `resolveUserCtors`. The needle is the whole
    opaque form, so there is no substring bleed between related names (`Age` vs.
    `Wage`: the needle's `"` delimiters block it).

    The underlying strings must already be pipeline-resolved — use
    `newtypeSubsts`, never `newtypeDecls` directly. -/
def resolveNewtypes (nts : List (Name × String)) (src : String) : String :=
  nts.foldl (init := src) fun s (n, u) =>
    let needle := s!"(GHCCore.tyConOpaque \"{n}\")"
    s.replace needle (newtypeArg u)

/-- `newtypeDecls` with each underlying string put through the OTHER newtypes'
    erasures: `newtype A = A B` where `B` is itself a newtype. Fuel-bounded (a
    chain of n newtypes needs n-1 rounds) and self-references are excluded, so
    the legal-but-useless `newtype A = A A` cannot diverge (it stays opaque →
    loud). Saturating the MAP rather than re-scanning the source also makes the
    result independent of dump order.

    The shared basis of the two consumers, which differ in exactly one step:
    `newtypeSubsts` (for splicing into THIS module's text) additionally resolves
    local opaque tycons to bare names; `newtypeExports` (for DEPENDENT modules)
    must not, because a bare local name means nothing there — it filters those
    newtypes out instead. -/
def newtypeChainSubsts (decls : List DataDecl) : List (Name × String) :=
  let raw := newtypeDecls decls
  let rec saturate (fuel : Nat) (nts : List (Name × String)) : List (Name × String) :=
    match fuel with
    | 0        => nts
    | fuel + 1 => saturate fuel (nts.map fun (n, u) =>
                    (n, resolveNewtypes (nts.filter (·.1 != n)) u))
  saturate raw.length raw

/-- The substitution list the pipeline actually applies: `newtypeChainSubsts`
    with each underlying string put through the passes that have ALREADY run on
    the text it gets spliced into, so no substitution can reintroduce a stale
    needle — local opaque tycons made bare. `newtype Wrapper = Wrapper Q` for a
    local `data Q` yields `(GHCCore.tyConOpaque "Q")` from `emitType`, and pass 1
    has already run over the source; splicing that raw would leave a live needle
    for `resolveExternalTypes` to rewrite to a nonexistent `M.Q`. -/
def newtypeSubsts (decls : List DataDecl) : List (Name × String) :=
  (newtypeChainSubsts decls).map fun (n, u) => (n, resolveUserTypes (keptTypeDecls decls) u)

/-! ### Cross-module newtype erasure (the manifest's `newtype` channel)

An imported newtype reaches a client module's Core as a BARE tycon — observed
`{"name": "Age", "tag": "TyCon"}` in `RecordClient`'s dump, the same convention
imported `data` types use — so `emitType` hands the client the same
`(GHCCore.tyConOpaque "Age")` needle the defining module produced. But the client
has no `typeDecls` entry for `Age` (the decl plugin dumps only the current
module's `tcg_tcs`), so pass 2 knows nothing to rewrite it to, and the
data-channel manifest deliberately carries no `Age` entry (there is no
`NewtypeBasic.Age` to point at). The needle would survive into the generated Lean
— loud, but the client cannot be transpiled at all.

The defining module therefore PUBLISHES its erasable newtypes as a second
manifest channel (`newtypeExports` → `newtypeManifestLine` → `transpile.sh`
appends → `parseExtManifest` → pass 2's substitution list). Sound because the
published string is module-INDEPENDENT: see `newtypeExports`' filter.
-/

/-- THIS module's newtypes that a DEPENDENT module can erase, as (name,
    underlying) manifest pairs.

    The filter is the whole soundness argument: an underlying string is
    exportable iff it contains no `GHCCore.tyConOpaque` needle, i.e. iff it is
    built entirely out of `typeConMap`-mapped tycons (`Int`, `List Int`,
    `(Int × Int)`, …). `emitType` emits the opaque needle for PRECISELY the
    unmapped tycons, so that one substring test subsumes every case where the
    string would be meaningless in another module:

    * a local user type (`newtype Wrapper = Wrapper Q`) — skipped, because the
      client has no `Q` in scope and the correct spelling would be `M.Q` (which
      needs qualified-underlying resolution: deliberately out of M2 scope);
    * an imported or otherwise unknown user type — skipped identically;
    * a chain that does not bottom out in a mapped type, and the recursive
      `newtype R = R R` — skipped, since `newtypeChainSubsts` leaves the needle.

    Skipping is loud, not silent: the client's needle survives into the emitted
    Lean, where `GHCCore.tyConOpaque` is undefined. Note the underlying string is
    taken PRE-`resolveUserTypes` (`newtypeChainSubsts`, not `newtypeSubsts`) —
    that pass would rewrite a local `(GHCCore.tyConOpaque "Q")` to a bare `Q` and
    hide it from this filter. -/
def newtypeExports (decls : List DataDecl) : List (Name × String) :=
  (newtypeChainSubsts decls).filter fun (_, u) =>
    (u.splitOn "GHCCore.tyConOpaque").length == 1

/-! ### Newtype-instance guard (Program validation, NOT a resolution pass)

Erasure identifies a newtype with its underlying type, so an instance whose head
is a newtype has nowhere to go — and both places it *can* go are silent-wrong,
the one failure mode this project forbids:

* **Eq relocates.** `newtype Mod7 = Mod7 Int` + a hand-written `Eq Mod7` emits
  `instance : BEq Int where beq := <mod-7 function>` inside the module namespace,
  so every `==` on `Int` in the module (theorem text included) silently means
  mod-7. Observed: `((1 : Int) == 8) = false` is *refuted* by `decide`.
* **Ord vanishes.** `newtype Coin = Coin Int` + `instance Ord Coin where compare
  (Coin a) (Coin b) = compare b a` matches `ordTypes` on the opaque head, so
  `isSuppressedMethod` drops every `$c` method, while the newtype is filtered out
  of `datas` and gets no `deriving Ord` either. The user's reversed `compare` is
  gone and Lean's own `Int` order takes over — with zero diagnostics.

So: ANY instance whose head type is a newtype is a hard transpiler error.

Derived-vs-hand-written is not distinguishable here (`tcg_insts` carries no
origin marker and GND instances have no `$c` methods to sniff — M2 spec
correction 3), so `deriving (Show)` on a newtype is refused for the same reason.
Relaxable later by extending the decl-plugin to dump instance origin.

Detection is STRUCTURAL: every newtype mentioned anywhere in a head type is
flagged, argument positions included. A newtype in argument position was the
sharpest silent-wrong hole here — `instance Eq (Celsius, Celsius)` reads as head
`(,)`, so a head-only check let it through and emitted
`instance : BEq (Int × Int)` with zero diagnostics, relocating Eq onto every pair
of `Int`s in the module. Observed on the pre-fix binary: exit 0, empty stderr,
and `theorem _ : ((1,2) == (1,3)) = true := by decide` builds.

CROSS-MODULE (M2 Task 6). The check must see IMPORTED newtypes too, and this is
soundness-critical rather than cosmetic. Task 5 could scope the check to the
current module's `typeDecls` only because nothing then erased an imported
newtype's needle, so an orphan `instance Eq Age` in a client failed loud at `lake
build` (`GHCCore.tyConOpaque` is undefined — `GhcCoreToLean/Runtime.lean` declares
no such symbol; grep: its only occurrences in this repo are the emitter's own
needle-construction and needle-rewriting sites). Task 6's manifest `newtype`
channel erases that needle, which would have turned the very same input into
failure mode (a) above — `instance : BEq Int` in the client's namespace, silently.
So `newtypeInstanceViolations` takes the imported newtype names as well, and the
INVARIANT tying the two features together is:

  the guard's newtype-name set ⊇ the set pass 2 erases.

Locally that holds because the guard keys off `newtypeNames` (ALL newtypes)
while pass 2 erases only `newtypeDecls` (well-formed ones). Across modules it
holds because both sides read the SAME manifest channel: an imported newtype is
erased iff `newtypeExports` published it, and exactly those names are handed to
the guard. An imported newtype `newtypeExports` skipped (underlying not fully
mapped) is erased by neither, and stays loud at `lake build` as before.

One deliberate scope limit remains, recorded rather than fixed:

* An instance on an imported newtype whose defining module is NOT in the current
  transpile graph (hence contributes no manifest entry) is still invisible here —
  and still loud at `lake build`, by the surviving-needle argument above.
-/

/-- Names of ALL `newtype` decls — well-formed or not.

    The guard keys off THIS, deliberately not off `newtypeDecls`: a malformed
    newtype does not erase, but it is still a newtype at the source level (GHC has
    still erased its value level), so an instance on it is just as unrepresentable
    and must be refused just as loudly. -/
def newtypeNames (decls : List DataDecl) : List Name :=
  (decls.filter (·.kind == "newtype")).map (·.name)

/-- `newtype` decls dumped with a shape Haskell does not admit (≠1 ctor or ≠1
    field) and which therefore do NOT erase — see `newtypeDecls`. Reported as a
    warning at the validation site so the shape's only diagnostic isn't an
    indirect Lean type mismatch. -/
def malformedNewtypes (decls : List DataDecl) : List Name :=
  let erased := (newtypeDecls decls).map (·.1)
  (newtypeNames decls).filter fun n => !erased.contains n

mutual
  /-- Every name from `nts` MENTIONED anywhere in a type — head position, tycon
      arguments, either side of an application or arrow, or a `∀` body.
      Duplicates are kept; the caller dedups.

      Structural rather than head-only because the head tycon alone misses the
      worst case: `instance Eq (Celsius, Celsius)` has head `(,)`, so a head-only
      check passed it through and emitted `instance : BEq (Int × Int)` — see the
      section header. Written as a `mutual` pair with `newtypeMentionsAll` so the
      recursion through `.tyCon`'s argument LIST is structural: `partial` would
      make this opaque to kernel reduction and the `#guard`s pinning it in
      `Tests/Unit.lean` would not elaborate. -/
  private def newtypeMentions (nts : List Name) : GHCType → List Name
    | .tyCon n args => (if nts.contains n then [n] else []) ++ newtypeMentionsAll nts args
    | .tyApp f x    => newtypeMentions nts f ++ newtypeMentions nts x
    | .tyFun a r    => newtypeMentions nts a ++ newtypeMentions nts r
    | .forAll _ b   => newtypeMentions nts b
    | .tyVar _      => []
    | .tyLit _      => []

  /-- `newtypeMentions` over a list of types — the recursive half that walks
      `.tyCon`'s arguments and, at the top level, an instance's `headTypes`. -/
  private def newtypeMentionsAll (nts : List Name) : List GHCType → List Name
    | []      => []
    | t :: ts => newtypeMentions nts t ++ newtypeMentionsAll nts ts
end

/-- Instances the transpiler must REFUSE, as `(className, newtypeName)` pairs.

    Every element of `headTypes` is scanned (not just the first — `instance
    Convert Int Celsius` is as unrepresentable as `instance Eq Celsius`), and each
    is scanned STRUCTURALLY, not just for its head tycon (`instance Eq (Celsius,
    Celsius)` is unrepresentable too, and was the silent-wrong hole this closed).
    One pair per distinct `(class, newtype)`: a head naming the same newtype twice
    is one problem reported once, while a multi-parameter class mentioning two
    different newtypes still reports both. Dedup keeps the first occurrence, so
    report order follows the dump.

    `extNtNames` are IMPORTED newtype names (the manifest's `newtype` channel).
    Passing them is soundness-critical, not optional politeness: those are exactly
    the names pass 2 now erases across module boundaries, so without them an
    orphan `instance Eq Age` in a client would silently relocate onto `Int`. See
    the section header's invariant. -/
def newtypeInstanceViolations (insts : List Instance) (decls : List DataDecl)
    (extNtNames : List Name := []) : List (Name × Name) :=
  let nts := newtypeNames decls ++ extNtNames
  (insts.flatMap fun i =>
    (newtypeMentionsAll nts i.headTypes).map fun n => (i.className, n)).eraseDups

/-- The refusal message for one `newtypeInstanceViolations` pair: names the class,
    the newtype, its underlying type when the newtype is well-formed enough to
    have one, and the remedy.

    `extNts` (the manifest's `newtype` channel) is consulted for the underlying
    type as well, so a violation on an IMPORTED newtype names `Int` rather than
    claiming the dump is malformed — the local `typeDecls` never contain an
    imported decl. Local entries take precedence, matching pass 2's shadowing. -/
def newtypeInstanceError (decls : List DataDecl) (v : Name × Name)
    (extNts : List (Name × String) := []) : String :=
  let (cls, nt) := v
  let under? := (newtypeSubsts decls ++ extNts).find? (·.1 == nt) |>.map (·.2)
  let erasedTo := match under? with
    | some u => s!" (erased → `{u}`)"
    | none   => " (malformed dump: it does not even erase cleanly)"
  let remedy := match under? with
    | some u => s!"write the instance — and any property about it — against\n" ++
                s!"  the underlying type `{u}`, or drop the instance"
    | none   => "write the instance — and any property about it — against\n" ++
                "  the underlying type, or drop the instance"
  s!"newtype instance not representable: `instance {cls} {nt}`\n" ++
  s!"  `{nt}` is a newtype{erasedTo}. Newtypes are erased to their underlying\n" ++
  s!"  type, so an instance on one has no Lean image: it would either silently\n" ++
  s!"  reattach to the underlying type (changing the meaning of every use of\n" ++
  s!"  `{cls}`'s methods at that type in this module, theorem text included) or be\n" ++
  s!"  dropped outright. Both are silent-wrong, so transpilation is refused.\n" ++
  s!"  Remedy: {remedy}.\n" ++
  s!"  Note: a `deriving` clause on a newtype is refused for the same reason —\n" ++
  s!"  the dump carries no derived-vs-hand-written marker to tell them apart.\n" ++
  s!"  Note: `{nt}` may sit NESTED in the instance head (e.g. `instance {cls}\n" ++
  s!"  ({nt}, {nt})`) rather than be the head itself; that is refused identically,\n" ++
  s!"  because the head's Lean image is built from the erased type."

/-- The warning for a malformed `newtype` (see `malformedNewtypes`). Not an error:
    Haskell admits neither shape, so only a corrupt or out-of-date decl sidecar
    can produce one, and the downstream failure is already loud (GHC erased the
    value level, so identity bodies against a surviving one-field inductive are
    type MISMATCHES). Erroring here would newly refuse input that currently
    transpiles; warning names the consequence up front instead. -/
def malformedNewtypeWarning (n : Name) : String :=
  s!"malformed newtype `{n}`: dumped with ≠1 constructor or ≠1 field, a shape\n" ++
  s!"  Haskell does not admit, so it is NOT erased and is emitted as an ordinary\n" ++
  s!"  data type. GHC has already erased its value level, so the generated Lean is\n" ++
  s!"  expected to FAIL to typecheck (identity bodies against a one-field\n" ++
  s!"  inductive). This indicates a corrupt or out-of-date decl sidecar."

/-- Characters that continue (or qualify) a Lean identifier. A ctor-name
    occurrence flanked by one of these is part of a LONGER name — `mkPoint`,
    `Points`, `Point.Point` — and must never be rewritten. -/
private def isIdentish (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '\'' || c == '.'

/-- Characters that can START a Lean value argument, i.e. that mark the
    preceding identifier as being APPLIED.

    Deliberately EXCLUDES lowercase letters: `instance : BEq CustomRatio where`
    would otherwise read `where` as an argument and rewrite a *type* to a ctor.
    The cost is that a ctor applied to a bare variable (`Point x y` in a user
    spec) is not rewritten — Lean then fails loud ("function expected at
    Point"), never silently. `-` is excluded for the same fail-loud reason:
    `Point -1 2` is subtraction in Lean, so a negative literal argument has to
    be parenthesised anyway (and then `(` fires). -/
private def isArgStart (c : Char) : Bool :=
  c == '(' || c == '[' || c == '⟨' || c.isDigit

/-- Boundary-aware rewrite of `bare` → `qual` at every APPLICATION-position
    occurrence: identifier boundaries on both sides (so `mkPoint` and an
    already-qualified `Point.Point` are left alone) and an argument following
    (`isArgStart`). This is what covers a ctor applied to a *literal*
    argument — `Rect (Point 0 0) 1 1` — which the fixed needles in
    `resolveUserCtors` cannot express: they all require a `(` immediately
    after the ctor name. -/
def replaceCtorApps (bare qual : String) (src : String) : String :=
  match src.splitOn bare with
  | []              => src
  | first :: pieces =>
    -- `pieces` are the gaps AFTER each occurrence; occurrence `i` sits between
    -- gap `i-1` and gap `i` (`next`). The LEFT boundary is read straight off the
    -- output built so far, which is always the text immediately preceding this
    -- occurrence: a non-empty preceding gap ends `acc`, and an EMPTY one means
    -- the previous occurrence was adjacent — that one's `appOK` was then false
    -- (its gap started with `bare`, not an arg), so it emitted `bare` and left
    -- `acc` ending identifier-ish, correctly blocking this one too. `acc` starts
    -- as `first`, so `acc.isEmpty` also covers the start-of-string case.
    let rec go (pieces : List String) (acc : String) : String :=
      match pieces with
      | []           => acc
      | next :: more =>
        let leftOK  := acc.isEmpty || !isIdentish acc.back
        let rightOK := next.isEmpty || !isIdentish next.front
        let after   := next.dropWhile (· == ' ')
        let appOK   := !after.isEmpty && isArgStart after.front
        let repl    := if leftOK && rightOK && appOK then qual else bare
        go more (acc ++ repl ++ next)
    go pieces first

/-- Qualify user-defined data constructors in any position where Lean's
    elaborator would otherwise be ambiguous (type vs. ctor under the same
    name). The recognised call-shapes are:

      *  `| Ctor `                              ← alt-pattern
      *  `(Ctor)`                               ← App in transpiler-emitted style
      *  `Ctor (` (preceded by whitespace)      ← App in user `[lean| … |]` spec
      *  `Ctor <arg>` at identifier boundaries  ← App to a literal/bracketed
                                                  argument (`replaceCtorApps`)

    Type annotations like `(x : T)` or `→ T →` match none of these, so they
    remain `T` and resolve to the type. -/
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
      let s := rules.foldl (init := s) fun s (needle, repl) => s.replace needle repl
      replaceCtorApps bareCtor qualCtor s

/-! ### The imported-type manifest (`EXT_TYPES_MANIFEST`)

Tab-separated, one entry per line, built per run by `transpile.sh`. TWO channels:

    Point⇥RecordOps      DATA — imported type `Point` is declared by module
                         `RecordOps`, so it emits as `RecordOps.Point`
                         (`resolveExternalTypes`, pass 4). Written by
                         `scripts/transpile_graph.py manifest`.
    Age⇥newtype⇥Int      NEWTYPE — imported newtype `Age` has no Lean name at
                         all; it ERASES to `Int` (`resolveNewtypes`, pass 2).
                         Written by the defining module's own transpile
                         (`newtypeExports`, appended by `transpile.sh`).

The channels cannot collide: a data line's second field is a MODULE name, and
`newtype` is a lowercase Haskell keyword, so no module can be called that. The
two lists must also stay DISJOINT downstream — a newtype leaking into the data
channel would emit `newtype.Age`.

Keys are BARE type names, so two graph modules declaring the same type name are
ambiguous. WITHIN the DATA channel that is a pre-existing property and first entry
wins (dependency order); its consequence is a mis-qualified `WrongModule.Point`,
which is loud almost always.

The two ambiguity shapes that involve the NEWTYPE channel are NOT that benign, so
`parseExtManifest` refuses both rather than picking a winner:

  * ACROSS the channels. Graph `{A: newtype Age = Age Int, B: data Age = …,
    C: imports B's Age}`: the manifest carries both `Age⇥B` and `Age⇥newtype⇥Int`,
    and pass 2 runs first, so C's `f :: Age -> Int` over B's DATA type emits
    `f : Int → Int` and a `@lean` theorem verifies a property about `Int` instead.
    That typechecks — silent-wrong.

  * WITHIN the newtype channel, with two DISTINCT underlyings. Graph
    `{A: newtype Key = Key Int, B: newtype Key = Key [Int], C: imports B's Key}`:
    the manifest carries `Key⇥newtype⇥Int` and `Key⇥newtype⇥List Int`,
    `resolveNewtypes` folds left so the FIRST wins, and C's `idKey :: Key -> Key`
    over B's `[Int]` emits `idKey : Int → Int` — with `∀ (k : Int), idKey k = k`
    reported valid. Also silent-wrong, and with no wrong-module name anywhere in
    the output to make it loud the way the data channel's clash is. The SAME
    underlying published by several modules is NOT this case: those entries are
    interchangeable, so they dedup to one.

In both refused shapes ALL of the name's entries are dropped and the name is
reported: the reference stays opaque and fails loud at `lake build`.

REACHABILITY, since the gate fix below landed: neither shape can arise from a
normal `transpile.sh` run any more. Both graphs need TWO modules to declare the
name, and the second one to be transpiled sees the first's entry — its own data
self-entry excluded — so `localImportCollisions` refuses it and the run aborts
before the manifest can hold the conflicting pair. These two checks therefore now
guard a hand-assembled or stale manifest, which is exactly where a
warn-and-drop (rather than a hard refusal) belongs.
-/

/-- The `newtype` channel's discriminator field. Lowercase and a Haskell keyword,
    hence never a module name — see the manifest section header. -/
def newtypeChannelTag : String := "newtype"

/-- The manifest line the DEFINING module publishes for one exported newtype (see
    `newtypeExports`). The underlying string may contain SPACES (`List Int`) but
    never a tab, so the 3-field split back out is unambiguous. -/
def newtypeManifestLine (n : Name) (u : String) : String :=
  s!"{n}\t{newtypeChannelTag}\t{u}"

/-- The manifest's two channels, plus the lines that parsed as neither. -/
structure ExtManifest where
  /-- DATA channel: (type name, defining module) → `resolveExternalTypes`. -/
  datas    : List (String × String) := []
  /-- NEWTYPE channel: (newtype name, underlying type) → `resolveNewtypes`. -/
  newtypes : List (Name × String)   := []
  /-- Lines that matched no channel; the caller warns and drops them. -/
  rejected : List String            := []
  /-- Irreconcilably ambiguous names — found in BOTH channels, or in the newtype
      channel with two DIFFERENT underlyings. ALL their entries are dropped in
      either channel, and the caller warns. -/
  ambiguous : List Name             := []
  deriving BEq, Repr, Inhabited

/-- Parse an `EXT_TYPES_MANIFEST` file body into its two disjoint channels (see
    the manifest section header for the line formats).

    A 2-field line whose module field is exactly `newtype` is a TRUNCATED newtype
    line: rejected, never read as data (as data it would emit `newtype.Age`).
    That check is what makes the "channels cannot collide" claim hold at the
    parser and not merely at the writers.

    Unparseable lines are REJECTED (reported by the caller) and dropped, not
    fatal: a dropped entry leaves the `(GHCCore.tyConOpaque "T")` needle in the
    emitted Lean, where `GHCCore.tyConOpaque` is undefined — so the failure mode
    of skipping is loud at `lake build`, whereas aborting would refuse a module
    over a corrupt line the user never wrote. Empty lines (the trailing newline
    always yields one) are neither parsed nor reported.

    A newtype-channel name is dropped from BOTH channels and reported in
    `ambiguous` when it also appears in the data channel, OR when it appears with
    two DIFFERENT underlying types — the two configurations where picking a winner
    would be silent-wrong rather than loud (see the section header's two graphs).
    Repeats of the SAME underlying are interchangeable, so they dedup to one entry
    and are not ambiguous. -/
def parseExtManifest (s : String) : ExtManifest :=
  let raw : ExtManifest := (s.splitOn "\n").foldl (init := {}) fun m line =>
    let reject := { m with rejected := m.rejected ++ [line] }
    if line.isEmpty then m else
    match line.splitOn "\t" with
    | [t, modName] =>
      if t.isEmpty || modName.isEmpty || modName == newtypeChannelTag then reject
      else { m with datas := m.datas ++ [(t, modName)] }
    | [t, tag, u] =>
      if t.isEmpty || u.isEmpty || tag != newtypeChannelTag then reject
      else { m with newtypes := m.newtypes ++ [(t, u)] }
    | _ => reject
  -- Dedup FIRST: the same (name, underlying) pair from two modules says the same
  -- thing, so it must not count as a conflict below.
  let nts := raw.newtypes.eraseDups
  let clashing := (nts.filterMap fun (n, u) =>
    if raw.datas.any (·.1 == n) || nts.any (fun (n', u') => n' == n && u' != u)
    then some n else none).eraseDups
  if clashing.isEmpty then { raw with newtypes := nts } else
  { raw with
    datas     := raw.datas.filter fun (t, _) => !clashing.contains t
    newtypes  := nts.filter       fun (t, _) => !clashing.contains t
    ambiguous := clashing }

/-! ### Local-vs-imported type-name collisions (Program validation)

`parseExtManifest` above can only see manifest-vs-manifest clashes. The module
that DECLARES the second same-named type is invisible there, because its own
newtype sidecar is appended to the manifest only AFTER it emits (`transpile.sh`),
and its `data` self-entries are indistinguishable from an import at that point.
That leaves a silent-wrong hole, proven end-to-end on the pre-fix binary:

    NtSA: newtype Tag = Tag Int
    NtSC: import qualified NtSA;  newtype Tag = Tag [Int]
          foreignTag :: NtSA.Tag -> NtSA.Tag   -- i.e. Int -> Int

`NtSC` transpiled with exit 0 and EMPTY stderr, emitting
`def foreignTag (t : (List Int)) : (List Int)` for an `Int -> Int` function, and
`theorem foreignTag_nil : foreignTag [] = [] := by blaster` reported `✅ Valid` —
a verdict about the empty list for a function on integers.

The root cause is not the ordering, and shadowing cannot be tuned to fix it: the
Core dump records type references UNQUALIFIED. `NtSA.Tag` arrives in NtSC's dump
as `{"name": "Tag", "tag": "TyCon"}`, byte-identical to a reference to NtSC's own
`Tag`. Whatever the pipeline picks, it is picking blind. So the only sound
behaviour is a loud refusal, and this is the function that detects it.

BOTH local kinds and BOTH manifest channels are in scope, because all four
pairings resolve blind and all four can typecheck afterwards:

* local `newtype` / imported `newtype` — pass 1 skips erasable newtypes, so the
  needle survives to pass 2, where `newtypeSubsts local ++ extNts` makes the
  LOCAL underlying win. The probe above.
* local `data` / imported `newtype` — pass 1 consumes the needle into a bare
  local name BEFORE pass 2 runs, so the imported reference silently becomes the
  local inductive and the manifest's erasure never fires.
* local `data` / imported `data`, and local `newtype` / imported `data` — same
  two mechanisms, with the imported type's `M.T` qualification (pass 4) never
  reached because pass 1 or 2 already consumed the needle.

DELIBERATE CONSERVATISM, recorded rather than fixed: the manifest is GRAPH-wide,
not import-scoped, so two graph modules that share a type name without importing
one another are refused too, even though neither is actually mis-resolved (each
one's pass 1 makes its own name bare). Refusing is over-strict there, but it is
LOUD and the remedy is the same rename; the alternative would be reconstructing
import edges the manifest does not carry. -/

/-- Local type names that ALSO name a type reachable through the module graph —
    the collision the unqualified Core dump makes unresolvable (see the section
    header). Order follows the local decl order; a name present in both manifest
    channels is reported once.

    `importedNames` is the manifest's name set: the DATA channel, the `newtype`
    channel, and the names `parseExtManifest` DROPPED as ambiguous. The dropped
    ones must be included — dropping only removes the entries, so a local decl of
    that name would resolve the reference blind and silently, instead of leaving
    the opaque needle that makes a dropped entry loud at `lake build`.

    The caller is responsible for excluding this module's OWN data-channel
    self-entries (`Type⇥ThisModule`, which `scripts/transpile_graph.py manifest`
    emits for every graph module including the one being transpiled). They are not
    collisions and are harmless — pass 1 makes the local name bare before pass 4
    could qualify it — and not filtering them would refuse every module that
    declares a `data` type. -/
def localImportCollisions (decls : List DataDecl) (importedNames : List Name) : List Name :=
  (decls.map (·.name) |>.filter importedNames.contains).eraseDups

/-- The refusal message for one `localImportCollisions` name: both origins, the
    root cause, and the remedy. Deliberately does NOT report which kind (`data` or
    `newtype`) either side is: the point is that the dump cannot tell the two
    REFERENCES apart, and naming a kind would invite the reader to believe some
    combination is safe. -/
def localImportCollisionError (n : Name) : String :=
  s!"type name collision: `{n}` is declared locally and imported from the module\n" ++
  s!"  graph. The Core dump records type references unqualified — an imported\n" ++
  s!"  `{n}` arrives spelled exactly like this module's own `{n}` — so the\n" ++
  s!"  transpiler cannot distinguish them and would resolve every reference to\n" ++
  s!"  whichever type it happened to try first. That typechecks and is silently\n" ++
  s!"  wrong (a function over the imported `{n}` emits with the local `{n}`'s\n" ++
  s!"  representation, theorem text included), so transpilation is refused.\n" ++
  s!"  Remedy: rename one of the types."

/-- Rewrite `(GHCCore.tyConOpaque "T")` → `M.T` for each external type `T`
    declared in a transpiled dependency module `M` (the manifest's DATA channel,
    built from the dependency `.decls.json`). Applied after `resolveUserTypes`,
    so locally-declared types are already bare; only imported types are
    rewritten, and genuinely unknown types stay opaque.

    Imported NEWTYPES never reach here: they have no `M.T` image and are erased
    one pass earlier (pass 2) from the manifest's separate `newtype` channel. -/
def resolveExternalTypes (extTypes : List (String × String)) (src : String) : String :=
  extTypes.foldl (init := src) fun s (tyName, modName) =>
    let needle      := s!"(GHCCore.tyConOpaque \"{tyName}\")"
    let replacement := s!"{modName}.{sanitize tyName}"
    s.replace needle replacement

/-- Every type-constructor name mentioned anywhere in a type. -/
private partial def tyConNames : GHCType → List Name
  | .tyCon n args => n :: args.flatMap tyConNames
  | .tyApp f a    => tyConNames f ++ tyConNames a
  | .tyFun a b    => tyConNames a ++ tyConNames b
  | .forAll _ b   => tyConNames b
  | .tyVar _      => []
  | .tyLit _      => []

/-- Locally-declared types that a decl's constructor fields refer to, deduplicated
    in first-occurrence order (self-references dropped: `data T = C T` needs no
    ordering, Lean inductives are self-recursive by construction). Consumers only
    test membership, but two fields of the same type — `data L = L Point Point` —
    would otherwise report `Point` twice. -/
def dataDeclDeps (localNames : List Name) (d : DataDecl) : List Name :=
  let mentioned := d.ctors.flatMap fun c => c.fields.flatMap fun f => tyConNames f.ty
  dedup (mentioned.filter fun n => n != d.name && localNames.contains n)

/-- Order data decls so that a decl using another local type as a field type is
    emitted AFTER it. Lean has no forward references and the decl-plugin's
    `tcg_tcs` dump order is not dependency order, so `inductive Rect` would
    otherwise reference a not-yet-declared `Point`.

    CONSTRAINT: the result is always exactly the input decls, reordered. Elements
    only move from `pending` to `acc` and never duplicate, so a preserved length
    implies a permutation; the closing length check is the totality fallback for
    the one input GHC cannot emit — two decls sharing a name, where
    `pending.filter (·.name != d.name)` drops both while placing one. On a
    dependency CYCLE (mutually recursive records, which would need a Lean
    `mutual` block) the remaining decls are appended in dump order. Either way
    Lean fails loud on a forward reference instead of a decl silently vanishing.

    The `| 0, pending` arm is DEAD: `go` starts at `fuel = ds.length` and every
    step consumes one fuel while removing one decl from `pending`, so `pending`
    empties first. It exists only to satisfy the termination checker. -/
def sortDataDecls (ds : List DataDecl) : List DataDecl :=
  let names := ds.map (·.name)
  let rec go (fuel : Nat) (pending : List DataDecl) (placed : List Name)
      (acc : List DataDecl) : List DataDecl :=
    match fuel, pending with
    | _, []            => acc.reverse
    | 0, pending       => acc.reverse ++ pending
    | fuel + 1, pending =>
      match pending.find? (fun d => (dataDeclDeps names d).all (fun n => placed.contains n)) with
      | some d => go fuel (pending.filter (·.name != d.name)) (d.name :: placed) (d :: acc)
      | none   => acc.reverse ++ pending
  let result := go ds.length ds [] []
  -- Totality fallback: any length change ⇒ hand back the input untouched.
  if result.length != ds.length then ds else result

/-- Apply the same name-resolution post-passes used on emitted bodies to a
    single user spec string: local types → bare, newtypes → underlying, imported
    types → `M.T`, user ctors → `T.C`.

    Only the transpiler-emitted OPAQUE spelling of a newtype erases here; a user
    spec that writes the newtype's name by hand (`∀ (a : Age)`) is left alone and
    fails loud (unknown identifier) — newtype properties are written against the
    underlying type.

    `extNts` is the manifest's `newtype` channel (imported newtypes); local
    newtypes come FIRST in the substitution list, so a local decl shadows an
    imported entry of the same bare name. -/
def resolveSpecText (typeDecls : List DataDecl) (extTypes : List (String × String))
    (s : String) (extNts : List (Name × String) := []) : String :=
  let kept := keptTypeDecls typeDecls
  resolveExternalTypes extTypes
    (resolveUserCtors kept
      (resolveNewtypes (newtypeSubsts typeDecls ++ extNts) (resolveUserTypes kept s)))

/-- Top-level entry: emit a full Program (data decls, value defs, instances).
    Name resolution runs as the pipeline documented under "Name-resolution
    post-passes" above: the TYPE pass (`resolveUserTypes`) runs on ALL sections —
    bodies/instances, the data block, and user spec text (via `resolveSpecText`)
    — because a local type used as another decl's FIELD type arrives opaque in the
    data block exactly as it does in a body. The CTOR pass (`resolveUserCtors`)
    runs on bodies and spec text ONLY, never the data block, where it would
    corrupt the inductive's own `| Ctor ` lines. The NEWTYPE pass
    (`resolveNewtypes`) runs between them on both sections; newtypes emit no decl
    at all. `extTypes` maps imported type names to their defining module so
    cross-module references resolve; `extNts` maps imported NEWTYPES to their
    underlying type (the manifest's two channels — see its section header). -/
def emitFullProgram (extTypes : List (String × String)) (p : Program)
    (extNts : List (Name × String) := []) : String :=
  -- Newtypes have no Lean image: they are erased at the type level (pass 2) and
  -- suppressed from every decl/ctor site. `kept` is the single suppression key.
  let kept := keptTypeDecls p.typeDecls
  -- LOCAL newtypes first: `resolveNewtypes` folds left and the needle is consumed
  -- by the first entry that matches, so a local decl shadows an imported entry of
  -- the same bare name (the manifest's keys are unqualified).
  let nts  := newtypeSubsts p.typeDecls ++ extNts
  -- User-declared ctors (e.g. `CustomRatio`) participate in the top-name
  -- set so App-position refs to them emit bare, not as `Name_<unique>`.
  -- A newtype ctor is NOT in this set: at pass-0000 it never reaches the emitter
  -- (M2 Task 3's positional census: 0 Var/DataAlt occurrences), and if a future
  -- compiler ever emits one, `Age_<unique>` / `| Age …` is an unknown identifier
  -- — loud, never a silent identity.
  let ctorNames : List Name :=
    kept.flatMap fun d => d.ctors.map (·.name)
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
  let keptBinds : CoreProgram := filterBinds (fun v _ => !isSuppressedMethod v) p.binds
  -- User classes → class decls + method→class map (selector rewrite). The decl
  -- plugin's shapes win over the instance-driven reconstruction (see
  -- `mergeClassDecls`); the map stays reconstruction-only, since it is keyed by
  -- the `$c` binds that only an instance provides.
  --
  -- `attachMethodShadows` over `keptBinds` — the binds actually emitted below —
  -- is what stops a LOCAL BINDER named like a method from being rewritten into
  -- the method (see `MethodRef`). The ambiguity that the bare key cannot resolve
  -- at all is refused up in `Main.lean` (`sameMethodAmbiguities`), before here.
  let (coreClasses, methodMapRaw) := reconstructClasses p.binds p.instances
  let methodMap := attachMethodShadows keptBinds methodMapRaw
  let userClasses := mergeClassDecls p.classDecls coreClasses
  let classNames := userClasses.map (·.name)
  -- Dependency order: a decl with another local type as a field type must come
  -- after it (Lean has no forward references; the dump order is not topological).
  -- Newtypes stay in the SORT's input — chains thread through them transitively
  -- (`Point` → `Wrapper`(newtype) → `Q`), and filtering first loses the edge —
  -- and are dropped only here, at the emission map.
  let datas := ((sortDataDecls p.typeDecls).filter fun d =>
      kept.any (·.name == d.name)).map fun d =>
    let hs := emitType (.tyCon d.name [])
    emitDataDecl (derivedEq.contains hs) (ordTypes.contains hs) d
  -- Default methods: the class body carries the `:=` defaults translated from
  -- GHC's `$dm<method>` binds, and `defaults` is THE key that also suppresses
  -- those binds and their instance-side wrappers below (see the "Default
  -- methods" section header). Computed from `p.binds`, the same list
  -- `emitInstance`'s `findClassMethodBind` searches, so the two cannot disagree
  -- about which binds exist.
  --
  -- The default BODY is emitted against the same top-name set as the user binds,
  -- so a reference to a top-level function emits bare — and, since the class
  -- block precedes every def, is then a loud forward reference. Only sibling
  -- methods (bare, via `MethodRef.bare`), builtins and locals are safe there.
  let defaults   := translatedDefaults p.binds userClasses
  let defaultTop := ctorNames ++ collectTopNames keptBinds
  let classDecls := userClasses.map fun c =>
    let ds := (defaults.filter (·.1 == c.name)).filterMap fun (_, m) =>
      (classDefaultBody methodMap defaultTop p.binds c m).map (fun body => (m, body))
    emitClassDecl ds c
  -- Partition kept binds for forward-visibility-safe ordering. Drop instance
  -- dict-builders (`$f…`) and Typeable junk; `$c…` method defs precede the
  -- instances (which reference them) which precede user binds (which use the
  -- instances). Classes go in the data block (before everything).
  --
  -- PER PAIR (`filterBinds`), never by a Rec group's head binder: GHC groups an
  -- instance's dict-builder with the method binds that need its dictionary, so
  -- head-name classification dropped or emitted the wrong half of a group — see
  -- `filterBinds` for both observed directions.
  let isJunkName (n : Name) : Bool :=
    n.startsWith "$f" || n.startsWith "$tc" || n.startsWith "$tr" || n.startsWith "$kr"
  -- A `$dm` bind whose body is now the class-body default has no second Lean
  -- image, and neither has a `$c` bind that is only GHC's wrapper around such a
  -- default (the instance omits that field instead — `classifyInstanceMethod`).
  let isTranslatedDm (n : Name) : Bool := defaults.any (fun (_, m) => "$dm" ++ m == n)
  let isWrapperBind (v : Var) (e : Expr) : Bool :=
    v.name.startsWith "$c" &&
      (let m := v.name.drop 2
       defaults.any (fun (_, dm) => dm == m) && isDefaultWrapperBody m e)
  let methodDefs := filterBinds
    (fun v e => v.name.startsWith "$c" && !isWrapperBind v e) keptBinds
  let userBinds  := filterBinds
    (fun v _ => !v.name.startsWith "$c" && !isJunkName v.name && !isTranslatedDm v.name)
    keptBinds
  let methodStr := emitProgramWith methodMap classNames methodDefs ctorNames
  let userStr   := emitProgramWith methodMap classNames userBinds ctorNames
  let insts := p.instances.filterMap (emitInstance defaults userClasses derivedEq p.binds)
  let instStr := String.intercalate "\n\n" insts
  let bodyRaw := String.intercalate "\n\n" (List.filter (· != "") [methodStr, instStr, userStr])
  let bodyResolved := resolveUserTypes kept bodyRaw
                    |> resolveNewtypes nts
                    |> resolveUserCtors kept
  -- `resolveUserTypes` (opaque → bare) must run on the data block too: a local
  -- type used as another decl's FIELD type arrives as
  -- `(GHCCore.tyConOpaque "Point")` there, exactly as in a body. Only the
  -- *type* pass runs here — `resolveUserCtors` would rewrite the `| Ctor `
  -- lines of the inductive itself.
  let dataBlock :=
    resolveNewtypes nts
      (resolveUserTypes kept
        (String.intercalate "\n\n" (List.filter (· != "") (datas ++ classDecls))))
  let sections := List.filter (· != "") [dataBlock, bodyResolved]
  -- External-type resolution runs over the whole output (data fields included).
  -- It is safe because `resolveUserTypes` has already made every LOCAL type bare
  -- in every section (data block included), so the opaque needle can only match
  -- an imported type. Note the shared manifest does carry the current module's
  -- own types (`Point → RecordOps`); those entries are dead for exactly that
  -- reason — before the data block was resolved they fired here and emitted a
  -- self-qualified `RecordOps.Point` field type.
  resolveExternalTypes extTypes (String.intercalate "\n\n" sections)

end GHCCore.Emit
