import GhcCoreToLean.AST
import GhcCoreToLean.Maps
-- `Lower` is imported for ONE thing: `eqHoistHeads`'s detection and
-- `retargetSelfEq`'s rewrite both need the PRE-`Lower` body (the type application
-- `Lower` erases is the only exact record of a class op's dispatch type), and the
-- rewritten body then has to be lowered before it can be emitted. No cycle —
-- `Lower` imports only `AST` and `Maps`.
import GhcCoreToLean.Lower

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

/-- GHC class-method bindings are named `$c<op>` (e.g. `$c==`). With more than
    one instance of a class these collide after sanitization, so we suffix them
    with their unique (like a local). -/
def isClassMethodName (n : Name) : Bool := n.startsWith "$c"

/-- For a Var reference: bare name if it's a known top-level binding,
    `<name>_<unique>` otherwise. Top-level names are resolved against
    a set of names collected from the program.

    A `$c<op>` name is EXEMPT from the top-level arm, because `defNameId` spells
    those with their unique (`isClassMethodName`) — so the bare arm would emit
    `_dollar_ccompare` for a def actually named `_dollar_ccompare_2966`. The two
    functions used to disagree, and the disagreement became reachable when M3
    Task 6's `Ord` section started passing the WHOLE program's top-name set (so a
    `$c` bind could reference a user top-level function by its bare name); before
    that, `$c` names were in `top` too, but no emitted body referenced one. -/
def refId (topNames : List Name) (v : Var) : String :=
  if topNames.contains v.name && !isClassMethodName v.name then sanitize v.name
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

/-! ## Literal emission

    STRING AND CHAR LITERAL ESCAPING (M4 Task 2). Both payloads used to be
    interpolated RAW, which was harmless only while the shim discarded them and
    every string arrived as the placeholder `<bs>`. With real bytes flowing, a
    literal containing `"` or a newline emits unparseable Lean: MEASURED on
    `quoted = "say \"hi\"\n"`, whose emitted `("say "hi"\n")` was a SYNTAX error
    (`16:43: unexpected identifier; expected ')', ',' or ':'`) that fired
    *instead of* the unknown-identifier error the mapping was supposed to produce
    — see the `M4 Task 1` block in `Tests/Unit.lean`.

    ESCAPING, NOT `Char.ofNat`. The alternative was to sidestep quoting by
    emitting char literals as `Char.ofNat n`. Rejected because it buys nothing:
    `emitLiteralPattern` must emit a real char literal (`Char.ofNat n` is not a
    pattern — Lean answers "Invalid pattern: Expected a constructor or constant
    marked with `[match_pattern]`"), so an escaper is needed for the pattern
    position regardless, and having two different spellings of a `Char` literal
    depending on position is strictly worse than one.

    WHAT IS ESCAPED, and what deliberately is not: the two quotes, the backslash,
    and the C0 control characters (`\n`/`\t`/`\r` by name, the rest as `\xNN`) —
    all verified accepted by the v4.24 parser in BOTH literal positions. Non-ASCII
    is emitted RAW: the generated file is UTF-8, `'é'`/`'💩'` are valid Lean
    literals, and `\uXXXX` cannot spell a non-BMP character anyway. That also
    settles Task 1's handoff about a U+FFFD "arriving from a non-UTF-8 literal":
    post-refusal (see `unrepresentableStringLiterals`) a U+FFFD in an emitted
    literal is always a genuine user U+FFFD, and it emits raw like any other
    non-ASCII character. -/

/-- One character, escaped for a Lean string or char literal. Both quotes are
    escaped in both positions: `\"` and `\'` are accepted inside either literal
    form, so one escaper serves both and there is no position-dependent variant to
    get wrong. -/
private def escapeLitChar (c : Char) : String :=
  match c with
  | '\\' => "\\\\"
  | '"'  => "\\\""
  | '\'' => "\\'"
  | '\n' => "\\n"
  | '\t' => "\\t"
  | '\r' => "\\r"
  | c    =>
    let n := c.toNat
    if n < 0x20 || n == 0x7F then
      let hex := (Nat.toDigits 16 n).asString
      s!"\\x{if hex.length == 1 then "0" ++ hex else hex}"
    else String.singleton c

/-- A Lean string literal (quotes included) for `s`. -/
def escapeStringLit (s : String) : String :=
  "\"" ++ s.foldl (fun acc c => acc ++ escapeLitChar c) "" ++ "\""

/-- A Lean char literal (quotes included) for `c`. -/
def escapeCharLit (c : Char) : String :=
  "'" ++ escapeLitChar c ++ "'"

def emitLiteral : Literal → String
  | .litInt n    => s!"({n} : Int)"
  | .litWord n   => s!"({n} : Nat)"
  | .litFloat f  => s!"({f} : Float)"
  | .litDouble f => s!"({f} : Float)"
  | .litString s => escapeStringLit s
  -- Unreachable in a module that emits at all: `Main.lean` refuses the program
  -- before emission (`unrepresentableStringLiterals`). Kept LOUD rather than
  -- plausible — an undefined identifier — so that a future caller who emits
  -- without running the refusal gets a `lake build` failure naming the bytes
  -- instead of a silently-wrong string.
  | .litStringUnrepresentable hex => s!"(GHCCore.unrepresentableStringLiteral \"{hex}\")"
  | .litChar c   => escapeCharLit c
  | .litLabel l  => s!"GHCCore.foreignLabel \"{l}\""

/-- Literal in PATTERN position (a `LitAlt` alternative).

    THE `.litString` ARM FAILS LOUD, and that is a change of kind, not of text. A
    Haskell string literal is a `[Char]`, so against the `List Char` scrutinee
    that `unpackCString#` now produces, `"hi"` is a type error at best; before
    this task it emitted a `String` pattern that could only ever be ill-typed.

    IS `LitAlt (MachStr …)` REACHABLE? Not from a string pattern in ordinary
    Haskell: GHC's `tidyLitPat` expands a SHORT `HsString` pattern into a
    cons-chain of `Char` patterns and routes a long one through `eqString`, so
    `case s of "hi" -> …` never becomes a literal alternative. But `hsLitKey` maps
    `HsStringPrim` (an `Addr#` literal pattern) to `LitString`, and `matchLiterals`
    builds `LitAlt` from `hsLitKey`. REVIEW CORRECTION: the `MagicHash` route
    this comment used to name is NOT reachable — GHC 9.2.7 rejects both
    `f "hi"# = 1` and `case a of "hi"# -> 1` in the front end, before Core
    (`error: Illegal unboxed string literal in pattern: "hi"#`, measured). The
    `hsLitKey` mapping still exists and TH-generated patterns / other front ends
    were not probed, so the arm is dead-but-unproven rather than ruled out.
    Measured negatively: `LitChar` ×0 and
    zero value-position `LitString` in any of 35 dumps, i.e. the arm is entirely
    unobserved either way. Under "cannot rule it out ⇒ fail loud" it emits an
    undefined pattern head, which Lean rejects with "Invalid pattern: Expected a
    constructor or constant marked with `[match_pattern]`" (verified).

    `.litChar` in pattern position is fine and stays a real literal: `'c'` against
    a `Char` scrutinee is exactly right. -/
def emitLiteralPattern : Literal → String
  | .litInt n    => toString n
  | .litWord n   => toString n
  | .litFloat f  => toString f
  | .litDouble f => toString f
  | .litString s => s!"(GHCCore.unsupportedStringPattern {escapeStringLit s})"
  | .litStringUnrepresentable hex => s!"(GHCCore.unrepresentableStringLiteral \"{hex}\")"
  | .litChar c   => escapeCharLit c
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
    * `C ∈ classNames` — a class the transpiler emits itself → `[C t]`, PRECEDED
      by `superBinders`' entry for `C` if it has one: the binder templates of
      `C`'s transitive BUILTIN superclasses (`classSuperBinders`; M3 Task 5).
      `class Ord a => Capped a` ⇒ `Capped a =>` peels to
      `[Ord t] [LT t] … [BEq t] [Capped t]`, because the emitted Lean `class
      Capped` does NOT carry the builtin parent (see `emitClassDecl`) and a body
      constrained only by `Capped a` may still use the parent's operators.
    * `Maps.classConMap C` — a BUILTIN class with a Lean image → that map's
      binder templates, `{t}` filled in (`Eq a =>` ⇒ `[BEq t]`).
    * `C ∈ classNames` applied to TWO OR MORE bare type variables (M3 Task 7) →
      `[C a b]`, in its own arm further down with its own restrictions (no
      `superBinders`, no `classConMap`) — see there.
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
partial def stripClassConstraintsGo (classNames : List Name)
    (superBinders : List (Name × List String)) : GHCType → List String × GHCType
  | .forAll _ b => stripClassConstraintsGo classNames superBinders b
  | .tyFun (.tyCon c [.tyVar t]) r =>
    let fill (ts : List String) : List String := ts.map (·.replace "{t}" (tyVarId t))
    let binders : Option (List String) :=
      if classNames.contains c then
        -- Builtin-superclass binders FIRST: they are what the class itself cannot
        -- carry, and `[C t]` never depends on them (the emitted class takes no
        -- instance-implicit parameters), so the order is for readability only.
        some (fill ((superBinders.find? (·.1 == c)).map (·.2) |>.getD [])
                ++ [s!"[{sanitize c} {tyVarId t}]"])
      else (Maps.classConMap c).map fill
    match binders with
    | some bs =>
      let (cs, rest) := stripClassConstraintsGo classNames superBinders r
      (bs ++ cs, rest)
    | none => ([], .tyFun (.tyCon c [.tyVar t]) r)
  -- MULTI-PARAMETER user-class constraint (M3 Task 7): `Convert a b => …` ⇒
  -- `[Convert a b]`. Deliberately a SEPARATE arm below the one-argument one,
  -- rather than an n-ary generalization of it, so that no single-parameter
  -- constraint can reach different code than it did before this arm existed —
  -- which is what makes the corpus byte-identity claim structural rather than
  -- merely measured. Everything the one-argument arm declines (`Eq [a]`,
  -- `Eq Int`, an ordinary `Int ->` value arrow) still lands here and is still
  -- declined, because both tests below fail for it.
  --
  -- Two deliberate NON-uses, each of which would be silent-wrong at two
  -- parameters:
  -- * `superBinders` is NOT consulted. Its templates carry a single `{t}` hole,
  --   and `supers` records parent NAMES only — which parameter a parent
  --   constrains is unrecoverable (`emitClassDecl`), so filling `{t}` with
  --   *some* parameter would emit a binder about the wrong one. The superclass
  --   of a multi-parameter class is dropped and REPORTED instead
  --   (`multiParamSupers`); `classSuperBinders` returns no entry for such a
  --   class, so this is belt-and-braces.
  -- * `Maps.classConMap` is NOT consulted. Every class it maps is
  --   single-parameter (`Eq`/`Ord`/`Num` in Haskell take one), so a two-argument
  --   head bearing one of those names is not that class and must not pick up its
  --   recipe.
  -- Only BARE type variables are peeled, as above: a partially-applied head like
  -- `Convert Int b` / `Convert a Int` stays loud rather than being peeled into a
  -- binder mentioning a type constructor.
  --
  -- NOT because the shape cannot arrive — an earlier version of this comment
  -- claimed "a monomorphic signature passes no dictionary", which is false; GHC
  -- does pass one. What GHC does is reject the signature without
  -- `FlexibleContexts`, and WITH the extension the shape reaches a dump:
  -- `convToF :: Convert a Fahrenheit => a -> Int` (MEASURED) emits the header
  -- `def convToF {t_v9102 : Type} (x_9111 : ((GHCCore.tyConOpaque "Convert")
  -- (t_v9102) (Fahrenheit.Fahrenheit))) : …`, i.e. the unpeeled constraint as the
  -- first value binder — and `GHCCore.tyConOpaque` is not a definition, so that
  -- file fails with `error: Unknown identifier `GHCCore.tyConOpaque`` (measured
  -- directly). LOUDNESS is the soundness argument for declining, not
  -- unreachability; the guards pin all three declined shapes.
  | .tyFun (.tyCon c args) r =>
    let tvs := args.filterMap fun a => match a with
      | .tyVar t => some (tyVarId t)
      | _        => none
    if args.length >= 2 && tvs.length == args.length && classNames.contains c then
      let (cs, rest) := stripClassConstraintsGo classNames superBinders r
      (s!"[{sanitize c} {String.intercalate " " tvs}]" :: cs, rest)
    else ([], .tyFun (.tyCon c args) r)
  | t => ([], t)

/-- `stripClassConstraintsGo` with the binder list deduplicated. An explicit
    `(Eq a, Ord a) => …` peels two constraints whose Lean images overlap (`Ord`'s
    set contains `[BEq t]`), and repeating an instance-implicit binder, while
    legal, is noise. First-occurrence order is preserved, so `LT` still precedes
    `DecidableLT`. Binders for DIFFERENT type variables are different strings and
    are never merged.

    `superBinders` is TRAILING and defaults to `[]` so that every pre-M3-Task-5
    caller (and every `#guard`) keeps its meaning: no entry for a class ⇒ exactly
    the old `[C t]`. -/
def stripClassConstraints (classNames : List Name) (t : GHCType)
    (superBinders : List (Name × List String) := []) : List String × GHCType :=
  let (cs, rest) := stripClassConstraintsGo classNames superBinders t
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

private def defNameId (v : Var) : String :=
  if isClassMethodName v.name then localId v else sanitize v.name

private def emitDefHeader (mm : List MethodRef) (classNames : List Name) (top : List Name)
                          (v : Var) (args : List Var)
                          (resTy : GHCType) (rhsBody : Expr) (rec? : Bool)
                          (superBinders : List (Name × List String) := []) : String :=
  let name     := defNameId v
  -- Strip class-constraint arrows (`C a =>`) from the signature → `[C a]`
  -- instance-implicit binders; the remaining type aligns with the term binders
  -- (the dict term-binder is already erased by Lower).
  let (constraints, strippedTy) := stripClassConstraints classNames v.ty superBinders
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

/-- `recOverride` replaces the `occursInExpr` verdict that decides whether a def
    gets `decreasing_by all_goals sorry`. Only the `Ord`/`Eq` blocks spliced into
    the data block pass it (`some false`), and only because a self-recursive
    `compare` is retargeted onto its OWN binder (`retargetSelfCompare`): that
    mention is not user recursion, and closing it with a `sorry` would put one
    inside an `Ord` instance and taint every `decide` proof about the order. Those
    bodies recurse on a constructor field of the scrutinee, which Lean takes as
    structural recursion; one it cannot take fails loud.

    It reaches the hoisted `$c==` blocks too, since they are spliced by the same
    code. So a RECURSIVE hand-written `Eq` that gets hoisted also loses the
    `decreasing_by all_goals sorry` it would get in the ordinary method section, and
    must pass structural recursion instead. Unmeasured (no probe has produced that
    shape), loud either way, and the direction is the one this project prefers: a
    real termination check rather than a `sorry` under an instance. -/
def emitBind (mm : List MethodRef) (classNames : List Name) (top : List Name) (b : Bind)
    (superBinders : List (Name × List String) := [])
    (recOverride : Option Bool := none) : String :=
  -- Result type is computed from the constraint-stripped signature so the
  -- erased dict arrow isn't mistaken for a value arg. `superBinders` is NOT
  -- threaded here: it only ever adds BINDERS, never changes the stripped type
  -- (`.2`), so the header and the result type cannot drift apart over it.
  let resTyOf (v : Var) (nargs : Nat) : GHCType :=
    stripFunTys nargs (stripClassConstraints classNames v.ty).2
  let recOf (v : Var) (e : Expr) : Bool :=
    recOverride.getD (occursInExpr v.name e)
  match b with
  | .nonRec v e =>
    let (args, body) := peelLams e
    let resTy        := resTyOf v args.length
    emitDefHeader mm classNames top v args resTy body (recOf v e) superBinders
  | .rec_ pairs =>
    match pairs with
    | [(v, e)] =>
      let (args, body) := peelLams e
      let resTy        := resTyOf v args.length
      emitDefHeader mm classNames top v args resTy body (recOf v e) superBinders
    | _        =>
      let defs := pairs.map fun (v, e) =>
        let (args, body) := peelLams e
        let resTy        := resTyOf v args.length
        emitDefHeader mm classNames top v args resTy body true superBinders
      let body := String.intercalate "\n" defs
      s!"mutual\n{body}\nend"

/-- Collect the names of every top-level binder in a program. -/
private def collectTopNames (p : CoreProgram) : List Name :=
  p.foldl (init := []) fun acc b => match b with
    | .nonRec v _ => v.name :: acc
    | .rec_ pairs => pairs.foldl (init := acc) fun acc (v, _) => v.name :: acc

def emitProgram (mm : List MethodRef) (classNames : List Name) (p : CoreProgram)
    (superBinders : List (Name × List String) := []) : String :=
  let top      := collectTopNames p
  let bindStrs := p.map (fun b => emitBind mm classNames top b superBinders)
  String.intercalate "\n\n" bindStrs

/-- Like `emitProgram`, but extends the "top-level names" set with extra
    names that should NOT get a `_unique` suffix when emitted as Var refs.
    The intended use is to splice in user-declared data constructors so
    `App (Var Foo) ...` becomes `Foo a b`, not `Foo_3490`. -/
def emitProgramWith (mm : List MethodRef) (classNames : List Name) (p : CoreProgram)
    (extraTopNames : List Name) (superBinders : List (Name × List String) := [])
    (recOverride : Option Bool := none) : String :=
  let top      := extraTopNames ++ collectTopNames p
  let bindStrs := p.map (fun b => emitBind mm classNames top b superBinders recOverride)
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

/-- The four instances Lean's `Ord` does NOT supply but the transpiler's lowered
    operators need: `decide (a ≤ b)` / `decide (a < b)` want `LE`/`LT` (Lean's are
    `Prop`-valued), and `Min.min`/`Max.max` want `Min`/`Max`. Core makes
    `leOfOrd`/`ltOfOrd`/`minOfLe`/`maxOfLe` plain `def`s, not instances, so every
    `Ord` the transpiler emits has to name them.

    ONE definition, two emission sites, deliberately: the data block for a DERIVED
    `Ord` (`emitDataDecl`) and the instance section for a HAND-WRITTEN one
    (`emitInstance`). Both derive all four FROM `compare`, which is what makes the
    order coherent by construction at every type this emitter produces (see the
    `M3 Task 3` block in `Tests/Unit.lean`) — and what makes a hand-written `$c<`/
    `$cmin` body unreachable; M3 Task 6 owns that call, argued at `ordRoute`. -/
def ordCompanionInsts (leanTy : String) : String :=
  s!"instance : LE {leanTy} := leOfOrd\ninstance : LT {leanTy} := ltOfOrd\n" ++
  s!"instance : Min {leanTy} := minOfLe\ninstance : Max {leanTy} := maxOfLe"

/-- Emit a Haskell `data T = …` declaration as a Lean `inductive`. Bare
    constructor uses are *not* brought into scope via `open T` — that makes
    `T` ambiguous between the type and the ctor in Lean's elaborator. The
    body post-passes rewrite Haskell-style refs to the qualified `T.C` form.
    Field selectors GHC auto-generates are emitted alongside as regular
    defs. -/
def emitDataDecl (derivedEq derivedOrd : Bool) (d : DataDecl)
    (handwrittenOrd : Bool := false) : String :=
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
  --
  -- `handwrittenOrd` (M3 Task 6) is the type whose `Ord` is the USER's, emitted as
  -- an `instance : Ord T where compare := …` block with the same four companions
  -- (`ordCompanionInsts`) — NOT here, because that block references a `$ccompare`
  -- def, which is SPLICED into the data block immediately after this `inductive`
  -- rather than emitted here. All this flag does here is `DecidableEq`,
  -- and it is Task 3's mandatory handoff rather than a convenience: the `Ord`
  -- constraint recipe contains `[BEq t]`, so an `Ord`-constrained call at such a
  -- type needs SOME `BEq` route. `deriving Ord` used to supply it via this same
  -- `DecidableEq`; with the derived order gone the flag keeps it. A type that also
  -- has a hand-written `Eq` gets its explicit `instance : BEq T` as a second
  -- candidate, and the explicit one wins — measured, and pinned by the `M3T6R`
  -- `#guard`s in `Tests/Unit.lean` (the same measurement `M3T3R` made for a
  -- DERIVED `Ord`, redone with the order coming from an instance block).
  --
  -- "The explicit one wins" is about DECLARATION ORDER, not priority: among equal
  -- candidates Lean picks the last declared. So it held at every ordinary use site
  -- — those follow both instances — and FAILED inside the `$ccompare` def, which
  -- precedes the user's `BEq`. That was a silent-wrong (a cross-multiply `Eq` plus
  -- a `compare` testing `x == y` computed STRUCTURAL equality there, with no
  -- diagnostic), and it is closed by hoisting the user's `BEq` ahead of the compare
  -- def — `eqHoistHeads` in `emitFullProgram`. Dropping this `DecidableEq` would
  -- have been the wrong fix: it also supplies `Decidable (a = b)`, which `BEq` does
  -- not, and it is the only `BEq` route for a type with NO hand-written `Eq`.
  let derivs := "Repr, Inhabited"
    ++ (if derivedEq || derivedOrd || handwrittenOrd then ", DecidableEq" else "")
    ++ (if derivedOrd then ", Ord" else "")
  let ordInsts := if derivedOrd then s!"\n\n{ordCompanionInsts leanName}" else ""
  s!"inductive {leanName} where\n{body}\nderiving {derivs}{ordInsts}"

/-- Emit a user class as a Lean `class`, one `(v : Type)` binder per type
    parameter. Single-parameter classes — the only ones supported end-to-end —
    are unchanged from v1 (`class Sized (a : Type) where …`).

    SUPERCLASSES (M3 Task 5). `c.supers` splits by what the parent IS, and only
    the first half reaches the class header:

    * a USER class (`classNames.contains`) → `extends P {t}`, the Lean image of
      `class Sized a => Container a`. Lean then makes `Sized` reachable from a
      `[Container t]` binder, which is what `sizeViaContainer`'s `Sized.size`
      call site needs, and an instance of the child may OMIT the parent field
      entirely — Lean fills it from the parent instance in scope. Both PROBED,
      transcripts in the `M3 Task 5` block of `GhcCoreToLean/Tests/Unit.lean`.
    * a BUILTIN class (`Maps.classConMap`) → NOTHING here. Its binder recipe is
      injected at every CONSTRAINT SITE instead (`stripClassConstraints`'
      `superBinders`), because `Ord`'s recipe contains `DecidableLT`/`DecidableLE`
      — `def`s, not structures — which `extends` rejects outright (`error:
      expected structure`) and which do not compose as instance-implicit class
      FIELDS either (both probed). CONSEQUENCE, pinned: the emitted class does
      not record the builtin parent, so a class-body DEFAULT under such a class
      gets no `Ord` in scope (loud), and the emitted instance no longer re-checks
      the parent obligation Haskell imposed — weaker than Haskell, not wrong,
      since GHC already accepted the program.
    * anything else (an unmapped builtin like `Show`, an imported user class,
      the plugin's `_UnknownSuper`) → nothing, and `unmappedSupers` reports it.

    MULTI-PARAMETER classes (M3 Task 7) get NO `extends` at all, and this is a
    REFUSAL, not an oversight: `supers` carries names only (the plugin discards
    which parameter each constraint applies to — `GhcDeclDump.ppSuperPred`), so
    with two type variables there is nothing to apply the parent to but a guess.
    Extending the plugin dump with per-super argument types is the fix M4-or-later
    can make; guessing would be silent-wrong. MEASURED on
    `examples/haskell/MultiParam.hs` (`class Sized a => Convert a b` ⇒
    `"supers":["Sized"], "tyVars":["a","b"]`): every `Convert` instance still
    emits, `size` at a monomorphic head still works, and only a body reaching
    `size` THROUGH a `Convert a b` constraint is lost — `failed to synthesize`, at
    `lake build`. `multiParamSupers` reports the drop, which is the half that was
    missing: the emitted-class side was already silent about it, since
    `unmappedSupers` only looks at whether a parent HAS a Lean image.

    The rest of the class emits exactly as a single-parameter one does: one
    `(v : Type)` binder per entry of `tyVars` (plugin-sourced since Task 1) and
    the method types as the plugin renders them. This is SUPPORTED, not merely
    tolerated — `MultiParam.hs` pins `class Convert (a : Type) (b : Type) where
    conv : (a → b); convBack : (b → a)` end to end.

    THE REVERSE DIRECTION — a multi-parameter class as the PARENT of a
    single-parameter one — is dropped for the same reason, and `arities` is the
    fact that lets it be. `class Convert a b => C a` is indeed rejected by GHC
    (`Not in scope: type variable ‘b’`), but a superclass may mention the child's
    own class variable more than once, and GHC 9.2.7 ACCEPTS
    `class Convert a a => C a` — MEASURED, transcript in the `M3 Task 7` block of
    `Tests/Unit.lean`. `extends` can apply a parent to the child's ONE variable
    and no more, so with no arity check this emitted
    `class C (a : Type) extends Convert a where …` — a two-parameter class
    applied to one argument, which Lean rejects with `error: type expected, got
    (Convert a : Type → Type)`. Loud, but at `lake build` and about the generated
    file, with `rc=0` and ZERO bytes of stderr at the transpiler: the same
    silent-diagnostic gap Task 7 closed in the other direction.

    So `arities` — `(class name, type-parameter count)` for the classes of this
    module — filters `extends` down to parents that take exactly ONE parameter,
    and `multiParamParentSupers` reports the rest. A parent ABSENT from `arities`
    is assumed to take one, which is what makes the parameter's `[]` default
    reproduce the pre-fix output exactly (and keeps every `#guard` that predates
    it meaning what it meant). The two tests compose into ONE filter, so a class
    whose only user parent is multi-parameter drops the clause entirely rather
    than emitting `extends  where`.

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
      (`Sized.size`), and class decls are emitted in SUPERCLASS-DEPENDENCY order
      (`sortClassDecls`) — which orders a parent before its children but says
      nothing about two unrelated classes, so a default calling an unrelated
      class's method is still a forward reference whenever that class comes
      later: loud, not silent.

    `classNames` is TRAILING and defaults to `[]`, which reproduces the
    pre-Task-5 output exactly (no super is a "user class" ⇒ no `extends`), and so
    is `arities` (see above). -/
def emitClassDecl (defaults : List (Name × String)) (c : ClassDecl)
    (classNames : List Name := []) (arities : List (Name × Nat) := []) : String :=
  let methodLines := c.methods.map fun m =>
    let decl := s!"  {sanitize m.name} : {emitType m.ty}"
    match defaults.find? (·.1 == m.name) with
    | some (_, body) => s!"{decl} := {body}"
    | none           => decl
  let params := String.intercalate " " (c.tyVars.map fun tv => s!"({tyVarId tv} : Type)")
  let extends? :=
    match c.tyVars with
    | [tv] =>
      -- A parent absent from `arities` is assumed to take ONE parameter, which is
      -- what makes the `[]` default reproduce the pre-fix output exactly.
      let arityOf (p : Name) : Nat :=
        match arities.find? (fun (a : Name × Nat) => a.1 == p) with
        | some (_, k) => k
        | none        => 1
      -- ONE filter, both tests: a user class whose own arity is 1 (or unknown).
      -- Splitting them would let a class whose only user parent is
      -- multi-parameter reach the `else` branch and emit `extends  where`.
      let userSupers := c.supers.filter fun p => classNames.contains p && arityOf p == 1
      if userSupers.isEmpty then ""
      else " extends " ++ String.intercalate ", "
             (userSupers.map fun p => s!"{sanitize p} {tyVarId tv}")
    | _ => ""
  s!"class {sanitize c.name} {params}{extends?} where\n" ++
    String.intercalate "\n" methodLines

/-- `(class name, type-parameter count)` for a class set — `emitClassDecl`'s
    `arities` argument, and the same list `multiParamParentSupers` reads through
    its `classes`. Both derive from ONE class set at the call site (`emitProgram`'s
    `userClasses`), which is what makes the emitted `extends` and the diagnostic
    exact complements: a user parent is in the clause iff it is not reported. -/
def classArities (classes : List ClassDecl) : List (Name × Nat) :=
  classes.map fun c => (c.name, c.tyVars.length)

/-- Superclass NAMES of `c` that emission drops on the floor: neither a user
    class in `classNames` (→ `extends`) nor a builtin with a `Maps.classConMap`
    recipe (→ constraint-site binders). Reachable as: an unmapped builtin
    (`Show`, `Fractional`, `Enum`), an imported user class (cross-module user
    classes are not supported end-to-end — see `mergeClassDecls`), and the
    plugin's `_UnknownSuper` placeholder for a superclass predicate that is not a
    class constraint at all (`GhcDeclDump.ppSuperPred`).

    A WARNING, not a refusal (`Main.lean`), for the same reason as
    `unresolvedInstanceMethods`: the consequence is `failed to synthesize` at a
    use site, i.e. already loud at `lake build`, and refusing would newly reject
    modules that transpile today (a `Show`-superclassed class whose parent methods
    are never called still works).

    SINGLE-PARAMETER classes only, since M3 Task 7. On a multi-parameter class
    EVERY superclass is dropped whatever its Lean image would be, and this
    function's reason ("no Lean image") is then the wrong reason to report — so
    `multiParamSupers` reports all of them instead, with the right one, and this
    one stays silent rather than double-reporting the subset it happens to
    recognize. -/
def unmappedSupers (classNames : List Name) (c : ClassDecl) : List Name :=
  if c.tyVars.length != 1 then [] else
  c.supers.filter fun s =>
    !classNames.contains s && (Maps.classConMap s).isNone

/-- Superclass NAMES dropped because `c` takes more than one type parameter (M3
    Task 7) — ALL of them, whatever their Lean image would have been.
    `emitClassDecl` emits no `extends` for such a class and
    `classSuperBinders` gives it no constraint-site binders, both because the
    plugin's `supers` channel records parent NAMES without saying which parameter
    each parent constrains (`GhcDeclDump.ppSuperPred`); see `emitClassDecl` for
    the full argument.

    Why this exists as its own diagnostic: before it, the drop was SILENT for
    exactly the parents that would otherwise have been emitted. A `Sized a =>
    Convert a b` produced `rc=0` and 0 bytes of stderr (measured on
    `examples/haskell/MultiParam.hs` before this task), because `unmappedSupers`
    asks only whether a parent has a Lean image and `Sized` — a locally declared
    class — has one. A WARNING rather than a refusal, on the same argument as
    `unmappedSupers`: the loss shows up as `failed to synthesize` at any use site
    that needs the parent through the child's constraint, and a module that never
    does that (like the fixture) is correct as emitted. -/
def multiParamSupers (c : ClassDecl) : List Name :=
  if c.tyVars.length == 1 then [] else c.supers

/-- Superclasses of a SINGLE-parameter class `c` dropped because the PARENT takes
    more than one type parameter — `(parent name, parent's parameter count)`.

    The other direction of `multiParamSupers`, and it took a review to notice it
    exists: `classSuperBinders`' docstring used to call this shape "not
    expressible in Haskell". `class Convert a b => C a` is rejected by GHC, but a
    superclass may mention the child's own class variable more than once and GHC
    9.2.7 ACCEPTS `class Convert a a => C a` (MEASURED — see `emitClassDecl` for
    the transcript and the emitted string it used to produce with `rc=0` and no
    stderr).

    `classes` is the module's class set, so `classes.find?` succeeding is exactly
    `classNames.contains` at `emitClassDecl`'s filter, and the arity test is the
    same one — the two are complements on one class set, never two.

    DISJOINT from both other superclass diagnostics by construction:
    `multiParamSupers` needs the CHILD to be multi-parameter (this one returns `[]`
    there), and `unmappedSupers` needs the parent to have no Lean image (this one
    only reports parents that ARE local classes, which have one). A WARNING, not a
    refusal, on the same argument as those two: what is lost is reaching the
    parent's methods through the child's constraint, which is `failed to
    synthesize` at `lake build`, and every other part of both classes still
    emits. -/
def multiParamParentSupers (classes : List ClassDecl) (c : ClassDecl)
    : List (Name × Nat) :=
  if c.tyVars.length != 1 then [] else
  c.supers.filterMap fun s =>
    match classes.find? (·.name == s) with
    | some parent => if parent.tyVars.length == 1 then none
                     else some (s, parent.tyVars.length)
    | none        => none

/-- A type-parameter count as English, for the two superclass warnings below.
    Neither LIVE call site can reach 1 — `multiParamSupers` fires only when the
    CHILD's arity is ≠ 1 and `multiParamParentSupers` only when the PARENT's is —
    so there is no singular case to render. (Both warnings are public `def`s, so a
    caller may pass anything; that is a `#guard`'s business, not this function's.)
    `0` is the whole point — `takes 0 type parameters`
    read as a bug in the transpiler rather than a fact about the class. Cosmetic
    only: the plugin channel dumps a class's real `classTyVars`, which is never
    empty, so a `0` here can come only from a hand-built `ClassDecl`. -/
private def paramCountPhrase (n : Nat) : String :=
  if n == 0 then "no type parameters" else s!"{n} type parameters"

/-- The warning for one `multiParamSupers` entry. -/
def multiParamSuperWarning (cls super : Name) (nparams : Nat) : String :=
  s!"class `{cls}` takes {paramCountPhrase nparams} and has the superclass `{super}`,\n" ++
  s!"  which is DROPPED from the emitted Lean class. The class-shape dump records a\n" ++
  s!"  superclass by NAME only, so with more than one parameter there is no fact\n" ++
  s!"  saying which parameter `{super}` constrains — `extends {super} ?` would be a\n" ++
  s!"  guess, and a wrong guess is silently wrong. The class itself, its methods and\n" ++
  s!"  its instances are emitted normally; what is lost is reaching `{super}`'s\n" ++
  s!"  methods THROUGH a `{cls}` constraint, which fails with `failed to synthesize\n" ++
  s!"  {super} …` at `lake build`. `{super}`'s methods at a concrete type are\n" ++
  s!"  unaffected.\n" ++
  s!"  Remedy: constrain the parent explicitly at each use site (`({super} a, {cls} a b) => …`),\n" ++
  s!"  or extend the decl plugin's `ppSuperPred` to dump each superclass's argument\n" ++
  s!"  types so the parameter can be identified."

/-- The warning for one `multiParamParentSupers` entry. Here the PARENT is the
    multi-parameter one and `nparams` is ITS count, so the remedy has to spell the
    parent's arguments out — `a` repeated `nparams` times, which is the shape GHC
    accepted in the first place. -/
def multiParamParentWarning (cls parent : Name) (nparams : Nat) : String :=
  let selfApp := String.intercalate " " (List.replicate nparams "a")
  s!"class `{cls}` takes one type parameter and has the superclass `{parent}`, which\n" ++
  s!"  takes {paramCountPhrase nparams} — so `{parent}` is DROPPED from the emitted Lean\n" ++
  s!"  class. Lean's `extends` applies a parent to the child's own type variable, i.e.\n" ++
  s!"  to ONE argument, and the class-shape dump records a superclass by NAME only\n" ++
  s!"  (`GhcDeclDump.ppSuperPred`). GHC accepts the declaration because the superclass\n" ++
  s!"  context's type variables are all `{cls}`'s own (`class {parent} {selfApp} => {cls} a`\n" ++
  s!"  is the simplest such shape), and which type each of `{parent}`'s parameters gets\n" ++
  s!"  is exactly what the dump drops. Emitting `extends {parent} a` anyway would leave\n" ++
  s!"  `{parent}` partially applied, which Lean rejects with `type expected, got\n" ++
  s!"  ({parent} a : Type → …)`. `{cls}` itself, its methods and its instances are\n" ++
  s!"  emitted normally; what is lost is reaching `{parent}`'s methods THROUGH a `{cls}`\n" ++
  s!"  constraint, which fails with `failed to synthesize {parent} …` at `lake build`.\n" ++
  s!"  Remedy: constrain the parent explicitly at each use site (`({parent} {selfApp}, {cls} a) => …`),\n" ++
  s!"  or extend the decl plugin's `ppSuperPred` to dump each superclass's argument\n" ++
  s!"  types so `extends {parent} {selfApp}` can be emitted."

/-- The warning for one `unmappedSupers` entry. -/
def unmappedSuperWarning (cls super : Name) : String :=
  s!"class `{cls}` has the superclass `{super}`, which is DROPPED from the emitted\n" ++
  s!"  Lean class: `{super}` is neither a class this module declares (which would\n" ++
  s!"  become `extends {super}`) nor a builtin with a binder recipe in\n" ++
  s!"  `Maps.classConMap` (which would be injected at each constraint site). A body\n" ++
  s!"  that uses `{super}`'s methods through a `{cls} a` constraint therefore fails\n" ++
  s!"  with `failed to synthesize {super} …` at `lake build`; `{cls}`'s own methods\n" ++
  s!"  are unaffected.\n" ++
  s!"  Likely causes: `{super}` is an unmapped builtin (`Show`, `Fractional`, …) —\n" ++
  s!"  add a `classConMap` entry; `{super}` is declared in another module (imported\n" ++
  s!"  user classes are not supported end-to-end); or the superclass is not a class\n" ++
  s!"  constraint at all (the plugin renders those as `_UnknownSuper`)."

/-- Builtin-superclass binder templates per user class, TRANSITIVELY, as
    `stripClassConstraints`' `superBinders`. `class Ord a => Capped a` ⇒
    `("Capped", ["[Ord {t}]", …, "[BEq {t}]"])`; a user parent contributes its own
    builtin-super binders, so `class Ord a => P a` + `class P a => C a` gives `C`
    the `Ord` recipe as well — the Lean `extends P a` chain reaches `P`, but `P`'s
    builtin parent lives only in constraint sites, so it has to be re-injected
    here or a `C a`-constrained body could not use `<`.

    Templates keep their `{t}` placeholder (substituted per constraint site) and
    are deduplicated in first-occurrence order, since `Ord`'s recipe already
    contains `[BEq {t}]` and two parents may overlap. The fuel is the class count:
    a superclass CYCLE is impossible in Haskell, so exhausting it means the class
    graph is malformed and the binders are simply truncated (loud at the use
    site), never looped.

    A MULTI-PARAMETER class contributes NOTHING and gets no entry, at any depth
    (M3 Task 7). A template's `{t}` is filled with the one type variable of the
    constraint site, and with two parameters there is no fact saying which of
    them the parent constrains (`supers` is names only), so any fill would be a
    guess about the wrong variable. Belt-and-braces: `stripClassConstraints`'
    multi-parameter arm does not read `superBinders` either. The drop is reported
    by `multiParamSupers`.

    The REVERSE direction — a multi-parameter class as the PARENT of a
    single-parameter one — IS expressible in Haskell, contrary to what this
    docstring claimed until a review measured it. `class Convert a b => C a` is
    rejected (`Not in scope: type variable ‘b’`), but a superclass may mention
    the child's own class variable more than once and GHC 9.2.7 accepts
    `class Convert a a => C a`. This function is safe there because `go` re-tests
    the arity of every class it DESCENDS into, not only the one it starts at: a
    single-parameter child whose parent takes two gets `[]` from the recursive
    call, so no `{t}` is ever filled from a parameter the child cannot see — even
    when that parent's own super has a recipe (`class Ord a => Convert a b`).
    `emitClassDecl` drops such a parent from `extends` on the same fact, and
    `multiParamParentSupers` reports it. -/
def classSuperBinders (classes : List ClassDecl) : List (Name × List String) :=
  let rec go (fuel : Nat) (c : ClassDecl) : List String :=
    match fuel with
    | 0      => []
    | fuel+1 =>
      if c.tyVars.length != 1 then [] else
      c.supers.flatMap fun s =>
        match Maps.classConMap s with
        | some recipe => recipe
        | none        =>
          match classes.find? (·.name == s) with
          | some parent => go fuel parent
          | none        => []
  let perClass := classes.map fun c =>
    let bs := go classes.length c
    (c.name, bs.foldl (init := ([] : List String))
               fun acc t => if acc.contains t then acc else acc ++ [t])
  perClass.filter fun (_, bs) => !bs.isEmpty

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
    `==`) never uses tag primops, so it keeps its body-translation.

    `Ord`'s counterpart is `ordRoute`, which since M3 Task 6 makes the SAME
    tag-primop test on `$ccompare` (it used to be instance-existence-based, which
    was silently wrong for a hand-written non-structural `Ord`). This comment used
    to say the test could not work for `Ord` "since a derived `compare` on a small
    enum is case-based and indistinguishable from a hand-written one" — the premise
    is CORRECT and measured (2-constructor enums and every constructor-with-fields
    shape are case-based), but the conclusion was wrong: such a body is
    TRANSLATABLE, and translating GHC's derived `compare` yields the derived order.
    See `ordRoute`'s section header for that argument and its exhaustive check. -/
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

/-- Look up a top-level binding by name, and by UNIQUE as well when the caller has
    one. Names alone are ambiguous in principle — GHC does not suffix `$c<method>`
    or `$f<Class><Ty>` names per instance, and `/tmp/transpile-Ratio.json` has two
    binds named `$c/=` distinguished only by unique — so a caller holding a unique
    should pass it. Callers with no unique (`translatedDefaults`/`classDefaultBody`
    on `$dm<method>`, `reconstructClasses`) pass `none` and keep the name-only
    behaviour exactly. -/
private def findBind (binds : CoreProgram) (n : Name) (u : Option Nat := none)
    : Option (Var × Expr) :=
  let hit (v : Var) : Bool := v.name == n && (u.all (· == v.unique))
  binds.findSome? fun b => match b with
    | .nonRec v e => if hit v then some (v, e) else none
    | .rec_ pairs => pairs.find? (fun (v, _) => hit v)

/-- `Instance.dfunUnique` translated into the CORE DUMP's unique numbering.

    THE TWO CHANNELS DO NOT NUMBER UNIQUES THE SAME WAY, and comparing them raw
    silently loses the match. MEASURED: `/tmp/transpile-SuperClass.json` carries
    `dfunName: "$fOrdLevel", dfunUnique: 8214565720323795259` while the bind named
    `$fOrdLevel` in the same file has `unique: 10555`. The instance channel is the
    decl plugin's `getKey (nameUnique …)` — GHC's packed 64-bit key, `(tag << 56)
    ||| index` (`shim/decl-plugin/GhcDeclDump.hs:141`) — whereas a bind's unique is
    the shim's `BinderId (Unique _ n) → n`, i.e. the INDEX alone
    (`shim/Main.hs:146-148`). Stripping the high byte reconciles them.

    VERIFIED over every instance in all 40 dumps in `/tmp/transpile-*.json`: 60/60
    instances have `dfunUnique % 2^56` equal to the unique of the bind with that
    dfun name, 0 mismatches, and the high byte is `114` (`'r'`) throughout. The same
    scan found 0 dumps with two top-level binds sharing a dfun name, which is why
    this is hardening rather than a fix — and why the one caller
    (`dfunMethodBinds`) falls back to the name-only lookup if the unique-keyed one
    comes up empty: if a future GHC or shim ever renumbers, that degrades to
    today's behaviour instead of dropping every instance. -/
def dfunDumpUnique (dfunKey : Nat) : Nat := dfunKey % 72057594037927936

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
    default-method wrapper is a property of its body (`isDefaultWrapperBody`).

    THE FALLBACK, since M3 Task 5. This matcher can only see methods whose type
    STARTS with the class parameter, so `empty :: a` and `insert :: Int -> a -> a`
    are invisible to it and their instance was dropped whole. `dfunMethodBinds`
    reads the attribution out of the instance's own dictionary instead and is
    tried first; this stays for the shapes that one declines (a dfun whose body is
    not a recognizable dictionary, a class the plugin channel has no shape for).

    NEVER THE FIRST OF SEVERAL, and that is the fix for a MEASURED silent-wrong.
    The key `(method, first-value-arg type)` does NOT mention the declaring CLASS,
    so a user class declaring an operator method whose instance head also carries
    the builtin instance of the class that declares the same operator gives TWO
    binds at one key, distinguishable only by unique. OBSERVED on
    `examples/haskell/UserClassEqWithEq.hs` (`class MyEq a where (==)` +
    `data R = R Int Int deriving Prelude.Eq`, needing NO `import Prelude hiding` —
    `/tmp/transpile-UserClassEqWithEq.json` has `$c==` at unique 2948 for `MyEq R`
    and 2931 for `Eq R`, both typed `R -> R -> Bool`), where `findSome?`'s first
    match handed the USER class's body (`a > c`) to `hwEqBindAt` and emitted

        instance : BEq R where
          beq := _dollar_c_eq__eq__2948        -- the USER class's body

    with the derived structural `_dollar_c_eq__eq__2931` emitted and never
    referenced. `structEq x y = x Prelude.== y` then computed the user's operator:
    `#eval` said `true` where Haskell says `False`, and
    `theorem … = false := by decide` reported "proved that the proposition … is
    false" — with `rc=0` and empty stderr from the transpiler.

    `none` HERE IS DEFENSE IN DEPTH, NOT THE DIAGNOSTIC. `Main.lean` refuses such
    a program before any emission (`ambiguousMethodBinds`), so this arm is
    unreachable in a run that emits; it exists so that no future caller — one
    reached on a path the Program-level check does not cover — can silently take a
    first match again. A reader must NOT read `none` as "no such bind": it means
    "no UNIQUE such bind". -/
private def findClassMethodBind (binds : CoreProgram) (method : Name) (headTyStr : String)
    : Option (Var × Expr) :=
  let matchesHead (v : Var) : Bool :=
    v.name == method &&
      (match firstValArgTy v.ty with
       | some t => emitType t == headTyStr
       | none   => false)
  let hits : List (Var × Expr) := binds.flatMap fun b => match b with
    | .nonRec v e => if matchesHead v then [(v, e)] else []
    | .rec_ pairs => pairs.filter (fun (v, _) => matchesHead v)
  match hits with
  | [hit] => some hit
  | _     => none

/-- Unwind an application spine into its head and its arguments, left to right.
    `f @T d x` ⇒ `(f, [Type T, Var d, Var x])`. -/
private partial def spineOf : Expr → Expr × List Expr
  | .app f a => let (h, as) := spineOf f; (h, as ++ [a])
  | e        => (e, [])

/-- The `$c<method>` bind for each of `cd`'s methods, read POSITIONALLY out of the
    instance's own dictionary — the attribution that fixes `SuperClass.hs`'s
    dropped `Container Bag`.

    A dfun body is one of exactly two observed shapes (`/tmp/transpile-SuperClass.
    json`, quoted in the `M3 Task 5` block of `GhcCoreToLean/Tests/Unit.lean`):

    * MULTI-field dictionary — `$fContainerBag = C:Container @Bag $fSizedBag
      $cempty $cinsert`. Head is the dictionary constructor `C:<Class>`; then type
      arguments, then one argument per SUPERCLASS dictionary (`role = dict`), then
      the methods in class order. Dropping `.type_` args and `dict`-role args
      leaves exactly the method list, and GHC's field order is `classOpItems`
      order — the same order the plugin's `methods` list is in.
    * SINGLE-method dictionary — `$fSizedBag = $csize`. A one-method, superclass-
      free class dictionary is a newtype over the method, so the dfun body IS the
      method reference, with no constructor and (at pass-0000) no cast.

    THE GUARD, and why it is name-based even though the pairing is positional:
    every paired arg must be named `$c` ++ the method's name. Order agreement
    between GHC's dict fields and `classOpItems` is an assumption about GHC's
    internals, and if it ever breaks, positional pairing alone would attribute
    `empty`'s body to `insert` — a SILENT wrong instance. With the guard, any
    disagreement (or an arg count mismatch) rejects the whole attribution, falls
    through to `findClassMethodBind`, and at worst drops the instance LOUDLY. It
    also costs nothing on the shapes we have: GHC does not suffix these names per
    instance (two instances of one class both bind `$c<method>`, disambiguated by
    unique — see `findClassMethodBind`), which is also why the bind lookup below
    matches on name AND unique: the name alone is ambiguous in exactly that case,
    and the spine hands us the right unique.

    Declines with `[]` when the spine shape or the name guard rejects the
    instance. It does NOT guarantee a total list: the final `filterMap` drops any
    method whose `$c` bind is absent from `binds` (verified: with `$cinsert`
    filtered out, this returns just `[("empty", …)]`). That partial case is safe
    because `emitInstanceUser` requires EVERY method to resolve, so a partial list
    drops the instance LOUDLY rather than mixing mechanisms per method. Kept
    non-`private` so `Tests/Unit.lean` can guard the decline arms directly. -/
def dfunMethodBinds (binds : CoreProgram) (cd : ClassDecl) (i : Instance)
    : List (Name × Var × Expr) :=
  let byNameUnique (v : Var) : Option (Var × Expr) :=
    binds.findSome? fun b =>
      let hit (w : Var) : Bool := w.name == v.name && w.unique == v.unique
      match b with
      | .nonRec w e => if hit w then some (w, e) else none
      | .rec_ pairs => pairs.find? (fun (w, _) => hit w)
  -- The dfun by NAME AND UNIQUE: the instance channel hands us both, and a dfun
  -- name is not guaranteed unique in a module. `dfunDumpUnique` is load-bearing —
  -- the two channels number uniques differently, and matching `i.dfunUnique` RAW
  -- resolved nothing, which dropped `SuperClass.hs`'s `Container Bag` instance
  -- (measured; see that function).
  --
  -- The `orElse` is a SILENT degradation to name-only matching, not a loud one:
  -- should the packed encoding drift, this falls back to the FIRST bind of that
  -- name with no diagnostic, and in a module with two instances whose dfuns share
  -- a name it would attribute the wrong one. That is the arm's whole purpose (a
  -- drifted encoding must not drop every instance), and the mask itself is
  -- verified rather than assumed — GHC masks the index at construction in
  -- `mkUnique`, and 65/65 instances across the dumps match with tag 114 — so the
  -- fallback is unreachable today. Making it loud is the improvement to make if it
  -- ever fires.
  match (findBind binds i.dfunName (some (dfunDumpUnique i.dfunUnique))).orElse
          (fun _ => findBind binds i.dfunName) with
  | none          => []
  | some (_, rhs) =>
    let (head, args) := spineOf rhs
    let methodVars : List Var :=
      match head with
      | .var hv =>
        if args.isEmpty then
          -- Newtype dictionary: the body IS the sole method.
          if hv.name.startsWith "$c" then [hv] else []
        else if hv.name.startsWith "C:" then
          args.filterMap fun a => match a with
            | .var av => if av.role == .dict then none else some av
            | _       => none
        else []
      | _ => []
    if methodVars.length != cd.methods.length then []
    else
      let paired := cd.methods.zip methodVars
      if paired.all (fun (m, v) => v.name == "$c" ++ m.name) then
        paired.filterMap fun (m, v) => (byNameUnique v).map (fun (w, e) => (m.name, w, e))
      else []

/-! ### Two `$c<method>` binds at one head (the ambiguous-attribution refusal)

Every bind lookup keyed on `(method name, first value-argument type)` —
`findClassMethodBind` and its `$ccompare` twin `findCompareBind` — is ambiguous
exactly when TWO classes declare a method of the same name and both have an
instance at one head. GHC does not suffix `$c<method>` names per instance, so the
two binds differ only by unique, and the key does not mention the class.

WHY THE TWO EXISTING GUARDS MISS IT, both measured. `sameMethodAmbiguities`
builds its class set from the plugin-dumped ∪ Core-reconstructed USER classes, so
a builtin `Eq`/`Ord` is not in it and the operator looks singly-declared.
`unmappedOperatorMethods` requires the method to be ABSENT from the method map,
and here it is present — the user class does have a surviving `$c` bind, it is
just not the one the `Eq` route picks up.

WHY THIS REFUSES RATHER THAN ATTRIBUTING CORRECTLY, which is the honest part.
The attribution IS available: an instance's own dictionary names its methods'
binds by unique (`dictMethodRefs`; `$fEqR = GHC.Classes.C:Eq @R $c==(2931)
$c/=(2940)` and `$fMyEqR = $c==(2948)` in the fixture dump), and the USER-class
side already uses it (`dfunMethodBinds`, tried before the head match, wires
`instance : MyEq R` correctly today). What is NOT available is correct EMISSION,
because the emitter reaches this key from FOUR independent head-only decision
points:

  * `findClassMethodBind` — the `Eq`/`Ord`/fallback bind lookup;
  * `findCompareBind` — a second, separate copy of the same first-value-argument
    match, feeding `ordRoute`'s derived-vs-hand-written decision;
  * `emitFullProgram`'s `isSuppressedMethod` — `headMatches` is name+head with no
    unique, so it suppresses or keeps BOTH colliding binds as a pair;
  * `derivedEqTypes` — a name+tag-primop scan, so a user-class `$c==` over an enum
    would put the head in `derivedEq` and take the real `Eq` out.

Threading uniques through some of those and not the rest does not remove the
wrong answer, it MOVES it to the un-threaded point — with no diagnostic, which is
the one failure mode this project forbids. `UserClassNeqWithEq.hs`'s header
already scoped that refactor as a follow-up needing `isSuppressedMethod` to stop
being name+head keyed. So the program is refused, loudly and by name, and the
refactor stays a separate change.

THE ONE EXEMPTION is a collision whose binds all belong to the SAME class: two
instances of one MULTI-PARAMETER class sharing a first head type (`instance
Convert Foo Bar` + `instance Convert Foo Baz` both give `$cconv` at `Foo`). That
is the shape `dfunMethodBinds` was built for and it attributes them positionally,
so nothing is guessed; the head match returns `none` and, if the dictionary ever
declines too, the instance drops LOUDLY through `unresolvedInstanceMethods`.
`MultiParam.hs` does not reach the exemption — its two instances are mirrored
(`Convert Celsius Fahrenheit`/`Convert Fahrenheit Celsius`), so the first
value-argument types already differ. -/

/-- Every `$c<method>` bind reference in instance `i`'s OWN dictionary, as
    `(bind name, unique)` — the channel that says which INSTANCE, and so which
    CLASS, a `$c` bind belongs to.

    Deliberately WEAKER than `dfunMethodBinds`, and for the case that one cannot
    serve: no `ClassDecl` is needed, nothing is paired positionally and no arity
    is checked, because the classes this has to attribute include the BUILTIN
    `Eq`/`Ord` — for which `reconstructClasses` and `mergeClassDecls` build no
    `ClassDecl` at all (both filter `builtinClasses`). It answers only "which
    `$c` names and uniques does this dictionary mention", which is all the
    ambiguity check needs.

    BOTH observed dfun shapes, same two as `dfunMethodBinds`: the multi-field
    dictionary constructor spine and the single-method newtype dictionary whose
    body IS the method reference. The dict-constructor test is NOT that function's
    `startsWith "C:"` — a locally declared class's constructor is bare
    (`C:Container`) but an IMPORTED one is module-qualified, and the dumps spell
    `Eq`'s `GHC.Classes.C:Eq`, i.e. exactly the case this function exists for.
    Reusing the bare-prefix test would have attributed nothing on the `Eq` side
    and made the check unable to tell a two-class collision from a one-class one.

    Declines with `[]` on an unrecognized shape or a missing dfun bind; the caller
    treats "not attributed" as "refuse", never as "same class". -/
private def dictMethodRefs (binds : CoreProgram) (i : Instance) : List (Name × Unique) :=
  let isDictCon (n : Name) : Bool := n.startsWith "C:" || (n.splitOn ".C:").length > 1
  -- Name AND masked unique, with the same name-only `orElse` degradation as
  -- `dfunMethodBinds` — see `dfunDumpUnique` for why the mask is load-bearing.
  match (findBind binds i.dfunName (some (dfunDumpUnique i.dfunUnique))).orElse
          (fun _ => findBind binds i.dfunName) with
  | none          => []
  | some (_, rhs) =>
    let (head, args) := spineOf rhs
    match head with
    | .var hv =>
      if args.isEmpty then
        (if hv.name.startsWith "$c" then [(hv.name, hv.unique)] else [])
      else if isDictCon hv.name then
        args.filterMap fun a => match a with
          | .var av => if av.name.startsWith "$c" then some (av.name, av.unique) else none
          | _       => none
      else []
    | _ => []

/-- Every `(bind name, source-spelled head, candidates)` where more than one
    `$c<method>` bind carries one instance head and they are not all one class's —
    the Program-level refusal wired to an `eprintln` in `Main.lean`. Each candidate
    is `(declaring class or "?" when the dictionary did not attribute it, emitted
    def name)`.

    KEYED EXACTLY LIKE THE LOOKUPS IT PROTECTS: `$c`-prefixed binder names, and
    `firstValArgTy`'s first value-argument type rendered by `emitType`. A method
    with no value argument at all (`$cempty : Bag`) has no key here and needs
    none — `findClassMethodBind`'s `matchesHead` is `false` for it too, so it can
    never be the bind that function confuses.

    ON `p.binds`, the post-filter post-`Lower` list, because that is the list
    `emitInstance`, `derivedEqTypes`, `ordRoute` and `dfunMethodBinds` all search;
    `p.rawBinds` carries the same binders (same filtering, only the erasure
    differs) and `emitFullProgram`'s `keptBinds` is a subset, so a refusal computed
    here covers every consumer. Being computed on the SUPERSET makes it
    conservative in the safe direction: a collision one of whose binds
    `isSuppressedMethod` would have dropped is refused here, where the message can
    name both classes, rather than emitted and left to `lake build` to report as an
    `unknown identifier` on a mangled `$c` def name.

    Post-`Main.lean`-filter is also what keeps `Ratio` out: its dump has
    `$cshowsPrec` twice at `Int` and `$cshowList` twice at `[]`, and
    `isDerivedShowMethod` drops all three `$cshow…` names before `userProg` exists
    (verified — `Ratio` is byte-identical across this change).

    Disjoint from `unmappedOperatorMethods` in both directions, which is why the
    two refusals can be ordered freely: that one fires when NO `$c` bind for the
    method survives, this one when TWO do. `UserClassNeqWithEq.hs` is the first
    case (`isEqNeqBind` drops both `$c/=` binds, so no key here has two
    candidates) and is still refused by that check, with its message unchanged. -/
def ambiguousMethodBinds (p : Program) : List (Name × Name × List (Name × String)) :=
  let cands : List (Var × String) := p.binds.flatMap fun b =>
    let one (v : Var) : List (Var × String) :=
      if !v.name.startsWith "$c" then [] else
      match firstValArgTy v.ty with
      | some t => [(v, emitType t)]
      | none   => []
    match b with
    | .nonRec v _ => one v
    | .rec_ ps    => ps.flatMap (fun (v, _) => one v)
  let owners : List ((Name × Unique) × Name) := p.instances.flatMap fun i =>
    (dictMethodRefs p.binds i).map fun r => (r, i.className)
  let ownerOf (v : Var) : Option Name :=
    (owners.find? (·.1 == (v.name, v.unique))).map (·.2)
  -- Source spelling for the message: `emitType`'s key is the pre-resolution
  -- `(GHCCore.tyConOpaque "R")` needle — the right thing to match binds with and
  -- the wrong thing to show a user. Same idiom as `ordForwardRefs`.
  let nameOfHead (h : String) : Name :=
    match p.typeDecls.find? (fun d => emitType (.tyCon d.name []) == h) with
    | some d => d.name
    | none   => h
  let keys := (cands.map (fun (v, h) => (v.name, h))).eraseDups
  keys.filterMap fun (nm, h) =>
    -- Deduplicated by UNIQUE, so a bind listed twice cannot fake a collision.
    let group := (cands.filterMap fun (v, hh) =>
        if v.name == nm && hh == h then some v else none).foldl (init := []) fun acc v =>
      if acc.any (·.unique == v.unique) then acc else acc ++ [v]
    if group.length < 2 then none else
    let shown := group.map fun v => ((ownerOf v).getD "?", localId v)
    match group.map ownerOf with
    -- Every bind attributed AND all to one class ⇒ the multi-parameter exemption.
    -- "Not attributed" is NOT "same class": an unrecognized dictionary shape falls
    -- through to the refusal, which is the safe direction.
    | (some c) :: rest => if rest.all (· == some c) then none else some (nm, nameOfHead h, shown)
    | _                => some (nm, nameOfHead h, shown)

/-- The refusal message for one `ambiguousMethodBinds` entry. Names the method,
    the head type, and every candidate class with the def it would have become. -/
def ambiguousMethodBindError (bindName : Name) (head : Name)
    (cands : List (Name × String)) : String :=
  let mname := if bindName.startsWith "$c" then bindName.drop 2 else bindName
  let lines := String.intercalate "\n" (cands.map fun (cls, dn) =>
    s!"    - declared by class `{cls}`, would emit as `{dn}`")
  s!"the method `{mname}` at instance head `{head}` has {cands.length} `{bindName}` bindings,\n" ++
  s!"  and they do not all belong to one class:\n" ++
  lines ++ "\n" ++
  s!"  GHC does not suffix `$c<method>` names per instance, so those bindings differ\n" ++
  s!"  only by unique, and every bind lookup in the emitter keys on\n" ++
  s!"  (method name, first value-argument type) — NOT on the declaring class. It\n" ++
  s!"  would therefore take whichever binding the dump lists first.\n" ++
  s!"  MEASURED on the `==` cell of this shape (`examples/haskell/UserClassEqWithEq.hs`):\n" ++
  s!"  `instance : BEq R` was wired to the USER class's body while the derived\n" ++
  s!"  structural body was emitted and never referenced, so `x == y` computed the\n" ++
  s!"  user's operator — `#eval` disagreed with Haskell and `decide` PROVED the\n" ++
  s!"  Haskell truth false, with rc=0 and empty stderr. That is the one failure mode\n" ++
  s!"  this transpiler forbids, so the program is refused. The same key decides the\n" ++
  s!"  `Ord` route too (`ordRoute` reads it to choose between `deriving Ord` and the\n" ++
  s!"  user's `compare`), where a first-match picks the ORDER the module computes.\n" ++
  s!"  The instance dictionaries above DO say which binding is whose, but the emitter\n" ++
  s!"  decides on this key in four independent places (`findClassMethodBind`,\n" ++
  s!"  `findCompareBind`, `isSuppressedMethod`, `derivedEqTypes`); attributing at some\n" ++
  s!"  of them and not the rest would move the wrong answer, not remove it.\n" ++
  s!"  Remedy: rename the class method to a name no other class in scope at `{head}`\n" ++
  s!"  declares, or drop one of the two instances on `{head}`."

/-- The emitted (unique-suffixed) def name of that binding. -/
private def findClassMethod (binds : CoreProgram) (method : Name) (headTyStr : String) : Option String :=
  (findClassMethodBind binds method headTyStr).map (fun (v, _) => localId v)

/-! ### `Ord`: derived, hand-written, or neither (M3 Task 6)

An `Ord` instance takes exactly one of three routes, and `ordRoute` is the SINGLE
decision procedure — consulted by `emitInstance` (what to emit), `emitFullProgram`
(which `$c` binds to suppress, and whether the data decl derives `Ord`/
`DecidableEq`) and `unsupportedOrdInstances` (the diagnostic), so those cannot
disagree.

WHAT IT REPLACED, and why that was silent-wrong. Until this task the key was
INSTANCE EXISTENCE: every type with an `Ord` instance got `deriving Ord` plus the
companions, and `isSuppressedMethod` dropped its real `$ccompare`/`$c<`/… bodies.
A hand-written non-structural `Ord` was therefore replaced by Lean's structural
order with zero diagnostics. MEASURED at the parent commit on `data W = W Int` +
`instance Ord W where compare (W a) (W b) = compare b a`: the emitted `wLt` reads
`decide (a < b)` against `deriving Ord`, so `wLt (W 1) (W 2)` is `true` in Lean and
`False` in Haskell — and `theorem … = false := by decide` PROVED the Haskell truth
false. Task 5 made it worse in reach, not in kind: an `Ord a =>`-constrained call
at such a head used to fail LOUD (`failed to synthesize LT t`, no binder recipe)
and now elaborates against the same wrong order.

THE DISCRIMINATORS, both read off `examples/haskell/OrdHandwritten.hs` and the
six-shape probe recorded in the `M3 Task 6` block of `Tests/Unit.lean`:

* **tag primops** (`usesTagPrim`, as `derivedEqTypes` uses for `Eq`) — GHC's
  DERIVED `compare` on a multi-constructor type is `case dataToTag# a of … `,
  untranslatable, so it routes to `deriving Ord`. A hand-written body never
  contains one (probed: even `compare a b = compare (fromEnum b) (fromEnum a)`
  keeps the primop inside `$cfromEnum`, since nothing inlines at `-O0`).
* **a Rec group with the dictionary builder** — GHC emits a method body that
  depends on the instance's OWN dictionary inside `Rec [$fOrdT, …]`, the same
  shape M3 Task 4 observed for default methods. Rec membership alone is NOT the
  discriminator: TWO different bodies produce it, and the first release of this
  task classified both `.unsupported`, which broke plain `deriving Ord` on every
  recursive ADT (see `ownDictOpsAtHead`, which splits them):

  * a MINIMAL `<=`-only instance's `compare` — the class default,
    `if x == y then EQ else if x <= y then LT else GT`, reaching the `Eq`
    superclass through `$p1Ord @T $fOrdT` and `<=` through `$fOrdT`. Not
    emittable: the body needs several methods of the instance being defined,
    which Lean does not see forward. `unsupported` drops the whole `Ord`, so
    every use is loud, and `Main.lean` warns.
  * a SELF-RECURSIVE `compare`, which recurses as `compare @T $fOrdT` and so
    lands in the very same group. `data Tree = Leaf | Node Tree Tree deriving
    (Eq, Ord)` is this shape — 2 constructors, so no tag primop routes it to
    `.derived`. It IS emittable: the only thing it needs from its own dictionary
    is `compare`, i.e. the def being emitted, so `retargetSelfCompare` rewrites
    the call to the def's own name and Lean's structural recursion takes it.
    MEASURED end-to-end; the `M3T6C` block in `Tests/Unit.lean` pins the order
    against Lean's own `deriving Ord` on the same inductive.

  This test reads a Rec group's MEMBERSHIP, which `filterBinds`' docstring warns
  against classifying by — so note what it does not do: it never reads the group's
  HEAD or its order, only whether SOME member is a dict builder, which is stable
  under the per-pair filtering both `Main.keepBinding` and `filterBinds` do. The
  dfun itself survives to this point in every path checked: `Lower.lowerBind`
  rewrites bodies and keeps every top-level binder, `Main.isGhcRuntimePlumbing`
  drops `$fShow…` but no other `$f`, and `emitFullProgram`'s `isJunkName` (which
  does drop every `$f`) runs on `keptBinds`, AFTER this decision, over a separate
  list. Witnessed e2e: `OrdHandwritten.hs`'s `MinDef` reaches `unsupported`, which
  it could not if the dfun had been filtered out of the group by then. Were that to
  change, this arm would flip to `handwritten` and emit a body referencing an
  erased dictionary — loud (unknown identifier), not silent.

`.handwritten` carries the `$ccompare` def name so the caller cannot re-derive it
by a different key.

THE TWO MISCLASSIFICATION DIRECTIONS, both pinned in `Tests/Unit.lean`:

* **hand-written read as DERIVED** (the silent-wrong direction) is closed for every
  body GHC generates from ordinary Haskell, because the only way a tag primop
  reaches a `$ccompare` body at `-O0` is a LITERAL `dataToTag#` in user source.
  That residual is real and MEASURED (`{-# LANGUAGE MagicHash #-}` +
  `compare a b = compare (I# (dataToTag# b)) (I# (dataToTag# a))` ⇒ `tagprim=True`
  in the dump), not hypothetical; it stays silent-wrong, no worse than the
  pre-task state where every hand-written `Ord` was. Closing it needs instance
  ORIGIN from the decl-plugin (the same extension M2 named for `deriving` on a
  newtype); a shape test on the derived body was rejected as fragile — a
  false negative there would make working derived enums loud.
* **derived read as HAND-WRITTEN** is SOUND, and it is the COMMON case, not a
  corner. GHC's derived `compare` uses tag primops IFF the type has **≥3 NULLARY
  constructors, independently of how many non-nullary ones it has**. That is the
  measured rule and it is NOT the one this comment first claimed ("an all-nullary
  enum with ≥3 constructors"); the counterexample that settles it is `Mix2`:

      data N3   = N1 | N2 | N3                       3 nullary        tagprim=True
      data T2   = M1 | M2                            2 nullary        tagprim=False
      data Mix  = X1 | X2 | X3 Int                   2 nullary + 1    tagprim=False
      data Mix2 = Y1 | Y2 | Y3 | Y4 Int              3 nullary + 1    tagprim=True
      data Mix3 = Z1 Int | Z2 Int | Z3 Int           0 nullary + 3    tagprim=False

  (all `deriving (Eq, Ord)`; `$ccompare` scanned for `dataToTag#`/`tagToEnum#`).
  `Mix2` is not all-nullary yet takes the `.derived` route, which is why the
  earlier wording mattered: the scope of the soundness argument below is "every
  shape with ≤2 nullary constructors", not "every non-enum". So
  `data Coin = Heads | Tails deriving Ord` (the `OrdInstance` fixture) and
  `data Pair = Pair Int Int deriving Ord` both take the `.handwritten` route. The
  old comment on `derivedEqTypes` guessed exactly this ("a derived compare on a
  small enum is case-based and indistinguishable from a hand-written one") and it
  is right.

  Sound because the derived `compare` body IS the derived order, and the companions
  are functions of `compare` either way — so the emitted instance computes what
  `deriving Ord` computes. MEASURED rather than argued: the `M3T6B` `#guard`s pin
  `compare a b == <emitted body> a b` for the 2-ctor enum, the 3-ctor
  with-fields and the single-ctor-two-field shapes, exhaustively over the
  constructor space with fields sampled to hit `<`/`=`/`>`.

  What remains is a translation risk, not a semantic one: the body must EMIT.
  `Ordering` and `LT`/`EQ`/`GT` are mapped in `Maps.lean` on the expression side and
  on the case-ALT side (`Generated/OrdInstance.lean` and
  `Generated/OrdHandwritten.lean` exercise both), and a body that failed to
  translate would be loud. One such body EXISTS today, and it predates this task:
  derived `==` on a multi-constructor type with fields emits GHC's `void#` fallback
  (`GHC.Prim.void_hash_`, unknown identifier). Measured with BOTH binaries on the
  same dump — 5 occurrences each, all inside `$c==` defs, none inside `$ccompare` —
  so the `Eq` path owns it and no derived `compare` shape probed here is affected.

HAND-WRITTEN `$c<` / `$cmin` / … BODIES ARE DROPPED, and here is the decision in
full, because M3 Task 3's block explicitly hands it to this task. `<`, `≤`, `min`,
`max` at a hand-written-`Ord` type come from `ordCompanionInsts`, i.e. from
`compare`, so an instance defining `compare` AND a disagreeing `<` loses the `<`.
Three reasons, in increasing strength:

* Those bodies are not the user's own code in the first place. OBSERVED: for
  `instance Ord W where compare …`, GHC puts every other `Ord` method in
  `Rec [$fOrdW, $cmax, $c>=, $c>, $c<=, $cmin, $c<]` with bodies calling
  `compare @W $fOrdW` / `<= @W $fOrdW`, i.e. the class DEFAULTS specialized to this
  instance. Dropping them loses nothing a user wrote — unless the user wrote both
  `compare` and `<`, which is the only case this paragraph is really about.
* There is nowhere to wire one. The companions cannot be arbitrary: `decide (a < b)`
  needs `Decidable (a < b)`, which core provides ONLY as
  `DecidableRel (@LT.lt α ltOfOrd)` — matching `ltOfOrd` LITERALLY. MEASURED: swap
  in `instance : LT W := ⟨fun a b => <hand-written> a b = true⟩` and the very next
  `decide (a < b)` is `error: failed to synthesize Decidable (a < b)`. So a
  hand-written `<` body cannot become the `LT` instance without breaking every
  `<` at that type; `ltOfOrd` off `compare` is the only shape that works.
* Lean is then MORE lawful than a law-violating Haskell instance (Task 3's framing),
  which is a defensible place to land rather than a compromise.

A user who defines BOTH `compare` and `<` gets the `compare` one. A user who defines
`<` (or `<=`) ONLY has no `compare` of their own at all: the default lands in that
Rec group and the whole instance is `unsupported` — loud and warned, rather than
half-translated.

WHAT REMAINS UNSUPPORTED after the self-recursion arm, all loud:

* the `<=`/`<`-only minimal instance (above): its `compare` needs `==` and `<=`
  from the instance being defined, and only `compare` can be redirected;
* a hand-written `compare` that recurses AND uses another method of its own `Ord`
  (`compare x y = if x <= y then … else compare …`): `ownDictOpsAtHead` sees two
  ops, so the whole `Ord` is dropped rather than emitted with a dangling `<=`;
* MUTUALLY recursive types (`data A = A B; data B = B A deriving Ord`), whose two
  `compare` defs would need one Lean `mutual` block — this emitter places each
  type's block next to its own `inductive`, so the second def's forward reference
  to the first is loud. Not fixed here; it also needs a `mutual` DATA block,
  which `sortDataDecls` does not emit either (its cycle arm is already documented
  as loud-on-forward-reference).
* a `compare` whose own-dict argument types could not be read at all (nothing
  matched at the head type). That collapses with the case above deliberately:
  "we could not tell what it needs" and "it needs more than `compare`" get the
  same conservative route, which is what the pre-fix code did for both. -/
inductive OrdRoute where
  /-- GHC-derived: `deriving Ord` + companions in the data block, `$c` bodies
      suppressed (they use tag primops and have no Lean image). -/
  | derived
  /-- The user's own `compare` (or GHC's derived one on a shape with ≤2 nullary
      constructors), emitted as a def plus an instance block pointing at that def
      name, plus the same companions. `selfRec` marks the body that recurses
      through its own dictionary, whose `compare @T $fOrdT` call
      `retargetSelfCompare` must rewrite to `compareRef` before emission. -/
  | handwritten (compareRef : String) (selfRec : Bool)
  /-- No emittable `compare` (absent, or a dictionary-dependent body needing more
      of the instance than `compare`): no `Ord` at all, loud at every use site. -/
  | unsupported
deriving DecidableEq, Repr

/-- The `$ccompare` bind at `headTyStr`, and whether it shares a top-level `Rec`
    group with a dictionary builder (`$f…`) — GHC's marker for a body that needs
    the instance's own dictionary, i.e. a class default rather than the user's
    code. Head matching is `findClassMethodBind`'s (`$ccompare`'s first value
    argument is the instance head), duplicated here only to also report the Rec
    group, which that function's return type cannot carry.

    AND IT INHERITS THAT FUNCTION'S AMBIGUITY, which is why the multi-match arm is
    duplicated too: a user class declaring a method named `compare` at a head that
    also has an `Ord` instance produces two `$ccompare` binds with one first
    value-argument type (`/tmp/transpile-ProbeCmpCollide.json`: `$ccompare` twice
    at `T`). `ordRoute` reads this function's answer to pick between `deriving Ord`
    and the user's body, so a first-match here decides the ORDER a module computes.
    `none` on a multi-match is defense in depth — `Main.lean`'s
    `ambiguousMethodBinds` refuses the program first — and again means "no UNIQUE
    such bind", not "none". -/
private def findCompareBind (binds : CoreProgram) (headTyStr : String)
    : Option (Var × Expr × Bool) :=
  let matchesHead (v : Var) : Bool :=
    v.name == "$ccompare" &&
      (match firstValArgTy v.ty with
       | some t => emitType t == headTyStr
       | none   => false)
  let hits : List (Var × Expr × Bool) := binds.flatMap fun b => match b with
    | .nonRec v e => if matchesHead v then [(v, e, false)] else []
    | .rec_ pairs =>
      let inDictRec := pairs.any (fun (w, _) => w.name.startsWith "$f")
      (pairs.filter (fun (v, _) => matchesHead v)).map fun (v, e) => (v, e, inDictRec)
  match hits with
  | [hit] => some hit
  | _     => none

/-- The emitted type of an application's FIRST `Var` argument — a POST-`Lower`
    approximation of the type a class op is instantiated at, which works only
    because `Lower` has erased the `@T` type application and the dictionary and
    left the value arguments. `none` when no argument is a bare `Var` (a compound
    argument carries no type here at all).

    THE FIRST ONE, not any one, and that is load-bearing. A class op's dispatch
    type is its first value argument's type, which is the convention
    `methodHeadStr`/`findClassMethodBind` already key on. Reading "some argument"
    instead over-reports on a dump quirk that is REAL: GHC's `case` binder arrives
    as `wild` with a shim-assigned unique, and its recorded TYPE is not reliably
    the scrutinee's — measured on `OrdSectionOrder.hs`, where
    `== @Frac2 $fEqFrac2 x wild` has `x : Frac2` (right) and `wild : Alpha`
    (wrong, and `Alpha` is another decl in the same module). Under "some argument"
    that made `eqHoistHeads` hoist `Alpha`'s `BEq` as well — harmless in itself,
    but a spurious hoist moves a body into the data block and can turn a `$c==`
    that calls a top-level function from working into loud.

    UNDER-REPORTING IS NOT UNIFORMLY CONSERVATIVE, and an earlier version of this
    docstring claimed it was ("the conservative direction for every caller").
    Per caller:

    * `ownDictOpsAtHead`, `retargetSelfCompare` — under-report ⇒ LOUD. Missing an
      op means `ordRoute` refuses the body, or a self-`compare` is left needing an
      `Ord` declared later; both fail at `lake build`.
    * `opArgTypes` (via `classOpHeadTy`) — under-report ⇒ SILENT-WRONG. Missing an
      `==` means `eqHoistHeads` does not splice the user's `BEq` ahead of the
      spliced `Ord` block, so that `==` binds `instBEqOfDecidableEq` (structural
      equality) with no diagnostic anywhere. `instance Eq G where G a b == G c d =
      a * d == c * b` plus a `compare` testing `G a b == G c d` is exactly that
      shape: post-`Lower` the spine is `== (G a b) (G c d)`, no bare `Var`, nothing
      detected. That caller therefore reads the TYPE APPLICATION out of the
      pre-`Lower` program (`classOpHeadTy`) and uses this function only as the
      fallback for a post-`Lower` input, where the quirk above is why it still
      reads the first argument and not any argument. -/
def firstVarArgTy : List Expr → Option String
  | []            => none
  | .var v :: _   => some (emitType v.ty)
  | _ :: rest     => firstVarArgTy rest

/-- The emitted type a class op is instantiated at, read from the application's
    TYPE ARGUMENT: `== @Cross $fEqCross (Cross a b) (Cross c d)` ⇒
    `emitType Cross`. OBSERVED spine, from `/tmp/transpile-OrdSectionOrder.json` —
    section (6) of that fixture, the `$ccompare` body of
    `instance Ord Cross where compare (Cross a b) (Cross c d) | Cross a b ==
    Cross c d = EQ | …`:

        App (App (App (App (Var GHC.Classes.==) (Type (TyCon Cross)))
                      (Var $fEqCross [role=dict]))
                 (App (App (Var Cross) (Var a)) (Var b)))
            (App (App (Var Cross) (Var c)) (Var d))

    i.e. `spineOf` gives `[Type Cross, Var $fEqCross, Cross a b, Cross c d]` and
    the FIRST element is the answer. Shape-independent: it does not matter what the
    value arguments look like, which is the whole point — `firstVarArgTy` reads
    nothing at all here, and on this spine the first bare `Var` is the DICTIONARY
    (`$fEqCross`, typed `_Unknown` by the shim), so it is not a usable fallback
    pre-`Lower` either. The measured argument-tag lists for the same fixture's two
    `Ord` heads are `[Type, Var, App, App]` for `Cross` and `[Type, Var, Var, Var]`
    for `Frac2` — the second is the only one the pre-fix read could see.

    EXACT for the ops this is used with, and that is a precondition rather than a
    theorem: it assumes a SINGLE-PARAMETER class whose class variable is the first
    type argument of the method (`Eq a`'s `==`, `Ord a`'s `compare`). A
    multi-parameter or higher-kinded op would put something else first and this
    would answer the wrong type silently — so `opArgTypes`' `ops` list must stay
    single-parameter class methods.

    FALLS BACK to `firstVarArgTy` when there is no type argument at all. That is
    the post-`Lower` case (`Lower` erases `.type_` arguments), which the two
    `eqHoistHeads` callers reach only for a `Program` whose `rawBinds` defaulted
    to `binds` — a hand-written test literal. Falling back keeps those literals
    answering what they answered before this fix. -/
def classOpHeadTy (as : List Expr) : Option String :=
  match as.findSome? (fun | .type_ t => some (emitType t) | _ => none) with
  | some h => some h
  | none   => firstVarArgTy as

/-- The FOREIGN (dotted, i.e. non-local) operators this body applies to a value of
    `headTy`. For a `$ccompare` body that shares a Rec group with its own
    dictionary builder, this is what the body needs FROM that dictionary, and the
    set decides `ordRoute`'s two Rec-group arms:

    * `["GHC.Classes.compare"]` — self-recursion and nothing else, so redirecting
      the call to the def being emitted (`retargetSelfCompare`) discharges it;
    * anything else, EMPTY INCLUDED — more of the instance than `compare`, or a
      shape whose argument types could not be read; `.unsupported`.

    OBSERVED, the two bodies it separates (spines in the `M3 Task 6` block of
    `Tests/Unit.lean`): derived `compare` on `data Tree = Leaf | Node Tree Tree`
    applies only `compare @Tree $fOrdTree a1 b1`, while the `<=`-only class
    default applies `== @T ($p1Ord @T $fOrdT)` AND `<= @T $fOrdT` — post-`Lower`,
    `[GHC.Classes.compare]` versus `[GHC.Classes.==, GHC.Classes.<=]`.

    Restricted to DOTTED names on purpose. A call to a local top-level function at
    the head type (`compare (norm x) (norm y)`) is not a dictionary dependency and
    must not veto the arm; and a nested `compare` at a DIFFERENT type
    (`compare @Int` over two fields, which every derived compare on a type with
    fields contains) is excluded by the argument-type test, not by the name. -/
partial def ownDictOpsAtHead (headTy : String) : Expr → List Name
  | .var _            => []
  | .lit _            => []
  | .type_ _          => []
  | .coercion         => []
  | .cast e           => ownDictOpsAtHead headTy e
  | .tick e           => ownDictOpsAtHead headTy e
  | .lam _ b          => ownDictOpsAtHead headTy b
  | .let_ bnd b       =>
    (match bnd with
     | .nonRec _ e => ownDictOpsAtHead headTy e
     | .rec_ ps    => ps.flatMap (fun p => ownDictOpsAtHead headTy p.2))
      ++ ownDictOpsAtHead headTy b
  | .case_ s _ _ alts =>
    ownDictOpsAtHead headTy s
      ++ alts.flatMap (fun (.mk _ _ r) => ownDictOpsAtHead headTy r)
  | e@(.app f a)      =>
    let (h, as) := spineOf e
    let here := match h with
      | .var op =>
        if op.name.contains '.' && firstVarArgTy as == some headTy then [op.name] else []
      | _       => []
    -- Recursing into `f` re-analyses the partial spine (`compare a1` inside
    -- `compare a1 b1`) and can report the same op twice; `dedup` at the caller
    -- makes that unobservable, and the alternative (skipping `f`) would miss an
    -- op applied inside an ARGUMENT of another application.
    here ++ ownDictOpsAtHead headTy f ++ ownDictOpsAtHead headTy a

/-- Rewrite this body's SELF-RECURSIVE `compare` calls — `compare` applied to a
    value of `headTy`, which post-`Lower` is the erased `compare @T $fOrdT` — to
    reference `self` (the `$ccompare` binder itself) instead of the class op.

    The point is that `refId`/`defNameId` then spell it `localId self`, i.e. the
    very def this body becomes, so Lean's structural recursion closes the loop
    that GHC closed through the dictionary. Both misfire directions are LOUD, and
    that is the whole safety argument: retargeting a call that was NOT at the head
    type gives an argument-type mismatch, and failing to retarget one that was
    leaves `compare` needing an `Ord {headTy}` that is declared after this def
    (`failed to synthesize`). Neither can silently change the order computed.

    Applied ONLY on the `.handwritten … (selfRec := true)` route, so a body
    without a self-call is passed through untouched by construction. -/
partial def retargetSelfCompare (headTy : String) (self : Var) : Expr → Expr
  | .cast e           => .cast (retargetSelfCompare headTy self e)
  | .tick e           => .tick (retargetSelfCompare headTy self e)
  | .lam v b          => .lam v (retargetSelfCompare headTy self b)
  | .let_ bnd b       =>
    let bnd' := match bnd with
      | .nonRec v e => Bind.nonRec v (retargetSelfCompare headTy self e)
      | .rec_ ps    => Bind.rec_ (ps.map fun (v, e) => (v, retargetSelfCompare headTy self e))
    .let_ bnd' (retargetSelfCompare headTy self b)
  | .case_ s bv ty alts =>
    .case_ (retargetSelfCompare headTy self s) bv ty
      (alts.map fun (.mk c bs r) => Alt.mk c bs (retargetSelfCompare headTy self r))
  | e@(.app f a)      =>
    let (h, as) := spineOf e
    match h with
    | .var op =>
      if op.name == "GHC.Classes.compare" && firstVarArgTy as == some headTy then
        (as.map (retargetSelfCompare headTy self)).foldl Expr.app (.var self)
      else
        .app (retargetSelfCompare headTy self f) (retargetSelfCompare headTy self a)
    | _ => .app (retargetSelfCompare headTy self f) (retargetSelfCompare headTy self a)
  | e                 => e

/-- Which of the three routes the `Ord` instance at `headTyStr` takes — see the
    section header for the full argument. Keyed on the head STRING (the spelling
    every instance-matching key in this file uses, computed before the resolution
    passes run), so it can be called from the instance side and the bind side
    alike. Recomputed per call (`emitFullProgram` asks twice per `Ord` head,
    `emitInstance` and `unsupportedOrdInstances` once each) and each call scans the
    binds; the product is bounded by the `Ord`-instance count, which is why the
    single decision procedure is preferred over caching it in a threaded list.

    The Rec-group arm is MONOTONE against the first release of this task, which
    answered `.unsupported` for every body in a dictionary group: the only route
    that changed is the one `ownDictOpsAtHead` recognises as self-recursion, and
    every other body still lands where it did. So no input that worked can break
    here, and the arm that was added is loud on either misfire
    (`retargetSelfCompare`). -/
def ordRoute (binds : CoreProgram) (headTyStr : String) : OrdRoute :=
  match findCompareBind binds headTyStr with
  | none                    => .unsupported
  | some (v, e, inDictRec) =>
    if usesTagPrim e then .derived
    else if !inDictRec then .handwritten (localId v) false
    else if dedup (ownDictOpsAtHead headTyStr e) == ["GHC.Classes.compare"]
    then .handwritten (localId v) true
    else .unsupported

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

/-- One `Var` is a mislabelled default-method occurrence. -/
private def dmDictVar (v : Var) : List Name :=
  if v.name.startsWith "$dm" && v.role == .dict then [v.name] else []

/-- Every `$dm`-named dict-role `Var` inside an expression, in ANY position:
    references, lambda binders, both `let` forms, the case binder and pattern
    binders. The match is TOTAL (no catch-all) so that adding an `Expr`
    constructor cannot silently shrink the scan — `Lower` erases dict-role Vars
    both at references (`isTypeOrDictArg`, argument position) and at binders
    (`isTypeOrDictBinder`, lambda/`let`), so every position is failure surface. -/
private partial def dmDictVarsInExpr : Expr → List Name
  | .var v      => dmDictVar v
  | .lit _      => []
  | .app f a    => dmDictVarsInExpr f ++ dmDictVarsInExpr a
  | .lam v b    => dmDictVar v ++ dmDictVarsInExpr b
  | .let_ bnd b =>
    (match bnd with
     | .nonRec v e => dmDictVar v ++ dmDictVarsInExpr e
     | .rec_ ps    => ps.flatMap (fun p => dmDictVar p.1 ++ dmDictVarsInExpr p.2))
      ++ dmDictVarsInExpr b
  | .case_ scr cb _ alts =>
    dmDictVarsInExpr scr ++ dmDictVar cb
      ++ alts.flatMap (fun (.mk _ bs r) => bs.flatMap dmDictVar ++ dmDictVarsInExpr r)
  | .cast e     => dmDictVarsInExpr e
  | .type_ _    => []
  | .coercion   => []
  | .tick e     => dmDictVarsInExpr e

/-- Every `$dm<method>` `Var` in the program whose ROLE says `dict` — binders AND
    references, at top level and inside every body. Should be empty: the shim
    classifies `$dm` as `id`. A non-empty result means the dump's roles are the
    old heuristic's, under which `Lower` silently ERASES that occurrence
    (`isTypeOrDictArg` in argument position, `isTypeOrDictBinder` at a
    lambda/`let` binder); wired to a warning in `Main.lean`.

    References are scanned, not just binders, because the shim carries TWO
    independent copies of the `$d`/`$f` prefix rule: `binderRole` for binders and
    `convertExternalName` for references. GHC reaches a top-level name through
    `EVarGlobal` even inside its own module, so a `$dm` USE is classified by the
    second copy — a reference's role is NOT inherited from its binder. Both copies
    now exempt `$dm`; while only `binderRole` did, `$dmgreet`'s binder said `id`
    and its one reference said `dict` (DefaultMethods dump: `/binds/4` vs
    `/binds/26/pairs/1/rhs/fun/fun`), the exact split a binders-only scan is blind
    to. That reference was harmless only because it sits in HEAD position, which
    `isTypeOrDictArg` never inspects; nothing kept it there.

    Must be applied to the RAW dump, before `Lower`: lowering has already deleted
    a dict-role occurrence in argument position, so the lowered program no longer
    holds the evidence. `Main.lean` calls it on `prog.binds` for that reason. -/
def dmVarsMislabelledAsDicts (binds : CoreProgram) : List Name :=
  (binds.flatMap fun b => match b with
    | .nonRec v e => dmDictVar v ++ dmDictVarsInExpr e
    | .rec_ pairs => pairs.flatMap (fun (v, e) => dmDictVar v ++ dmDictVarsInExpr e)
  ).eraseDups

/-- The warning for one `dmVarsMislabelledAsDicts` entry. -/
def dmDictRoleWarning (n : Name) : String :=
  s!"default-method `Var` `{n}` arrived with role `dict`. It is a method BODY, not\n" ++
  s!"  a dictionary — the shim's role heuristic (`$d`-prefixed ⇒ dict) must exempt\n" ++
  s!"  `$dm` in BOTH places that rule is written (`binderRole` for binders,\n" ++
  s!"  `convertExternalName` for references), and this dump's does not. Consequence:\n" ++
  s!"  an occurrence of `{n}` in argument position — or as a lambda/`let` binder —\n" ++
  s!"  is erased as a dictionary, silently dropping the default's body from wherever\n" ++
  s!"  it was used. Rebuild the shim."

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
    or skip one with no diagnostic).

    `spine` is the instance's `dfunMethodBinds` attribution and is consulted
    FIRST, because it is the more informative of the two: it knows the methods
    whose type does not start with the class parameter. It is TRAILING with a `[]`
    default so a caller (or `#guard`) that has no dictionary to read falls back to
    exactly the pre-M3-Task-5 behavior. -/
def classifyInstanceMethod (defaults : List (Name × Name)) (binds : CoreProgram)
    (cls : Name) (headTyStr : String) (m : ClassMethod)
    (spine : List (Name × Var × Expr) := []) : MethodFate :=
  let defaulted := defaults.contains (cls, m.name)
  let fromSpine := (spine.find? (·.1 == m.name)).map (fun (_, v, e) => (v, e))
  match fromSpine.orElse (fun _ => findClassMethodBind binds ("$c" ++ m.name) headTyStr) with
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
  let spine := dfunMethodBinds binds cd i
  let fates := cd.methods.map fun m =>
    (m, classifyInstanceMethod defaults binds i.className tyStr m spine)
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
    (`mergeClassDecls`' methods-disagree path); and a method whose type does not
    START with the class parameter WHEN the dictionary attribution also declines
    (`dfunMethodBinds` — no dfun bind, an unrecognized dfun body, or its name
    guard rejecting the pairing).

    That last shape is what M3 Task 5 mostly REMOVED. It used to fire on
    `examples/haskell/SuperClass.hs` — `$cempty : Bag` (no value argument at all)
    and `$cinsert : (Int -> (Bag -> Bag))` (first argument `Int`) are both
    invisible to `findClassMethodBind`'s first-value-argument match, and the
    `Container Bag` instance was dropped for it. The dictionary now attributes both
    positionally, so the fixture emits, and what remains here is the residue: the
    same shape in a module where no dictionary can be read.

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
      -- Same attribution `emitInstanceUser` uses, from the same `p.binds`, or the
      -- warning and the emission would disagree about which methods resolve.
      let spine := dfunMethodBinds p.binds cd i
      cd.methods.filterMap fun m =>
        if classifyInstanceMethod defaults p.binds i.className tyStr m spine == .unresolved
        then some (i.className, headTypeNames i, m.name) else none

/-- Every `(class, superclass)` pair the class emission drops, program-wide — the
    Program-level view of `unmappedSupers`, wired to an `eprintln` in `Main.lean`.
    Computed on the MERGED class set, exactly like the other diagnostics here, so a
    class with no local instance (plugin-only) is covered too. -/
def droppedSupers (p : Program) : List (Name × Name) :=
  let classes := mergeClassDecls p.classDecls (reconstructClasses p.binds p.instances).1
  let classNames := classes.map (·.name)
  classes.flatMap fun c => (unmappedSupers classNames c).map fun s => (c.name, s)

/-- Every `(class, superclass, parameter count)` dropped for the multi-parameter
    reason, program-wide — the Program-level view of `multiParamSupers`, wired to
    an `eprintln` in `Main.lean`. Disjoint from `droppedSupers` and from
    `droppedMultiParamParents` by construction (each of the three per-class
    functions is empty wherever another can be non-empty: this one needs the CHILD
    to take ≠ 1 parameters, `droppedMultiParamParents` needs it to take exactly
    one, and `droppedSupers` needs the parent to have no Lean image while
    `droppedMultiParamParents` only reports parents that are local classes), so no
    superclass is reported twice. Computed on the MERGED class
    set like every other diagnostic here — and note that only the PLUGIN channel
    can produce a multi-parameter shape at all: `reconstructClasses` invents a
    single type variable, so a run with no decls sidecar reports nothing here and
    emits a one-parameter class for a two-parameter Haskell one. That fallback
    mis-shape is loud (the emitted class's method types mention a variable the
    header does not bind, and every instance head has two arguments where the
    class takes one). -/
def droppedMultiParamSupers (p : Program) : List (Name × Name × Nat) :=
  let classes := mergeClassDecls p.classDecls (reconstructClasses p.binds p.instances).1
  classes.flatMap fun c =>
    (multiParamSupers c).map fun s => (c.name, s, c.tyVars.length)

/-- Every `(class, superclass, SUPERCLASS's parameter count)` dropped because the
    PARENT takes more than one type parameter — the Program-level view of
    `multiParamParentSupers`, wired to an `eprintln` in `Main.lean`. Computed on
    the MERGED class set, and from THAT set's arities, so it reports exactly the
    parents `emitProgram`'s `emitClassDecl` call leaves out of `extends`.

    Like `droppedMultiParamSupers` this is reachable only through the PLUGIN
    channel: `reconstructClasses` invents one type variable per class, so with no
    decls sidecar no class is multi-parameter and this list is empty. -/
def droppedMultiParamParents (p : Program) : List (Name × Name × Nat) :=
  let classes := mergeClassDecls p.classDecls (reconstructClasses p.binds p.instances).1
  classes.flatMap fun c =>
    (multiParamParentSupers classes c).map fun (s, n) => (c.name, s, n)

/-- The warning for one `unresolvedInstanceMethods` entry. -/
def unresolvedInstanceMethodWarning (cls head mname : Name) : String :=
  s!"instance `{cls} {head}` is DROPPED: its method `{mname}` resolves to nothing —\n" ++
  s!"  no `$c{mname}` binding for that instance head survives in this module, and the\n" ++
  s!"  class declares no default body for it (or the default's `$dm{mname}` binding is\n" ++
  s!"  itself missing). A Lean instance cannot omit a field that has no default, so\n" ++
  s!"  the whole instance is skipped; every use of `{cls}`'s methods at `{head}` will\n" ++
  s!"  fail with `failed to synthesize {cls} {head}` at `lake build`.\n" ++
  s!"  Likely causes: the instance's dictionary could not be read (no dfun binding,\n" ++
  s!"  or a shape whose method arguments are not named `$c<method>`) AND `{mname}`'s\n" ++
  s!"  type does not start with the class parameter, which is the fallback\n" ++
  s!"  attribution's only key; the binding was filtered as `Eq`/`Show` plumbing (see\n" ++
  s!"  Main.lean's drop rules); or the class-shape dump declares a method this module\n" ++
  s!"  has no binding for."

/-- The `Ord` instances that get NO Lean image (`OrdRoute.unsupported` — see the
    `Ord`-route section header), for `Main.lean`'s warning. Not a refusal: the drop
    is loud at `lake build` (every `compare`/`<`/`min` at that type fails to
    synthesize) and refusing would newly reject modules whose unusable `Ord` is
    never used — the same call `unresolvedInstanceMethods` makes. Same `ordRoute`
    the emission uses, over the same `p.binds`, so warning and emission cannot
    disagree about which instances vanish. -/
def unsupportedOrdInstances (p : Program) : List Name :=
  (p.instances.filter (·.className == "Ord")).filterMap fun i =>
    match ordRoute p.binds (i.headTypes.map emitType |> String.intercalate " ") with
    | .unsupported => some (headTypeNames i)
    | _            => none

/-- The warning for one `unsupportedOrdInstances` entry.

    Deliberately does NOT claim a user instance exists, nor that defining `compare`
    is always the remedy. The first release of this message asserted both, and on
    the shape that actually reached it most often — a plain `deriving Ord` on a
    recursive ADT, no user instance anywhere — it blamed a minimal `(<=)` instance
    the user had not written and prescribed a `compare` that would have landed in
    the very same Rec group. That shape is now EMITTED (`ordRoute`'s self-recursion
    arm), so what is left really is dictionary-dependent beyond `compare`; the
    message says which cases those are and stops short of promising a fix. -/
def unsupportedOrdWarning (head : Name) : String :=
  s!"instance `Ord {head}` is DROPPED: no translatable `compare` body for it.\n" ++
  s!"  Either there is no `$ccompare` binding at that head, or the one there needs\n" ++
  s!"  MORE of the `Ord {head}` dictionary than `compare` — which Lean does not see\n" ++
  s!"  forward, since that dictionary is the instance being defined. Two known\n" ++
  s!"  shapes reach this:\n" ++
  s!"    * a MINIMAL instance defining only `(<=)` (or only `(<)`), whose `compare`\n" ++
  s!"      is GHC's class default `if x == y then EQ else if x <= y then LT else GT`\n" ++
  s!"      — it needs `==` and `<=` from this same instance;\n" ++
  s!"    * a hand-written `compare` that recurses AND calls another method of its\n" ++
  s!"      own `Ord` (self-recursion ALONE is fine and is emitted).\n" ++
  s!"  NOTHING structural is substituted (that substitution was this transpiler's\n" ++
  s!"  silent-wrong behaviour until M3 Task 6); instead every\n" ++
  s!"  `compare`/`<`/`<=`/`min`/`max` at `{head}` fails loudly at `lake build` with\n" ++
  s!"  `failed to synthesize`.\n" ++
  s!"  Fix, for the minimal-instance shape: define `compare` itself, in terms of the\n" ++
  s!"  fields rather than of `<=`. For the recursive shape: express the non-`compare`\n" ++
  s!"  method call as a `compare … = …` test instead."

/-- The emitted head-type strings at which this body applies one of `ops` — the
    `classOpHeadTy` reading, i.e. the type argument of the application when there
    is one (exact, and the reason this must be given a PRE-`Lower` body) and the
    first bare-`Var` argument's type otherwise.

    Used for ONE question: at which types does an emitted `Ord`-section body call
    `==`/`/=`? Those are the `BEq` instances that must precede it.

    `ops` must be SINGLE-PARAMETER class methods — see `classOpHeadTy`, whose
    "first type argument is the dispatch type" reading is a precondition on the
    caller, not something it can check. -/
partial def opArgTypes (ops : List Name) : Expr → List String :=
  let rec go : Expr → List String
    | .cast e           => go e
    | .tick e           => go e
    | .lam _ b          => go b
    | .let_ bnd b       =>
      (match bnd with
       | .nonRec _ e => go e
       | .rec_ ps    => ps.flatMap (fun p => go p.2))
        ++ go b
    | .case_ s _ _ alts => go s ++ alts.flatMap (fun (.mk _ _ r) => go r)
    | e@(.app f a)      =>
      let (h, as) := spineOf e
      let here := match h with
        | .var op => if ops.contains op.name then (classOpHeadTy as).toList else []
        | _       => []
      here ++ go f ++ go a
    | _                 => []
  fun e => (go e).eraseDups

/-- The hand-written-`Eq` `$c==` bind at `h`, if that is the route `h`'s `Eq`
    takes. `derivedEq` is passed in rather than recomputed, because the caller's
    bind list may already have the derived `$c==` binds suppressed — recomputing
    `derivedEqTypes` over THAT list answers "no derived Eq anywhere". -/
def hwEqBindAt (binds : CoreProgram) (derivedEq : List String) (h : String)
    : Option (Var × Expr) :=
  if derivedEq.contains h then none else findClassMethodBind binds "$c==" h

/-- The heads whose OWN hand-written `$c==` body applies one of `ops` at that same
    head — a SELF-RECURSIVE hand-written `Eq`.

    Its own key, not a by-product of the `$ccompare` scan, because the defect it
    marks does not need a `compare` that mentions `==` at all. The `$c==` def
    precedes its `instance : BEq T` in EVERY layout — the instance references the
    def — so a self-`==` inside that body never sees the user's `BEq`. Whether that
    is silent or loud is decided by one line of the `inductive`: a
    `handwrittenOrd`/`derivedOrd` head carries `deriving … DecidableEq`, so
    `instBEqOfDecidableEq` is in scope from the data block and the call computes
    STRUCTURAL equality with no diagnostic; without that `deriving` the same call
    is a loud `failed to synthesize BEq T`. The silent half is the one that matters,
    and `eqHoistHeads` seeds on this so `eqBlockFor` gets the head — that is where
    `retargetSelfEq` runs, and where `spliceDef`'s `recOverride := some false`
    makes the resulting self-call STRUCTURAL recursion rather than a
    `decreasing_by all_goals sorry`.

    CANDIDATES come from `scanBinds` itself — every `$c==` binder's head via
    `methodHeadStr` — so no caller has to supply a head list that could disagree
    with the binds. `binds` still decides membership (`hwEqBindAt`), and the body is
    read from `scanBinds` because `classOpHeadTy` needs the pre-`Lower` type
    application.

    ONE definition, two consumers — the seed (`eqHoistHeads`) and the residual
    diagnostic (`hoistedEqSelfResiduals`) — so "which `Eq` recurses at its own
    head" has a single answer. -/
def selfEqHeads (binds scanBinds : CoreProgram) (derivedEq : List String)
    (ops : List Name) : List String :=
  let headOfEqBinder (v : Var) : List String :=
    if v.name == "$c==" then (methodHeadStr v).toList else []
  let cands := (scanBinds.flatMap fun b => match b with
    | .nonRec v _ => headOfEqBinder v
    | .rec_ ps    => ps.flatMap (fun (v, _) => headOfEqBinder v)).eraseDups
  cands.filter fun h =>
    (hwEqBindAt binds derivedEq h).isSome &&
      (match findClassMethodBind scanBinds "$c==" h with
       | some (_, e) => (opArgTypes ops e).contains h
       | none        => false)

/-- The heads whose hand-written `instance : BEq` must be emitted BEFORE the
    spliced `Ord` blocks, because some spliced body calls `==`/`/=` at that head.

    THE B3 FIX. Without it the only `BEq` in scope inside a `$ccompare` def was
    core's `instBEqOfDecidableEq`, off the `deriving DecidableEq` that
    `emitDataDecl`'s `handwrittenOrd` flag adds — so a cross-multiply `Eq` plus a
    `compare` testing `x == y` computed STRUCTURAL equality there, silently, while
    every ordinary use site got the user's instance. Lean picks the last-declared
    of equal candidates, which is why declaration order is the whole story.

    Seeded by the `$ccompare` bodies and closed over the hoisted `$c==` bodies
    themselves: one of those may call `==` at a THIRD type, whose `BEq` then has to
    precede it too. `fuel` bounds the closure (the decl count is enough — each
    round either adds a head or stops).

    ALSO SEEDED by `selfEqHeads`, which is NOT reachable from the `$ccompare` scan:
    a hand-written `Eq` that recurses at its own head has the same silent-wrong
    whether or not any `compare` mentions `==` there, because the `$c==` def
    precedes its `instance : BEq` in every layout. Routing such a head through the
    hoist is what gets it `retargetSelfEq` and `recOverride := some false`. The
    seed is UNIONED into each round rather than only into the initial accumulator —
    `next` is recomputed from scratch, so an element that did not re-derive itself
    would be dropped — and APPENDED, so when the seed is empty (every corpus module
    but the two fixture sections) the result is order-for-order what it was.

    TWO BIND LISTS, and the split is the fix for the compound-argument
    silent-wrong. `scanBinds` is the PRE-`Lower` program (`Program.rawBinds`) and
    is used only to fetch the BODIES that get scanned, because the type argument
    `classOpHeadTy` reads is exactly what `Lower` erases. `binds` is the list the
    emission keeps, and every MEMBERSHIP decision still comes from it: a head is
    hoisted only if `hwEqBindAt binds` finds a hand-written `$c==` there, so no
    head can be spliced whose body the emitter does not have. Passing the same
    list twice reproduces the pre-fix behaviour exactly (`classOpHeadTy` falls
    back to `firstVarArgTy` when the type argument is gone), which is what a
    `Program` with a defaulted `rawBinds` does.

    The detected set is now a SUPERSET of the pre-fix one: an `==` whose arguments
    are compound produced no head at all before and produces its exact head now,
    so `hwEqBindAt`'s filter is doing strictly more work. Every added element is a
    genuine `==`-at-that-head, which is why this is not the spurious hoist
    `localTypesInExpr` warns about — that one comes from reading a type off the
    wrong `Var`, and the type-application read consults no `Var` at all.

    ONE definition, two callers — the emission (`emitFullProgram`) and the
    forward-reference diagnostic (`ordForwardRefs`) — so the set that gets spliced
    and the set that gets scanned for forward references cannot disagree. The two
    pass `binds` differently (kept binds vs. the whole program, as they did before
    this fix) but pass the SAME unfiltered `scanBinds`. -/
def eqHoistHeads (binds : CoreProgram) (scanBinds : CoreProgram)
    (derivedEq : List String) (handwrittenOrdHeads : List String) (fuel : Nat)
    : List String :=
  let eqOps : List Name := ["GHC.Classes.==", "GHC.Classes./="]
  -- The body comes from `scanBinds`, the decision that there IS one from `binds`:
  -- a head with no kept `$ccompare` is not on the hand-written route at all.
  let bodyOf (method : Name) (h : String) : Option Expr := do
    let _ ← findClassMethodBind binds method h
    (findClassMethodBind scanBinds method h).map (·.2)
  let cmpBodies := handwrittenOrdHeads.filterMap (bodyOf "$ccompare" ·)
  -- `==` only: retargeting is what the hoist buys such a head, and `retargetSelfEq`
  -- redirects `==` alone (the def being emitted IS `==`). A `/=`-at-own-head body
  -- gains nothing from moving, and is reported instead — `hoistedEqSelfResiduals`.
  let selfSeed := selfEqHeads binds scanBinds derivedEq ["GHC.Classes.=="]
  let rec grow (fuel : Nat) (acc : List String) : List String :=
    match fuel with
    | 0        => acc
    | fuel + 1 =>
      let bodies := cmpBodies ++ acc.filterMap fun h =>
        if (hwEqBindAt binds derivedEq h).isSome then bodyOf "$c==" h else none
      let next := ((bodies.flatMap (opArgTypes eqOps) ++ selfSeed).filter
                    fun h => (hwEqBindAt binds derivedEq h).isSome).eraseDups
      if next == acc then acc else grow fuel next
  grow fuel selfSeed

/-- Rewrite a hand-written `$c==` body's SELF-RECURSIVE `==` calls — `==`
    instantiated at `headTy`, which PRE-`Lower` is `== @T $fEqT a b` — to
    reference `self` (the `$c==` binder itself), so `refId`/`defNameId` spell it
    `localId self`: the very def this body becomes.

    WHY THIS IS NOT `retargetSelfCompare` WITH A DIFFERENT NAME. That function's
    safety argument is "both misfire directions are LOUD", and the FAILURE-to-
    retarget half of it does not transfer. `eqHoistHeads` splices the `$c==` def
    ahead of `instance : BEq T` (it has to — the instance references the def), so a
    self-`==` left in place resolves against the only `BEq T` in scope there:
    core's `instBEqOfDecidableEq`, off the `deriving DecidableEq` that
    `emitDataDecl`'s `handwrittenOrd` flag adds. That is STRUCTURAL equality, with
    no diagnostic — measured on `OrdSectionOrder.hs`'s parity-`Eq` list `PList`
    (section (7); `PCons a as == PCons b bs` tests `a mod 2 == b mod 2 && as == bs`),
    which was correct at depth 1 and silently structural at depth ≥ 2:
    `decide` PROVED `plistEq (PCons 1 (PCons 2 PNil)) (PCons 3 (PCons 4 PNil)) =
    true` FALSE. So this retarget must be RELIABLE, not
    merely loud-on-misfire, which is why it is keyed on the type application
    (`classOpHeadTy` — exact for any argument shape) and runs PRE-`Lower`, where
    that argument still exists. The over-retarget half does still fail loudly: a
    call at some other type becomes `self` applied to values of that type, an
    argument-type mismatch at `lake build`.

    PRODUCES A PRE-`Lower` EXPRESSION. The replaced spine keeps the arguments it
    had, type application and dictionary included, applied to `self` instead of to
    the class op; `Lower.lowerExpr` then erases those two exactly as it would have
    erased them from the original spine, leaving `self a b`. The caller must lower
    the result (`emitFullProgram`'s `eqBlockFor` does) — emitting it unlowered
    would apply the def to a type and a dictionary.

    Only `==` is retargeted, never `/=`: `self` IS `==`, and `$c/=` is not spliced.
    A `/=` at the own head inside a hoisted `$c==` body is therefore a residual,
    and `hoistedEqSelfResiduals` reports it by name. -/
partial def retargetSelfEq (headTy : String) (self : Var) : Expr → Expr
  | .cast e           => .cast (retargetSelfEq headTy self e)
  | .tick e           => .tick (retargetSelfEq headTy self e)
  | .lam v b          => .lam v (retargetSelfEq headTy self b)
  | .let_ bnd b       =>
    let bnd' := match bnd with
      | .nonRec v e => Bind.nonRec v (retargetSelfEq headTy self e)
      | .rec_ ps    => Bind.rec_ (ps.map fun (v, e) => (v, retargetSelfEq headTy self e))
    .let_ bnd' (retargetSelfEq headTy self b)
  | .case_ s bv ty alts =>
    .case_ (retargetSelfEq headTy self s) bv ty
      (alts.map fun (.mk c bs r) => Alt.mk c bs (retargetSelfEq headTy self r))
  | e@(.app f a)      =>
    let (h, as) := spineOf e
    match h with
    | .var op =>
      if op.name == "GHC.Classes.==" && classOpHeadTy as == some headTy then
        (as.map (retargetSelfEq headTy self)).foldl Expr.app (.var self)
      else
        .app (retargetSelfEq headTy self f) (retargetSelfEq headTy self a)
    | _ => .app (retargetSelfEq headTy self f) (retargetSelfEq headTy self a)
  | e                 => e

/-- `(type, op)` for every `==`/`/=` a hand-written `$c==` body still applies at its
    OWN head after `retargetSelfEq` has run. Two shapes reach it:

    * `/=` at the own head, which `retargetSelfEq` deliberately does not touch
      (`self` is `==`, and `$c/=` is not spliced);
    * an `==` the retarget could not establish a head type for — no type argument
      and no bare-`Var` argument either, which no observed dump produces but which
      would otherwise be silent.

    Either one resolves against whatever `BEq` the data block already has, since
    `instance : BEq T` necessarily FOLLOWS the def it points at. On a head that
    carries `deriving … DecidableEq` — every `handwrittenOrd`/`derivedOrd` head —
    that is core's `instBEqOfDecidableEq`, i.e. STRUCTURAL equality with no
    diagnostic; on a head without it the same call is a loud `failed to synthesize
    BEq T`. This makes the silent case LOUD at the transpiler, and says which of
    the two the reader is looking at.

    THE SCANNED SET is the hoisted heads UNION `selfEqHeads` for both ops, not the
    hoisted set alone. `eqHoistHeads` seeds on `==`-at-own-head, so every
    retargetable head is hoisted and covered either way; the union is what adds a
    head whose only own-head op is `/=`, which the hoist deliberately leaves where
    it is. -/
def hoistedEqSelfResiduals (p : Program) : List (Name × Name) :=
  let derivedEq := derivedEqTypes p.binds
  let hwOrd := (p.instances.filter (·.className == "Ord")).filterMap fun i =>
    let h := i.headTypes.map emitType |> String.intercalate " "
    match ordRoute p.binds h with
    | .handwritten _ _ => some h
    | _                => none
  let eqOps : List Name := ["GHC.Classes.==", "GHC.Classes./="]
  let scanned :=
    (eqHoistHeads p.binds p.rawBinds derivedEq hwOrd (p.typeDecls.length + 1)
      ++ selfEqHeads p.binds p.rawBinds derivedEq eqOps).eraseDups
  let nameOfHead (h : String) : Name :=
    match p.typeDecls.find? (fun d => emitType (.tyCon d.name []) == h) with
    | some d => d.name
    | none   => h
  scanned.flatMap fun h =>
    match findClassMethodBind p.rawBinds "$c==" h with
    | none        => []
    | some (v, e) =>
      let e' := retargetSelfEq h v e
      [("GHC.Classes.==", "=="), ("GHC.Classes./=", "/=")].filterMap fun (op, shown) =>
        if (opArgTypes [op] e').contains h then some (nameOfHead h, shown) else none

/-- The warning for one `hoistedEqSelfResiduals` entry. -/
def hoistedEqSelfResidualWarning (head op : Name) : String :=
  s!"hand-written `Eq {head}` applies `{op}` at `{head}` inside its own `==` body, and\n" ++
  s!"  that call is NOT redirected to the definition being emitted. That definition\n" ++
  s!"  necessarily PRECEDES `instance : BEq {head}` (the instance references it), so\n" ++
  s!"  the call resolves against whatever `BEq {head}` the data block already has:\n" ++
  s!"  core's `instBEqOfDecidableEq` if `{head}` carries `deriving … DecidableEq`\n" ++
  s!"  (every hand-written- or derived-`Ord` head does) — STRUCTURAL equality, not\n" ++
  s!"  `{head}`'s own — and otherwise a loud `failed to synthesize BEq {head}`.\n" ++
  s!"  A self-recursive `==` IS redirected (`retargetSelfEq`); `/=` is not, because\n" ++
  s!"  the def being emitted is `==`.\n" ++
  s!"  Fix: express the `{op}` as `not (… == …)`, or move the test out of the\n" ++
  s!"  instance body into a top-level function that `compare` calls instead."

/-- Names of every `Var` an expression references. -/
private partial def collectVarNames : Expr → List Name
  | .var v            => [v.name]
  | .app f a          => collectVarNames f ++ collectVarNames a
  | .lam _ b          => collectVarNames b
  | .cast e           => collectVarNames e
  | .tick e           => collectVarNames e
  | .let_ bnd b       =>
    (match bnd with
     | .nonRec _ e => collectVarNames e
     | .rec_ ps    => ps.flatMap (fun p => collectVarNames p.2))
      ++ collectVarNames b
  | .case_ s _ _ alts =>
    collectVarNames s ++ alts.flatMap (fun (.mk _ _ r) => collectVarNames r)
  | _                 => []

/-- `(head, function)` for every USER TOP-LEVEL function a SPLICED body calls —
    a hand-written `compare`, and a hand-written `$c==` hoisted ahead of one
    (`eqHoistHeads`). Those calls are FORWARD references and fail at `lake build`:
    the spliced blocks live in the data block (see `emitFullProgram`) and user binds
    are the last section, so nothing the user wrote at the top level is in scope
    inside either body.

    BOTH body kinds, because both are spliced. The `Eq` half is reachable from
    ordinary Haskell — `instance Eq F where F a b == F c d = key a == key c`
    alongside a `compare` that tests `x == y` hoists that `$c==` — and reporting
    only the `compare` half would leave a comment claiming coverage this does not
    have.

    Reported rather than fixed. Hoisting the callee would mean moving user binds
    into the data block too, and a bind can reference anything — its own type's
    instances included — so the hoist has no order that is right in general; the
    honest landing is a named diagnostic. The pre-M3T6 behaviour here was not
    "working" either: it DROPPED the hand-written `compare` and installed Lean's
    structural order silently, which is the silent-wrong this task exists to remove.

    The `$`-prefixed names are excluded because they are GHC plumbing, not user
    functions; a `$c`/`$dm` reference out of a compare body is a different (and so
    far unobserved) shape and would be loud on its own. -/
def ordForwardRefs (p : Program) : List (Name × Name) :=
  let topUser : List Name := (collectTopNames p.binds).filter fun n => !n.startsWith "$"
  let derivedEq := derivedEqTypes p.binds
  let hwOrd := (p.instances.filter (·.className == "Ord")).filterMap fun i =>
    let h := i.headTypes.map emitType |> String.intercalate " "
    match ordRoute p.binds h with
    | .handwritten _ _ => some (headTypeNames i, h)
    | _                => none
  let hoisted := eqHoistHeads p.binds p.rawBinds derivedEq (hwOrd.map (·.2))
                   (p.typeDecls.length + 1)
  -- The reported head is the TYPE the body belongs to, so an `Eq` hoisted at a
  -- different head than the `Ord` that needed it is named by its own type.
  let nameOfHead (h : String) : Name :=
    match p.typeDecls.find? (fun d => emitType (.tyCon d.name []) == h) with
    | some d => d.name
    | none   => h
  let bodies : List (Name × Expr) :=
    hwOrd.filterMap (fun (n, h) => (findClassMethodBind p.binds "$ccompare" h).map ((n, ·.2)))
      ++ hoisted.filterMap fun h => (hwEqBindAt p.binds derivedEq h).map ((nameOfHead h, ·.2))
  bodies.flatMap fun (n, e) =>
    (dedup (collectVarNames e)).filterMap fun v =>
      if topUser.contains v then some (n, v) else none

/-- The warning for one `ordForwardRefs` entry. -/
def ordForwardRefWarning (head fn : Name) : String :=
  s!"hand-written `compare` for `{head}` calls the top-level function `{fn}`, which\n" ++
  s!"  is emitted AFTER it: the `Ord {head}` block is spliced into the data block so\n" ++
  s!"  that types deriving `Ord` from `{head}`, and class-body defaults ordering\n" ++
  s!"  `{head}`s, can see it. `lake build` will report `unknown identifier {fn}` — the\n" ++
  s!"  reference is emitted by its real name, so the failure names the cause.\n" ++
  s!"  NOTHING structural is substituted (that substitution, which is what this\n" ++
  s!"  transpiler did before M3 Task 6, made the module compile with Lean's own\n" ++
  s!"  order instead of `{head}`'s — silently).\n" ++
  s!"  Fix: inline `{fn}`'s body into the `compare` definition, or move the ordering\n" ++
  s!"  logic into `{fn}` and make `compare` the only thing that mentions the fields."

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
    -- Three routes, decided by `ordRoute` (see its section header):
    --
    -- * DERIVED — `deriving Ord` + companions in the data block (`emitDataDecl`),
    --   which is also what puts them ahead of every bind using `≤`/`<`/`min`/`max`.
    --   Nothing here, and the untranslatable `$ccompare`/`$c<`/… defs are
    --   suppressed in `emitFullProgram`.
    -- * HAND-WRITTEN — the user's `compare`, wired here, with the same four
    --   companions derived from it. This string does NOT land in the instance
    --   section: `emitFullProgram` SPLICES it into the data block, immediately
    --   after the `$ccompare` def it points at and next to that type's own
    --   `inductive` (`ordBlockFor`/`blocksFor`; the sort widened by `ordRefDeps`
    --   is what puts the pieces in a workable order). Four measured layouts
    --   failed before that — a derived-`Ord` type with a hand-written-`Ord`
    --   FIELD, a class-body default using `min` at this head, a compare body
    --   ordering a non-field type, and a compare body calling `==` at a
    --   hand-written-`Eq` head (the silent one). See `emitFullProgram`'s "WHY THE
    --   DATA BLOCK" comment and the `M3 Task 6` block in `Tests/Unit.lean`.
    -- * UNSUPPORTED — no `Ord` at all; `Main.lean` warns and every use is loud.
    match ordRoute binds tyStr with
    | .derived            => none
    | .unsupported        => none
    | .handwritten cmpRef _ =>
      some (s!"instance : Ord {tyStr} where\n  compare := {cmpRef}\n\n"
              ++ ordCompanionInsts tyStr)
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

  1. `resolveUserTypes`      opaque local tycon → bare       — bodies, inductives +
                                                               class decls, spliced
                                                               Ord/Eq blocks, spec
                                                               text (4 sites)
  2. `resolveNewtypes`       newtype → underlying type       — after 1, before 3,
                                                               SAME 4 sites
  3. `resolveUserCtors`      ctor in application position → `T.C`
                                                             — bodies, spliced
                                                               Ord/Eq blocks, spec
                                                               text; NEVER the
                                                               inductives
  4. `resolveExternalTypes`  remaining opaque → `M.T`        — whole output, last;
                                                               requires 1 to have
                                                               run on EVERY section

Pass 1's four sites are, concretely: `emitFullProgram`'s `bodyResolved`
(method defs + instances + user binds), its `res12` over each `inductive` and each
class decl, its `resBody` over each spliced `Ord`/`Eq` block, and `resolveSpecText`
(user `@lean` theorem text). Pass 3 runs at the first, third and fourth of those;
pass 4 covers the whole joined output rather than any one section.

THE SPLICED BLOCKS ARE WHY PASS 3'S SITE LIST IS NOT SIMPLY "not the data block".
A hand-written `Ord`'s `$ccompare` def, and the hand-written `BEq` a compare body
may need before it, are emitted INSIDE the data block — between the `inductive`s,
next to their own type (see `emitFullProgram` for the four measured reasons). They
pattern-match on constructors and so need pass 3, which must never touch an
`inductive`'s own `| Ctor ` lines. Both hold only because each piece is resolved
SEPARATELY, with its own pipeline, and the already-resolved strings are then
joined. That is equivalent to resolving the join: every needle of passes 1–3 is a
single identifier occurrence, so none can span the `\n\n` between two pieces.

Pass 4 must run last, and pass 1 must have reached every section before it, or a
local type still spelled opaque gets rewritten to `M.T` for its OWN module `M`.

PASS 3 IS ALSO THE ONLY PASS WHOSE NEEDLES ARE BARE IDENTIFIERS — 1, 2 and 4 all
match `(GHCCore.tyConOpaque "X")`, whose own quotes cannot occur unescaped inside
a Lean string literal — so it is the only one that needs to know where the string
literals are. See "Literal-aware scanning" below for the scan and the audit.

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
spelling: `derivedEqTypes`/`ordRoute`/`findClassMethod` keys are built before any
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
* **Ord relocates too, and it did not always.** `newtype Coin = Coin Int` +
  `instance Ord Coin where compare (Coin a) (Coin b) = compare b a`. When this
  guard was written the reversed `compare` VANISHED: the head matched the old
  instance-existence `ordTypes`, so `isSuppressedMethod` dropped every `$c` method
  while the newtype was filtered out of `datas` and got no `deriving Ord` either,
  and Lean's own `Int` order took over with zero diagnostics. Since M3 Task 6 the
  same input takes the `ordRoute` HAND-WRITTEN route, and the failure mode becomes
  RELOCATION, exactly like `Eq`'s. MEASURED by handing that Program to
  `emitFullProgram` directly (the refusal lives in `Main.lean`, upstream of it):

      def _dollar_ccompare_42 : (Int → (Int → Ordering)) := compare
      instance : Ord Int where
        compare := _dollar_ccompare_42
      instance : LE Int := leOfOrd
      instance : LT Int := ltOfOrd
      instance : Min Int := minOfLe
      instance : Max Int := maxOfLe

  — the reversed order AND its four companions land on `Int` inside the module
  namespace, so every `<`/`≤`/`min`/`max` on `Int` there silently reverses. The
  refusal below is what keeps either form from happening; the change of failure
  mode is recorded because the guard's justification must not read as stale.

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

/-! ## Unrepresentable string literals

    THE SOUNDNESS CORE OF M4 TASK 2. Mapping `unpackCString#` turns a string
    literal from a loud unknown identifier into a value Lean believes, so any
    literal whose bytes did not survive the trip is no longer merely wrong — it is
    SILENTLY wrong: wrong `length`, wrong content, compiles fine.

    GHC writes literals in MODIFIED UTF-8, which deviates from the standard in
    exactly two ways (`utf8EncodeChar`, GHC 9.2.7): the overlong NUL `C0 80`, and
    3-byte encodings of lone surrogates. It is NOT CESU-8 — a supplementary
    character gets standard 4-byte UTF-8 (measured: `"\128169"` decodes to `💩`
    correctly) — so this must not become a blanket refusal of non-ASCII.

    THE SPLIT (this is why the coarse "any lossy decode" predicate was not the
    refusal criterion):
    * U+0000 IS A LEGAL LEAN `Char`. The shim now decodes `C0 80` back to a real
      NUL (`undoOverlongNul`), so `"a\0b"` transpiles FAITHFULLY as three
      characters. Refusing it would have declined Haskell that has a perfect Lean
      image, and it would have done so permanently.
    * U+D800–DFFF IS NOT A LEAN `Char` AT ALL (plan correction 3: Haskell's `Char`
      spans [0,0x10FFFF] including the 2048 surrogates; Lean's excludes them). No
      decoder can help, so this is the residue that must REFUSE.

    WHY THE FLAG COMES FROM THE SHIM. The predicate is `encodeUtf8 (decodeUtf8With
    lenientDecode bs) /= bs` over the NUL-repaired bytes — and the BYTES ARE GONE
    after JSON, so Lean cannot recompute it. The shim therefore emits
    `"unrepresentable": "<hex>"` and this pass reads it. And the refusal lives
    HERE rather than as a `die` in the shim because the shim cannot know whether a
    literal reaches emission: a shim-level death would crash modules whose only
    such literal sits in a dropped `$tr`/`$cshowsPrec`/error-collapsed bind, i.e.
    modules that transpile fine today. `Ratio` is that module — 54 `LitString`s,
    9 of them in real user binds' `error` messages — and it must stay green.

    SCOPE, stated honestly. `Main.lean` runs this over the FILTERED, post-`Lower`
    binds, so junk binds cannot trigger it. Binds dropped LATER, at emission (the
    `error`→`default` collapse discards a bottom's whole application, message
    included), are still in the walked set: a lone surrogate inside an `error`
    string would refuse a module that would have emitted fine. That is a
    conservative refusal — loud, never silent-wrong — and it is preferred to
    mirroring the collapse here, which would duplicate emission logic in a
    validator and could then disagree with it. -/

/-- Every `.litStringUnrepresentable` hex payload in an expression, including
    literals in PATTERN position (a `LitAlt` alternative) — `emitLiteralPattern`
    would put the same unrepresentable payload in the output. -/
private partial def unrepStringsInExpr : Expr → List String
  | .lit (.litStringUnrepresentable hex) => [hex]
  | .app f a          => unrepStringsInExpr f ++ unrepStringsInExpr a
  | .lam _ b          => unrepStringsInExpr b
  | .cast e           => unrepStringsInExpr e
  | .tick e           => unrepStringsInExpr e
  | .let_ bnd b       =>
    (match bnd with
     | .nonRec _ e => unrepStringsInExpr e
     | .rec_ ps    => ps.flatMap (fun p => unrepStringsInExpr p.2))
      ++ unrepStringsInExpr b
  | .case_ scr _ _ alts =>
    unrepStringsInExpr scr ++
      alts.flatMap (fun (.mk con _ rhs) =>
        (match con with
         | .litAlt (.litStringUnrepresentable hex) => [hex]
         | _ => []) ++ unrepStringsInExpr rhs)
  | _                 => []

/-- `(owner bind, hex bytes)` for every string literal with no faithful Lean
    image. The owner is the TOP-LEVEL bind the literal sits under, which is what
    the refusal names: it is the only thing that points a user at their source. -/
def unrepresentableStringLiterals (p : Program) : List (Name × String) :=
  p.binds.flatMap fun b =>
    match b with
    | .nonRec v e => (unrepStringsInExpr e).map fun h => (v.name, h)
    | .rec_ ps    => ps.flatMap fun (v, e) => (unrepStringsInExpr e).map fun h => (v.name, h)

/-- The refusal message for one `unrepresentableStringLiterals` pair. -/
def unrepresentableStringLiteralError (owner : Name) (hex : String) : String :=
  s!"string literal not representable: bytes `{hex}` in bind `{owner}`\n" ++
  s!"  GHC writes string literals in MODIFIED UTF-8, and these bytes decode to a\n" ++
  s!"  LONE SURROGATE (U+D800–DFFF) or are not valid UTF-8 even after the overlong\n" ++
  s!"  NUL (`C0 80`) is repaired. A Haskell `Char` spans [0,0x10FFFF] INCLUDING the\n" ++
  s!"  2048 surrogates; a Lean `Char` excludes them, so this literal has no Lean\n" ++
  s!"  value at all — not a different one. Emitting it would put U+FFFD replacement\n" ++
  s!"  characters in the output: a plausible-looking string of the wrong length and\n" ++
  s!"  the wrong content, which compiles. So transpilation is refused instead.\n" ++
  s!"  Remedy: remove the surrogate from the literal (`\\55296` and friends), or\n" ++
  s!"  represent the text as the byte/code-point list you actually mean.\n" ++
  s!"  Note: NUL is NOT this case — `\"a\\0b\"` transpiles faithfully as 3 chars."

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

/-! ### Literal-aware scanning (pass 3's one silent hole, closed)

M4 TASK 3. Pass 3 is the ONLY pass in the pipeline above whose needles are BARE
identifiers. Passes 1, 2 and 4 all key off `(GHCCore.tyConOpaque "X")`, and that
needle carries its own `"` delimiters: a Lean string literal spells an inner
quote `\"`, so the needle cannot match inside one. They are self-protecting by
construction (audited, M4 Task 3 — the only other `String.replace` in this file is
the `{t}` template fill in `Maps`-driven signature emission, which rewrites map
TEMPLATES, not emitted source). Pass 3 had no such protection: it is a plain text
rewrite, so a ctor name followed by an argument INSIDE a string literal was
rewritten too. That was documented as a hedge while its premise held — no Haskell
string literal could reach the emitter at all — and M4 Task 2 destroyed the
premise: `"Point (1)"` emitted as `"Point.Point (1)".toList`, type-correct,
compiles, SILENTLY WRONG (measured before the fix, `rc=0` on both transpile and
`lake build`).

THE SCANNER (exact state machine; two states, two characters of lookahead):

    OUTSIDE                                    IN-LITERAL
    `"`       → open literal, go IN-LITERAL      `"`     → close, go OUTSIDE
    `\` c     → copy both, stay OUTSIDE          `\` c   → copy both, stay IN
    `'` c `'` → copy all three, stay OUTSIDE     any c   → copy, stay IN
                (only when c ∉ { `\`, `'` } and the
                 opening `'` does not continue an
                 identifier — see `isIdentish`)
    any c     → copy, stay OUTSIDE

Why each arm exists:

* `\` c IN-LITERAL is what makes Task 2's escaping safe, in BOTH of its
  directions: `"say \"hi\""` must not end at the first `\"`, and `"x\\"` must end
  at the quote that follows the escaped BACKSLASH rather than reading `\"` as an
  escape and running past the end of the literal. Quote-counting gets the first
  wrong; quote-counting plus a naive "skip the char after a backslash" gets the
  second wrong. The state machine tracks escape state, so both hold.
* `\` c OUTSIDE exists for exactly one shape, and it is emitter-produced: a
  double-quote CHAR literal is spelled `'\"'` (`escapeLitChar` escapes both quote
  characters in both literal positions), and that `"` must not open a string.
* The `'` c `'` arm covers the HAND-WRITTEN spelling of that same hazard.
  `['"']` and `['s', 'a', 'y', ' ', '"', …]` are real corpus text
  (`Generated/StringBasics.lean:44,48`), where a raw `"` sits inside a char
  literal. It is deliberately NOT a third scanner state: Lean allows `'` inside
  identifiers (`x'`, `ds'`), so treating every apostrophe as a delimiter would
  desync the scanner on ordinary code — the exact mistake this arm is shaped to
  avoid. Requiring a non-identifier character BEFORE the quote and a closing
  quote exactly two characters later makes it fire on char literals and never on
  `x'`. An ESCAPED char literal (`'\n'`, `'\x00'`, `'\''`) needs no arm at all:
  the OUTSIDE `\` c rule steps over the payload, and the bare quotes around it
  then change no state.

BOTH RESIDUAL DEGRADATIONS ARE FAIL-LOUD, which is why this shape was chosen over
a full Lean lexer. An UNTERMINATED literal classifies the tail as literal, and a
spurious literal opened by a raw `"` that no arm above covers classifies the text
up to the next quote as literal — in both cases rewrites are SKIPPED, and a
skipped ctor rewrite is Lean's "function expected at Point", never a wrong value.
No arm can cause a rewrite the literal-unaware code would not have made, so
nothing here is silent.

REACHABILITY OF THOSE TWO CASES, enumerated rather than assumed. Every site in
this file that writes a `"` into the OUTPUT is one of six: `escapeStringLit` and
`escapeCharLit` (balanced, payload escaped — these are the literals this scan is
about), and four RAW interpolations whose payload is a name, a hex string or a
label: `(GHCCore.tyConOpaque "T")`, `(GHCCore.unrepresentableStringLiteral "hex")`
(unreachable post-refusal), `GHCCore.foreignLabel "l"` and `emitType`'s
`.tyLit (.str s)`. All six write BALANCED delimiters, so emitter output cannot
desync the scanner. The last two interpolate without escaping, so a payload
CONTAINING a raw quote or a trailing backslash would — but that same payload is a
Lean SYNTAX error on the line that carries it, so the failure is loud before the
scan matters, and both are unobserved in every generated file in the corpus.
Hand-written spec text is copied verbatim and is the only other source of either
case; it is resolved per `@lean` block, so a desync cannot cross blocks.
-/

/-- The scanner of the section header. `inLit` is the state, `acc` the segment
    built so far; a state change flushes `acc` and starts a fresh segment.
    Structural on the character list (NOT `partial`: the `#guard`s pinning it
    need kernel reduction). -/
private def litScan : List Char → Bool → String → List (Bool × String)
  | [], inLit, acc => [(inLit, acc)]
  -- IN-LITERAL: an escape pair is copied whole, so `\"` does not close and the
  -- `"` after a `\\` is not mistaken for an escaped quote.
  | '\\' :: c :: rest, true,  acc => litScan rest true  ((acc.push '\\').push c)
  | '"'  :: rest,       true,  acc => (true, acc.push '"') :: litScan rest false ""
  -- OUTSIDE: a quote opens a literal.
  | '"'  :: rest,       false, acc => (false, acc) :: litScan rest true "\""
  -- OUTSIDE: an unescaped one-character CHAR literal, but only where the opening
  -- quote cannot be an identifier's trailing apostrophe (`x'`).
  | '\'' :: c :: '\'' :: rest, false, acc =>
    if (acc.isEmpty || !isIdentish acc.back) && c != '\\' && c != '\'' then
      litScan rest false ((((acc.push '\'').push c).push '\''))
    else
      litScan (c :: '\'' :: rest) false (acc.push '\'')
  -- OUTSIDE: an escape pair here too — the emitter spells a double-quote char
  -- literal `'\"'`, whose quote must not open a string literal.
  | '\\' :: c :: rest, false, acc => litScan rest false ((acc.push '\\').push c)
  | c :: rest,          inLit, acc => litScan rest inLit (acc.push c)

/-- `src` split into alternating CODE (`false`) and STRING-LITERAL (`true`)
    segments in source order, the quotes belonging to the literal segment.
    Concatenating the second components reproduces `src` exactly (pinned in
    `Tests/Unit.lean`). See the section header for the state machine. -/
def litSegments (src : String) : List (Bool × String) :=
  litScan src.data false ""

/-- Apply `f` to every CODE segment of `src`, copying string literals verbatim.
    THE guard on every bare-identifier rewrite: `f` never sees literal content,
    so it cannot rewrite it.

    Behaviour-preserving outside literals, and the reason is worth stating rather
    than assuming. No needle of pass 3 contains a `"` (`| C `, `(C)`, ` C (`,
    `(C (`), so no legitimate match can span a code/literal boundary; and
    `replaceCtorAppsCode`'s boundary tests degenerate at a segment edge exactly as
    they did at a quote character — at a segment START `acc.isEmpty` makes
    `leftOK` true, which is what a preceding `"` (not `isIdentish`) gave; at a
    segment END the following text is empty, making `appOK` false, which is what a
    following `"` (not `isArgStart`) gave. -/
def mapOutsideLiterals (f : String → String) (src : String) : String :=
  String.join ((litSegments src).map fun (isLit, s) => if isLit then s else f s)

/-- THE RAW, LITERAL-UNAWARE rewrite. NOT for callers — use `replaceCtorApps`,
    which is this restricted to code segments. It stays public for one reason: the
    tests pin the silent-wrong behaviour it still has (the literal `"Point (1)"`
    becoming `"Point.Point (1)"`) directly against the wrapper's, so the fix is
    visible as a contrast rather than asserted.

    Boundary-aware rewrite of `bare` → `qual` at every APPLICATION-position
    occurrence: identifier boundaries on both sides (so `mkPoint` and an
    already-qualified `Point.Point` are left alone) and an argument following
    (`isArgStart`). This is what covers a ctor applied to a *literal*
    argument — `Rect (Point 0 0) 1 1` — which the fixed needles in
    `resolveUserCtors` cannot express: they all require a `(` immediately
    after the ctor name. -/
def replaceCtorAppsCode (bare qual : String) (src : String) : String :=
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

/-- `replaceCtorAppsCode` over the CODE segments of `src` only — the same
    application-position rewrite, with string-literal content left alone. THE name
    every caller uses: reaching for the raw one reintroduces the silent hole
    documented above. -/
def replaceCtorApps (bare qual : String) (src : String) : String :=
  mapOutsideLiterals (replaceCtorAppsCode bare qual) src

/-- Qualify user-defined data constructors in any position where Lean's
    elaborator would otherwise be ambiguous (type vs. ctor under the same
    name). The recognised call-shapes are:

      *  `| Ctor `                              ← alt-pattern
      *  `(Ctor)`                               ← App in transpiler-emitted style
      *  `Ctor (` (preceded by whitespace)      ← App in user `[lean| … |]` spec
      *  `Ctor <arg>` at identifier boundaries  ← App to a literal/bracketed
                                                  argument (`replaceCtorApps`)

    Type annotations like `(x : T)` or `→ T →` match none of these, so they
    remain `T` and resolve to the type.

    ALL FIVE REWRITES (the four needles and `replaceCtorApps`) see only the CODE
    segments of `mapOutsideLiterals`: a ctor name inside a Lean string literal is
    left alone, because rewriting it changes a VALUE rather than a name. -/
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
      -- Both halves skip string-literal content (`mapOutsideLiterals`): the four
      -- needles here, and `replaceCtorApps` internally.
      let s := mapOutsideLiterals
        (fun code => rules.foldl (init := code) fun c (needle, repl) =>
          c.replace needle repl) s
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

/-- Local type names a BODY mentions, via the type of every `Var` it references
    and of every `case` binder. Deduplicated, self-reference dropped (same
    convention as `dataDeclDeps`, whose result set this widens).

    This is the `Ord` section's real ordering requirement and the reason
    `sortDataDecls` takes `extraDeps`: a hand-written `compare` at `B` whose body
    calls `compare` at `A` needs `instance : Ord A` already emitted, and `A` need
    not be a FIELD of `B` — the field graph has no edge there at all. Measured:
    `instance Ord B where compare (B x) (B y) = compare (A x) (A y)` emitted
    `failed to synthesize Ord A` whenever the dump put `B` first.

    It over-approximates on purpose — a body that merely PROJECTS an `A` gets the
    same edge as one that orders two of them, and a `wild` `case` binder's recorded
    type is not always the scrutinee's (see `firstVarArgTy`), so an unrelated decl
    can pick up an edge too. An extra edge only constrains the order further, and
    the one thing it can do is turn a would-be pair of independent decls into a
    cycle, which `sortDataDecls` already appends in dump order and leaves loud at
    `lake build`. That is why the over-approximation is affordable HERE and not in
    `eqHoistHeads`, which moves a whole body and so reads only the first argument.

    TWO channels, and BOTH are needed. Binder/`Var` types catch a value of `A`
    that arrives as an argument or a `case` binder — the nested-field shape. But a
    DATA CONSTRUCTOR `Var` carries no type at all: the shim types it `_Unknown`
    (measured — `compare (A x) (A y)` dumps `Var A :: TyCon _Unknown`), so
    `compare (A x) (A y)` would report NO dependency on `A` and the reverse-order
    dump emitted `unknown identifier A.A`. `ctorOwner` closes that: a ctor
    occurrence, in a `Var` or in an alt pattern, names its own type. -/
partial def localTypesInExpr (localNames : List Name) (ctorOwner : Name → Option Name)
    (self : Name) : Expr → List Name :=
  let keep (t : GHCType) : List Name :=
    (tyConNames t).filter fun n => n != self && localNames.contains n
  let owner (n : Name) : List Name :=
    match ctorOwner n with
    | some d => if d != self && localNames.contains d then [d] else []
    | none   => []
  let altOwner : AltCon → List Name
    | .dataCon c => owner c
    | _          => []
  let rec go : Expr → List Name
    | .var v            => keep v.ty ++ owner v.name
    | .lit _            => []
    | .type_ t          => keep t
    | .coercion         => []
    | .cast e           => go e
    | .tick e           => go e
    | .lam v b          => keep v.ty ++ go b
    | .let_ bnd b       =>
      (match bnd with
       | .nonRec v e => keep v.ty ++ go e
       | .rec_ ps    => ps.flatMap (fun p => keep p.1.ty ++ go p.2))
        ++ go b
    | .app f a          => go f ++ go a
    | .case_ s bv _ alts =>
      go s ++ keep bv.ty
        ++ alts.flatMap (fun (.mk c bs r) =>
             altOwner c ++ bs.flatMap (fun b => keep b.ty) ++ go r)
  fun e => dedup (go e)

/-- Order data decls so that a decl using another local type as a field type is
    emitted AFTER it. Lean has no forward references and the decl-plugin's
    `tcg_tcs` dump order is not dependency order, so `inductive Rect` would
    otherwise reference a not-yet-declared `Point`.

    `extraDeps` WIDENS the edge set with dependencies the field graph cannot see.
    Its one caller passes the `Ord` section's compare-body reference graph
    (`localTypesInExpr`), because that section is emitted INSIDE this order — each
    type's `Ord` block sits next to its own `inductive` — so a reference out of one
    compare body into another type's `Ord` is an ordering constraint on the DATA
    decls. Defaulted to the empty graph so every other call site is unchanged.

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
def sortDataDecls (ds : List DataDecl) (extraDeps : Name → List Name := fun _ => []) : List DataDecl :=
  let names := ds.map (·.name)
  let depsOf (d : DataDecl) : List Name :=
    dataDeclDeps names d ++ ((extraDeps d.name).filter fun n => n != d.name && names.contains n)
  let rec go (fuel : Nat) (pending : List DataDecl) (placed : List Name)
      (acc : List DataDecl) : List DataDecl :=
    match fuel, pending with
    | _, []            => acc.reverse
    | 0, pending       => acc.reverse ++ pending
    | fuel + 1, pending =>
      match pending.find? (fun d => (depsOf d).all (fun n => placed.contains n)) with
      | some d => go fuel (pending.filter (·.name != d.name)) (d.name :: placed) (d :: acc)
      | none   => acc.reverse ++ pending
  let result := go ds.length ds [] []
  -- Totality fallback: any length change ⇒ hand back the input untouched.
  if result.length != ds.length then ds else result

/-- Order class decls so that a class comes AFTER every LOCAL class it extends.
    `sortDataDecls`' idiom, with `supers ∩ local class names` as the dependency
    edge — `extends Sized a` is a reference to a name Lean must already know, and
    class order became load-bearing the moment M3 Task 5 started emitting it.

    NECESSARY, not defensive: the decl plugin dumps `tcg_tcs` in REVERSE
    declaration order (`Container` before `Sized` — M3 Task 1's observation 2), so
    any class the reconstruction never sees (no local instance) arrives from
    `mergeClassDecls` child-first.

    STABLE on input with no local supers: `find?` takes the first pending decl
    whose deps are placed, and with no deps that is always the head, so every
    fixture without a superclass keeps its previous byte-for-byte order. Same
    totality fallback and same dead `| 0` arm as `sortDataDecls`; a `supers` CYCLE
    cannot come out of GHC (it rejects them), and if one ever did the remainder is
    appended in dump order and Lean fails loud on the forward `extends`. -/
def sortClassDecls (cs : List ClassDecl) : List ClassDecl :=
  let names := cs.map (·.name)
  let deps (c : ClassDecl) : List Name :=
    c.supers.filter (fun s => s != c.name && names.contains s)
  let rec go (fuel : Nat) (pending : List ClassDecl) (placed : List Name)
      (acc : List ClassDecl) : List ClassDecl :=
    match fuel, pending with
    | _, []             => acc.reverse
    | 0, pending        => acc.reverse ++ pending
    | fuel + 1, pending =>
      match pending.find? (fun c => (deps c).all (fun n => placed.contains n)) with
      | some c => go fuel (pending.filter (·.name != c.name)) (c.name :: placed) (c :: acc)
      | none   => acc.reverse ++ pending
  let result := go cs.length cs [] []
  if result.length != cs.length then cs else result

/-- Order instances so that an instance of a class comes AFTER the instance of
    every LOCAL class it extends, at the SAME head type. `instance : Container Bag`
    omits the `Sized` parent field and Lean fills it from the `Sized Bag` instance
    in scope, so the parent's `instance` block has to be emitted first.

    NECESSARY, and MEASURED rather than argued: the instance channel is in source
    declaration order, so writing `instance Container Bag` above `instance Sized
    Bag` — legal Haskell, and how `examples/haskell/SuperClass.hs` is deliberately
    written since M3 Task 5 — emitted the child first and Lean answered `error:
    Fields missing: `size`` (the flattened-parent form it falls back to when the
    parent instance is not in scope). Loud, but a legal module that failed to
    transpile.

    The dependency edge is only a LOCAL user superclass: a builtin parent
    contributes no `extends` and hence no ordering requirement (its binder recipes
    are constraint-site — see `emitClassDecl`), and a parent from another module is
    not emitted here at all. Heads are compared by their emitted spelling, the same
    key `emitInstanceUser` matches binds with.

    STABLE with no local supers (`find?` takes the pending head when nothing is
    blocked), so every fixture without a class hierarchy keeps its byte-for-byte
    instance order. Same totality fallback and dead `| 0` arm as `sortDataDecls`;
    an instance whose parent instance is MISSING is not blocked by this sort (its
    dependency is unsatisfiable, so `find?` never picks it while others remain and
    the `none` arm appends it) — that stays Lean's `Fields missing` error, which is
    the correct diagnosis. -/
def sortInstances (classes : List ClassDecl) (is : List Instance) : List Instance :=
  let classNames := classes.map (·.name)
  let headStr (i : Instance) : String :=
    i.headTypes.map emitType |> String.intercalate " "
  let key (i : Instance) : Name × String := (i.className, headStr i)
  let deps (i : Instance) : List (Name × String) :=
    match classes.find? (·.name == i.className) with
    | none    => []
    | some cd =>
      (cd.supers.filter classNames.contains).filterMap fun s =>
        if is.any (fun j => j.className == s && headStr j == headStr i)
        then some (s, headStr i) else none
  let rec go (fuel : Nat) (pending : List Instance) (placed : List (Name × String))
      (acc : List Instance) : List Instance :=
    match fuel, pending with
    | _, []             => acc.reverse
    | 0, pending        => acc.reverse ++ pending
    | fuel + 1, pending =>
      match pending.find? (fun i => (deps i).all (fun k => placed.contains k)) with
      | some i => go fuel (pending.filter (fun j => key j != key i)) (key i :: placed) (i :: acc)
      | none   => acc.reverse ++ pending
  let result := go is.length is [] []
  if result.length != is.length then is else result

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
  -- keeps body-translation.
  --
  -- Ord (M3 Task 6): `ordRoute` per instance head, NOT instance existence — that
  -- was the silent-wrong this task closed (every hand-written non-structural `Ord`
  -- was replaced by `deriving Ord`; see the `Ord`-route section header). A DERIVED
  -- head keeps the old treatment: `deriving Ord` + companions in the data block,
  -- every `$c` method suppressed. A HAND-WRITTEN head keeps exactly ONE `$c` bind,
  -- `$ccompare`, which the emitted `instance : Ord T` points at; the rest are
  -- suppressed as before, and are unemittable rather than merely unwanted (they
  -- call the instance's own dictionary — see the section header). An UNSUPPORTED
  -- head keeps nothing.
  let derivedEq : List String := derivedEqTypes p.binds
  let ordHeads : List String :=
    p.instances.filterMap fun i =>
      if i.className == "Ord" then some (i.headTypes.map emitType |> String.intercalate " ") else none
  let derivedOrd     : List String := ordHeads.filter (ordRoute p.binds · == .derived)
  let handwrittenOrd : List String := ordHeads.filter fun h =>
    match ordRoute p.binds h with | .handwritten _ _ => true | _ => false
  let headMatches (v : Var) (s : List String) : Bool :=
    match methodHeadStr v with | some hs => s.contains hs | none => false
  let isSuppressedMethod (v : Var) : Bool :=
    (eqMethodNames.contains v.name  && headMatches v derivedEq)
    || (ordMethodNames.contains v.name && headMatches v ordHeads
        && !(v.name == "$ccompare" && headMatches v handwrittenOrd))
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
  -- Superclass-dependency order (M3 Task 5): `extends Sized a` is a forward
  -- reference unless the parent's `class` block precedes the child's, and the
  -- merged order is the plugin's REVERSE declaration order for any class the
  -- reconstruction never saw. Sorted once, here, so every consumer below (class
  -- emission, `classNames`, the super-binder recipes) sees the same list.
  let userClasses := sortClassDecls (mergeClassDecls p.classDecls coreClasses)
  let classNames := userClasses.map (·.name)
  -- Builtin superclasses cannot ride on `extends` (probes in the M3 Task 5 block
  -- of `Tests/Unit.lean`), so their binder recipes are injected at every
  -- constraint site instead — `Capped a =>` ⇒ `[Ord t] … [Capped t]`.
  let superBinders := classSuperBinders userClasses
  -- Dependency order: a decl with another local type as a field type must come
  -- after it (Lean has no forward references; the dump order is not topological).
  -- Newtypes stay in the SORT's input — chains thread through them transitively
  -- (`Point` → `Wrapper`(newtype) → `Q`), and filtering first loses the edge —
  -- and are dropped only here, at the emission map.
  --
  -- WIDENED by the `Ord` section's compare-body REFERENCE graph (`extraDeps`).
  -- That section is emitted inside this order — each type's `Ord` block sits next
  -- to its own `inductive` — so a compare body at `B` that orders two `A`s makes
  -- `A` an ordering dependency of `B` even though `A` is not a FIELD of `B`. The
  -- field graph is strictly smaller than the requirement; `localTypesInExpr` says
  -- what the extra edges are and why over-approximating them is safe.
  let localTyNames : List Name := p.typeDecls.map (·.name)
  -- Which local decl a data-constructor name belongs to. Over the FULL decl list
  -- (newtypes included), because the sort's input is the full list too.
  let ctorOwner : Name → Option Name := fun c =>
    (p.typeDecls.find? fun d => d.ctors.any (·.name == c)).map (·.name)
  let headStrOf (n : Name) : String := emitType (.tyCon n [])
  let compareBodyAt (h : String) : Option (Var × Expr) :=
    findClassMethodBind keptBinds "$ccompare" h
  -- ASYMMETRY WITH `eqHoistHeads`, deliberate and LOUD where it bites: these
  -- extra ordering edges come from `$ccompare` bodies only. A `$c==` that
  -- `eqHoistHeads` hoists to `X` and whose body references type `Y` therefore
  -- contributes no edge `Y → X`, so `Y`'s `Ord`/`BEq` block can be emitted after
  -- `X`'s — `failed to synthesize Ord Y` at `lake build`, never a wrong answer.
  -- Only reachable when `Y` does not already arrive via a FIELD of `X` (the field
  -- graph `sortDataDecls` starts from), which is why no corpus module hits it.
  -- Widening the scan to hoisted `$c==` bodies is the fix if one ever does; it is
  -- not done here because every such edge would also constrain the order for
  -- bodies that merely PROJECT a `Y`, and an unnecessary edge can only turn an
  -- independent pair into a cycle (see `localTypesInExpr`).
  let ordRefDeps : Name → List Name := fun n =>
    let h := headStrOf n
    if !handwrittenOrd.contains h then []
    else match compareBodyAt h with
      | some (_, e) => localTypesInExpr localTyNames ctorOwner n e
      | none        => []
  let dataOrderDecls := sortDataDecls p.typeDecls ordRefDeps
  -- Paired with the head string, because the `Ord`/`Eq` blocks below are spliced
  -- in next to their own `inductive` and need the same key.
  let datas : List (String × String) :=
    (dataOrderDecls.filter fun d => kept.any (·.name == d.name)).map fun d =>
      let hs := headStrOf d.name
      (hs, emitDataDecl (derivedEq.contains hs) (derivedOrd.contains hs) d
             (handwrittenOrd := handwrittenOrd.contains hs))
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
  -- The arities of the SAME class set `classNames` comes from, so a parent is in
  -- `extends` iff `multiParamParentSupers` does not report it (`classArities`).
  let arities := classArities userClasses
  let classDecls := userClasses.map fun c =>
    let ds := (defaults.filter (·.1 == c.name)).filterMap fun (_, m) =>
      (classDefaultBody methodMap defaultTop p.binds c m).map (fun body => (m, body))
    emitClassDecl ds c classNames arities
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
  -- HAND-WRITTEN `Ord` — and, when a compare body needs it, a hand-written `Eq` —
  -- leave the general method-def / instance sections: they are spliced into the
  -- DATA BLOCK, each type's pieces next to that type's own `inductive`.
  --
  -- WHY THE DATA BLOCK AND NOT A LEADING SECTION OF `bodyRaw` (all measured; the
  -- first release of this task used the leading-section layout and each of these
  -- was a loud regression on ordinary Haskell that the fixture corpus could not
  -- see):
  --
  -- * A `.derived` type with a `.handwritten` type as a FIELD. `data Inner = Inner
  --   Int Int deriving (Eq, Ord)` (2 nullary constructors ⇒ no tag primop ⇒
  --   hand-written route) as the field of `data Quad = QA | QB | QC | QD Inner
  --   deriving (Eq, Ord)` (3 nullary ⇒ tag primops ⇒ derived route, so its `Ord`
  --   is `deriving Ord` ON THE INDUCTIVE): `error: failed to synthesize Ord Inner`,
  --   because the instance sat after the whole data block. Splicing fixes it for
  --   free — `sortDataDecls` already puts a field type first, so `Inner`'s block
  --   lands before `inductive Quad`.
  -- * A class-body DEFAULT using `≤`/`<`/`min`/`max` at a hand-written-`Ord` head:
  --   `failed to synthesize Min B` plus a cascading `Fields missing: bestB`. Class
  --   decls are the LAST thing in the data block, so every spliced `Ord` precedes
  --   them.
  -- * A compare body referencing another hand-written-`Ord` type that is not a
  --   FIELD — `ordRefDeps` above; the requirement is the reference graph, which is
  --   strictly larger than the field graph.
  -- * A compare body calling `==` at a type whose `Eq` is HAND-WRITTEN. There the
  --   only `BEq` in scope was `instBEqOfDecidableEq`, off the `deriving
  --   DecidableEq` this task's `handwrittenOrd` flag adds, so the body computed
  --   STRUCTURAL equality while the user's `instance : BEq T` sat further down —
  --   silently, two meanings of `==` in one module. `eqHoistHeads` moves that
  --   instance ahead of the compare def; Lean picks the LAST declared candidate
  --   among equal-priority ones, which is exactly why `M3T6R`'s "the explicit one
  --   wins" held at ordinary use sites and failed inside this section.
  --
  -- The resolution pipeline is why splicing needs its own pass rather than a
  -- reordering: a compare body pattern-matches on constructors and so needs
  -- `resolveUserCtors`, which must never run over an `inductive`'s own `| Ctor `
  -- lines. So each spliced block is resolved on its OWN, with the body pipeline,
  -- and joined already-resolved (see the resolution-pipeline header).
  let headOf (i : Instance) : String := i.headTypes.map emitType |> String.intercalate " "
  -- Which hand-written `BEq` instances the spliced bodies need in scope (the B3
  -- fix). Shared with `ordForwardRefs`, so the set spliced and the set scanned for
  -- forward references cannot disagree.
  let eqHoisted : List String :=
    eqHoistHeads keptBinds p.rawBinds derivedEq handwrittenOrd (p.typeDecls.length + 1)
  let isHandwrittenCompare (v : Var) : Bool :=
    v.name == "$ccompare" && headMatches v handwrittenOrd
  let isHoistedEq (v : Var) : Bool :=
    v.name == "$c==" && headMatches v eqHoisted
  let methodDefs := filterBinds
    (fun v e => v.name.startsWith "$c" && !isWrapperBind v e
                && !isHandwrittenCompare v && !isHoistedEq v)
    keptBinds
  let userBinds  := filterBinds
    (fun v _ => !v.name.startsWith "$c" && !isJunkName v.name && !isTranslatedDm v.name)
    keptBinds
  -- `superBinders` reaches BOTH sections. The `$c` method defs are monomorphic
  -- (their signatures carry no class constraint, so the recipes cannot fire there)
  -- and are passed the same list anyway: two emitters with one binder policy
  -- cannot drift, and a method with its own class constraint would be covered.
  let methodStr := emitProgramWith methodMap classNames methodDefs ctorNames superBinders
  let userStr   := emitProgramWith methodMap classNames userBinds ctorNames superBinders
  -- THE spliced-block top-name set: the WHOLE program's, not the one-bind program
  -- the first release passed. With only the `$ccompare` bind in scope, a reference
  -- to a user top-level function `norm` emitted `norm_2853` (a local id) and could
  -- not resolve under ANY ordering — `Unknown identifier norm_2853`. It now emits
  -- `norm`, which is still a forward reference (user binds come last, and hoisting
  -- them would need this section to move again), so `Main.lean` warns about the
  -- shape by name — see `ordForwardRefs`.
  let splicedTop := ctorNames ++ collectTopNames keptBinds
  -- `recOverride := some false`: a `.selfRec` compare's retargeted body mentions
  -- its own binder, which `emitBind` would otherwise read as user recursion and
  -- close with `decreasing_by all_goals sorry` — a `sorry` inside an `Ord`
  -- instance, tainting every `decide` proof about the order. Lean's STRUCTURAL
  -- recursion takes these bodies as they stand (the recursive call is always on a
  -- constructor field of the scrutinee), and a body it cannot take is loud.
  let spliceDef (b : Bind) : String :=
    emitProgramWith methodMap classNames [b] splicedTop superBinders (recOverride := some false)
  let resBody (s : String) : String :=
    resolveUserCtors kept (resolveNewtypes nts (resolveUserTypes kept s))
  let eqBlockFor (h : String) : Option String := do
    let (v, e) ← hwEqBindAt keptBinds derivedEq h
    let i ← p.instances.find? fun i => i.className == "Eq" && headOf i == h
    let inst ← emitInstance defaults userClasses derivedEq p.binds i
    -- A self-recursive `==` becomes recursion through the def's own name — and
    -- must, because the `instance : BEq` this def backs is emitted AFTER it, so a
    -- self-`==` left in place binds `instBEqOfDecidableEq` (structural) silently.
    -- See `retargetSelfEq`: it is keyed on the type application, so it runs on the
    -- PRE-`Lower` body and the result is lowered here. When the retarget is a
    -- no-op that lowering reproduces `e` exactly (`Lower.lowerProgram` is
    -- `lowerExpr` per bind, and `p.rawBinds` is the same bind list pre-`Lower`),
    -- which is why a hoisted non-recursive `Eq` is byte-identical to before.
    let e' := match findClassMethodBind p.rawBinds "$c==" h with
      | some (_, raw) => Lower.lowerExpr (retargetSelfEq h v raw)
      | none          => e
    some (resBody s!"{spliceDef (.nonRec v e')}\n\n{inst}")
  let ordBlockFor (h : String) : Option String := do
    let (v, e) ← compareBodyAt h
    let i ← p.instances.find? fun i => i.className == "Ord" && headOf i == h
    let inst ← emitInstance defaults userClasses derivedEq p.binds i
    -- Self-recursion through the instance's own dictionary becomes recursion
    -- through the def's own name; see `retargetSelfCompare`.
    let e' := match ordRoute p.binds h with
      | .handwritten _ true => retargetSelfCompare h v e
      | _                   => e
    some (resBody s!"{spliceDef (.nonRec v e')}\n\n{inst}")
  let blocksFor (h : String) : List String :=
    (if eqHoisted.contains h then (eqBlockFor h).toList else [])
      ++ (if handwrittenOrd.contains h then (ordBlockFor h).toList else [])
  -- An ORPHAN head (an instance on a type this module does not declare) has no
  -- `inductive` to sit next to; its blocks go after every local decl, before the
  -- class decls, which is where the pre-splice layout effectively put them too.
  let localHeads := datas.map (·.1)
  let orphanHeads := (handwrittenOrd ++ eqHoisted).eraseDups.filter
    fun h => !localHeads.contains h
  -- Superclass-dependency order again, now for the instances: a child instance
  -- omits its parent field and Lean synthesizes it from the parent instance in
  -- scope, which must therefore already be emitted (`sortInstances`).
  --
  -- `Ord` (and a hoisted `Eq`) is filtered out AFTER the sort, never before it:
  -- those instances are emitted in the data block above (the derived and
  -- unsupported `Ord` routes emit nothing here anyway, so the filter is
  -- behaviour-preserving for them), and filtering before the sort could in
  -- principle move the survivors relative to each other.
  let insts := ((sortInstances userClasses p.instances).filter fun i =>
      i.className != "Ord" && !(i.className == "Eq" && eqHoisted.contains (headOf i)))
    |>.filterMap (emitInstance defaults userClasses derivedEq p.binds)
  let instStr := String.intercalate "\n\n" insts
  let bodyRaw := String.intercalate "\n\n"
    (List.filter (· != "") [methodStr, instStr, userStr])
  let bodyResolved := resolveUserTypes kept bodyRaw
                    |> resolveNewtypes nts
                    |> resolveUserCtors kept
  -- `resolveUserTypes` (opaque → bare) must run on the data block too: a local
  -- type used as another decl's FIELD type arrives as
  -- `(GHCCore.tyConOpaque "Point")` there, exactly as in a body. Only the
  -- *type* pass runs on the `inductive`s and the class decls — `resolveUserCtors`
  -- would rewrite the `| Ctor ` lines of the inductive itself — while the spliced
  -- `Ord`/`Eq` blocks are already fully resolved (`resBody`) and are joined in
  -- as-is. Per-piece resolution is equivalent to resolving the join: every needle
  -- of passes 1–3 is a single identifier occurrence, so none can span the `\n\n`
  -- that separates two pieces.
  let res12 (s : String) : String := resolveNewtypes nts (resolveUserTypes kept s)
  let dataBlock :=
    String.intercalate "\n\n" (List.filter (· != "")
      (datas.flatMap (fun (h, d) => res12 d :: blocksFor h)
        ++ orphanHeads.flatMap blocksFor
        ++ classDecls.map res12))
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
