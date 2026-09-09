namespace GHCCore

abbrev Name   := String
abbrev Unique := Nat

inductive VarRole where
  | id
  | tyVar
  | dict
deriving Repr, DecidableEq, Inhabited

inductive GHCTyLit where
  | nat : Nat → GHCTyLit
  | str : String → GHCTyLit
deriving Repr, Inhabited

inductive GHCType where
  | tyVar  : Name → GHCType
  | tyApp  : GHCType → GHCType → GHCType
  | tyFun  : GHCType → GHCType → GHCType
  | forAll : Name → GHCType → GHCType
  | tyCon  : Name → List GHCType → GHCType
  | tyLit  : GHCTyLit → GHCType
deriving Repr, Inhabited

structure Var where
  name   : Name
  unique : Unique
  ty     : GHCType
  role   : VarRole
deriving Repr, Inhabited

inductive Literal where
  | litInt    : Int → Literal
  | litWord   : Nat → Literal
  | litFloat  : Float → Literal
  | litDouble : Float → Literal
  | litString : String → Literal
  /-- A string literal whose GHC bytes have NO faithful Lean image, carrying the
      HEX of those bytes (`"78 ed a0 80 79"`) rather than any decoded text.

      GHC writes string literals in MODIFIED UTF-8. Of its two deviations from
      standard UTF-8 the shim repairs one (the overlong NUL `C0 80`, since U+0000
      is a legal Lean `Char`) and cannot repair the other: a lone surrogate
      U+D800–DFFF is not a Lean `Char` at all, so there is nothing to decode it
      to. The shim flags such a literal (`"unrepresentable"` in the JSON) and
      `Main.lean` REFUSES the module before emission — see
      `Emit.unrepresentableStringLiterals`. The payload is the evidence, not a
      value: the lenient decode of those bytes is exactly the plausible-looking
      wrong string this constructor exists to keep out of the output. -/
  | litStringUnrepresentable : String → Literal
  | litChar   : Char → Literal
  /-- A `Char` literal with NO faithful Lean image, carrying the code point
      (`"U+D800"`) rather than any `Char`.

      Haskell's `Char` spans [0,0x10FFFF] INCLUDING the 2048 surrogates
      U+D800–DFFF; Lean's excludes them. So `'\55296'` is ordinary Haskell with
      no Lean value at all — not a different one. The shim's `MachChar` arm used
      `T.singleton`, which is NOT `Text`'s identity on `Char`: `text-1.2.5.0`
      applies `safe` and maps every surrogate to U+FFFD, so such a literal used
      to arrive as the replacement character and emit as a legal, wrong `Char`
      (measured: `CharSurrogate.hs` emitted `def lone : Char := '\65533'`, rc=0,
      green `lake build`). The shim now flags it (`"unrepresentable"` in the
      JSON) and `Main.lean` REFUSES the module before emission — see
      `Emit.unrepresentableCharLiterals`.

      SAME CHANNEL, DIFFERENT EVIDENCE, from `litStringUnrepresentable`: a
      string's loss is a byte-encoding fact (modified UTF-8) so its payload is
      bytes; a `Char`'s is not, so its payload is a code point and none of the
      overlong-NUL/`unpackCString#` story applies. Hence two constructors and
      two refusal messages rather than one of each.

      DECLARED AFTER `litChar`, deliberately: `deriving Inhabited` takes the
      FIRST constructor, so the order of these arms is load-bearing for
      `default : Literal`. -/
  | litCharUnrepresentable : String → Literal
  | litLabel  : String → Literal
deriving Repr, Inhabited

inductive AltCon where
  | dataCon : Name → AltCon
  | litAlt  : Literal → AltCon
  | default : AltCon
deriving Repr, Inhabited

mutual
  inductive Expr where
    | var    : Var → Expr
    | lit    : Literal → Expr
    | app    : Expr → Expr → Expr
    | lam    : Var → Expr → Expr
    | let_   : Bind → Expr → Expr
    | case_  : Expr → Var → GHCType → List Alt → Expr
    | cast   : Expr → Expr
    | type_  : GHCType → Expr
    -- A coercion in expression position (GHC `Coercion`). Payload-free: it
    -- exists only so `Lower` can erase it in argument position, exactly like
    -- `.type_`. Never valid in head position (a coercion is not a function) —
    -- if one survives lowering, `Emit` produces an undefined identifier so the
    -- generated file fails loud rather than silently meaning something.
    | coercion : Expr
    | tick   : Expr → Expr

  inductive Bind where
    | nonRec : Var → Expr → Bind
    | rec_   : List (Var × Expr) → Bind

  inductive Alt where
    | mk : AltCon → List Var → Expr → Alt
end

abbrev CoreProgram := List Bind

/-! ## Type and instance declarations

    These come from the `decl-plugin` JSON sidecar (not from Core itself).
    Together with `CoreProgram` they form the full `Program`. -/

structure DataField where
  name : Name
  ty   : GHCType
deriving Repr, Inhabited

structure DataConSpec where
  name   : Name
  fields : List DataField
deriving Repr, Inhabited

structure DataDecl where
  name  : Name
  kind  : String           -- "data" or "newtype"
  ctors : List DataConSpec
deriving Repr, Inhabited

structure Instance where
  className  : Name
  headTypes  : List GHCType
  dfunName   : Name
  dfunUnique : Nat
deriving Repr, Inhabited

structure ClassMethod where
  name : Name
  ty   : GHCType   -- the method type with the class parameter(s) free, e.g. `a → Int`
  /-- Does the class declare a default body for this method? Only the
      decl-plugin channel can know this (`ClassOpItem`'s `DefMethInfo`); the
      Core-reconstruction fallback always says `false` — a `$dm<method>` bind is
      indistinguishable from an ordinary top-level bind there. Consumed by M3
      Task 4. -/
  hasDefault : Bool := false
deriving Repr, Inhabited

/-- A user type class's *shape*.

    v2 (M3 Task 1) widened this from a single `tyVar` to a `tyVars` list and
    added `supers`, because the shape now has a second, authoritative source: the
    decl-plugin's `classDecls` channel (`GhcDeclDump.ppClass`), which reads the
    real `Class` out of GHC's `TcGblEnv`. The older source —
    `Emit.reconstructClasses`, which infers a class from its instances' `$c`
    method binds — cannot see superclasses or defaults at all (class-op and `$p`
    superclass-selector Ids are not top-level binds) and always produced a
    single type parameter. It is kept as the fallback for a run with no plugin
    sidecar; see `Emit.mergeClassDecls` for the precedence rule. -/
structure ClassDecl where
  name    : Name
  /-- The class's type parameters, e.g. `["a"]`. MULTI-parameter classes are
      supported end to end since M3 Task 7 — `examples/haskell/MultiParam.hs` pins
      `class Convert a b`, two instances of it, and a `Convert a b =>` constraint.
      What such a class does not get is its SUPERCLASSES (see `supers`). The
      Core-reconstruction fallback always invents exactly one parameter, so only
      the plugin channel can produce a longer list. -/
  tyVars  : List Name
  /-- Superclass *names*, e.g. `["Sized"]` for `class Sized a => Container a`.
      Consumed by emission since M3 Task 5: a parent this module declares becomes
      `extends Sized a`, a builtin with a `Maps.classConMap` recipe becomes
      instance-implicit binders at every constraint site
      (`Emit.classSuperBinders`), and anything else is dropped with a warning
      (`Emit.unmappedSupers`).

      NAMES only is the channel's limit (`GhcDeclDump.ppSuperPred` discards each
      superclass's ARGUMENTS), and that is what the two arity-related drops are
      about: a superclass of a multi-parameter class cannot be applied to one of
      several variables (`Emit.multiParamSupers`), and a multi-parameter parent of
      a single-parameter class cannot be applied to the child's one variable
      (`Emit.multiParamParentSupers`). Both are dropped and WARNED rather than
      guessed; a guess would be silently wrong. -/
  supers  : List Name
  methods : List ClassMethod
deriving Repr, Inhabited

structure Program where
  binds     : CoreProgram
  typeDecls : List DataDecl
  instances : List Instance
  /-- Class shapes from the decl-plugin sidecar. Defaulted to `[]` so a Program
      built from a pre-`classDecls` JSON (or a hand-written test literal) still
      elaborates; `Emit` then falls back to Core reconstruction. -/
  classDecls : List ClassDecl := []
  /-- THE SAME binds as `binds`, but PRE-`Lower`: same filtering, only the
      erasure has not happened. `Main.lean` sets it to the list it hands to
      `Lower.lowerProgram`, so the two differ in exactly one way.

      Why the emitter needs both. `Lower` erases a class-method application's
      TYPE argument (`== @T $fEqT a b` ⇒ `== a b`), and that argument is the only
      exact record of the type a class op is instantiated at: post-`Lower` the
      dispatch type has to be guessed from a value argument's type, which fails
      outright when no argument is a bare `Var` (`G a b == G c d`). That guess is
      what `Emit.eqHoistHeads` used to decide which hand-written `BEq` must
      precede a spliced `Ord` block, and a miss there is SILENT-WRONG: the `==`
      inside the block falls back to `instBEqOfDecidableEq`, i.e. structural
      equality. `Emit.classOpHeadTy` reads the type application out of THIS list
      instead. Emission still uses `binds` — a lowered body is what has a Lean
      image — so this field is read only by the analyses that need the type.

      Defaulted to `binds` so a hand-written test literal (or any caller that has
      only the lowered program) keeps the pre-existing post-`Lower` behaviour
      rather than silently analysing an empty list. -/
  rawBinds  : CoreProgram := binds
deriving Inhabited

end GHCCore
