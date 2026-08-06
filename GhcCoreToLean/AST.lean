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
  | litChar   : Char → Literal
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
  /-- The class's type parameters, e.g. `["a"]`. Multi-parameter classes are not
      supported end-to-end yet (M3 Task 7); the list shape is here so the plugin
      channel can carry the truth rather than truncate it. -/
  tyVars  : List Name
  /-- Superclass *names*, e.g. `["Sized"]` for `class Sized a => Container a`.
      NOT yet consumed by emission (M3 Task 5) — a class with a superclass
      therefore emits without it, which fails loud at the use site (`failed to
      synthesize Sized …`) rather than silently. -/
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
deriving Inhabited

end GHCCore
