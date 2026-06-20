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
  ty   : GHCType   -- the *generalized* method type, e.g. `a → Int`
deriving Repr, Inhabited

structure ClassDecl where
  name    : Name
  tyVar   : Name           -- the class's type parameter, e.g. "a"
  methods : List ClassMethod
deriving Repr, Inhabited

structure Program where
  binds     : CoreProgram
  typeDecls : List DataDecl
  instances : List Instance
deriving Inhabited

end GHCCore
