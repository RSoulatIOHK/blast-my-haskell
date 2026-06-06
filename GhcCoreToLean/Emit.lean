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
  | c   => if isLeanIdChar c then String.singleton c else "_"

/-- Lean-safe identifier from a GHC name. Wraps in `«…»` if the result is a keyword. -/
def sanitize (s : String) : String :=
  let mapped := s.foldl (fun acc c => acc ++ sanitizeChar c) ""
  if leanKeywords.contains mapped then s!"«{mapped}»" else mapped

/-- Disambiguating identifier — append the unique to the sanitized name. -/
def sanitizeWithUnique (v : Var) : String :=
  s!"{sanitize v.name}_{v.unique}"

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
  | .tyVar n         => n
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

/-- Literal as a Lean pattern (for `LitAlt`). -/
def emitLiteralPattern : Literal → String
  | .litInt n    => toString n
  | .litWord n   => toString n
  | .litFloat f  => toString f
  | .litDouble f => toString f
  | .litString s => s!"\"{s}\""
  | .litChar c   => s!"'{c}'"
  | .litLabel _  => "_"   -- foreign labels not meaningful as patterns

/-! ## Var emission (locals vs. mapped global ids) -/

def emitVar (v : Var) : String :=
  match valueMap v.name with
  | some lean => lean
  | none      => sanitize v.name

/-! ## Expr emission -/

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
    let resolved := (dataConMap name).getD (sanitize name)
    if bndrs.isEmpty then resolved
    else
      let bs := String.intercalate " " (bndrs.map (sanitize ·.name))
      s!"{resolved} {bs}"

mutual
  partial def emitExpr : Expr → String
    | .var v   => emitVar v
    | .lit l   => emitLiteral l
    | .app f a => s!"({emitExpr f}) ({emitExpr a})"
    | .lam v body =>
      s!"(fun {sanitize v.name} => {emitExpr body})"
    | .let_ b body =>
      s!"({emitLet b}\n{emitExpr body})"
    | .case_ scr _cb _ty alts =>
      let alts'   := reorderAlts alts
      let altsStr := alts'.map emitAlt
      let header  := s!"(match {emitExpr scr} with"
      let body    := String.intercalate "\n" altsStr
      s!"{header}\n{body})"
    | .cast e  => emitExpr e
    | .tick e  => emitExpr e
    | .type_ _ => "(GHCCore.typeArg : GHCCore.GHCType)"

  /-- Render a single Alt arm. -/
  partial def emitAlt : Alt → String
    | .mk con bndrs rhs =>
      s!"| {emitAltPattern con bndrs} => {emitExpr rhs}"

  /-- Render a Let. Returns the let-binding line(s) without the body. -/
  partial def emitLet : Bind → String
    | .nonRec v e =>
      s!"let {sanitize v.name} := {emitExpr e}"
    | .rec_ pairs =>
      let lines := pairs.map fun (v, e) =>
        s!"  {sanitize v.name} := {emitExpr e}"
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

private def emitDefHeader (v : Var) (args : List Var) (resTy : GHCType) (rhsBody : Expr) (rec? : Bool) : String :=
  let name     := sanitize v.name
  let argStrs  := args.map (fun a => s!"({sanitize a.name} : {emitType a.ty})")
  let argStr   := String.intercalate " " argStrs
  let resStr   := emitType resTy
  let body     := emitExpr rhsBody
  let head     :=
    if argStrs.isEmpty then s!"def {name} : {resStr} :="
    else s!"def {name} {argStr} : {resStr} :="
  let term     :=
    if rec? then "\ndecreasing_by all_goals sorry"
    else ""
  s!"{head}\n  {body}{term}"

/-! ## Top-level bind emission -/

def emitBind (b : Bind) : String :=
  match b with
  | .nonRec v e =>
    let (args, body) := peelLams e
    let resTy        := stripFunTys args.length v.ty
    let rec?         := occursInExpr v.name e
    emitDefHeader v args resTy body rec?
  | .rec_ pairs =>
    -- Treat a singleton Rec as a stand-alone recursive def (no `mutual` wrapper).
    -- Multi-element Rec wraps in mutual.
    match pairs with
    | [(v, e)] =>
      let (args, body) := peelLams e
      let resTy        := stripFunTys args.length v.ty
      let rec?         := occursInExpr v.name e
      emitDefHeader v args resTy body rec?
    | _        =>
      let defs := pairs.map fun (v, e) =>
        let (args, body) := peelLams e
        let resTy        := stripFunTys args.length v.ty
        emitDefHeader v args resTy body true
      let body := String.intercalate "\n" defs
      s!"mutual\n{body}\nend"

def emitProgram (p : CoreProgram) : String :=
  let bindStrs := p.map emitBind
  String.intercalate "\n\n" bindStrs

end GHCCore.Emit
