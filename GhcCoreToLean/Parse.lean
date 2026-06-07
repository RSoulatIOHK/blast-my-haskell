import Lean
import GhcCoreToLean.AST

namespace GHCCore
open Lean

private def getTag (j : Lean.Json) : Except String String :=
  j.getObjValAs? String "tag"

private def getField (j : Lean.Json) (k : String) : Except String Lean.Json :=
  j.getObjVal? k

private def parseVarRole : Lean.Json → Except String VarRole := fun j => do
  let s ← j.getStr?
  match s with
  | "id"    => .ok .id
  | "tyVar" => .ok .tyVar
  | "dict"  => .ok .dict
  | other   => .error s!"unknown VarRole: {other}"

private def parseGHCTyLit (j : Lean.Json) : Except String GHCTyLit := do
  let kind ← j.getObjValAs? String "kind"
  let value ← j.getObjValAs? String "value"
  match kind with
  | "Nat" =>
    match value.toNat? with
    | some n => .ok (.nat n)
    | none   => .error s!"TyLit Nat value not parseable: {value}"
  | "Symbol" | "Str" | "String" => .ok (.str value)
  | other => .error s!"unknown TyLit kind: {other}"

partial def parseGHCType (j : Lean.Json) : Except String GHCType := do
  let tag ← getTag j
  match tag with
  | "TyVar"  => do
    let n ← j.getObjValAs? String "name"
    .ok (.tyVar n)
  | "TyApp"  => do
    let f ← parseGHCType (← getField j "fun")
    let a ← parseGHCType (← getField j "arg")
    .ok (.tyApp f a)
  | "TyFun"  => do
    let a ← parseGHCType (← getField j "arg")
    let r ← parseGHCType (← getField j "res")
    .ok (.tyFun a r)
  | "ForAll" => do
    let v ← j.getObjValAs? String "var"
    let b ← parseGHCType (← getField j "body")
    .ok (.forAll v b)
  | "TyCon"  => do
    let n ← j.getObjValAs? String "name"
    let argsJ ← getField j "args"
    let arr ← argsJ.getArr?
    let args ← arr.toList.mapM parseGHCType
    .ok (.tyCon n args)
  | "TyLit"  => do
    let lit ← parseGHCTyLit j
    .ok (.tyLit lit)
  | other    => .error s!"unknown GHCType tag: {other}"

def parseVar (j : Lean.Json) : Except String Var := do
  let name   ← j.getObjValAs? String "name"
  let uniq   ← j.getObjValAs? Nat    "unique"
  let tyJ    ← getField j "type"
  let ty     ← parseGHCType tyJ
  -- role defaults to .id if absent (forward-compat per plan Step 3)
  let role ← match j.getObjVal? "role" with
    | .ok rj => parseVarRole rj
    | .error _ => .ok .id
  .ok { name, unique := uniq, ty, role }

def parseLiteral (j : Lean.Json) : Except String Literal := do
  let tag ← getTag j
  match tag with
  | "LitInt"    => do
    let n ← j.getObjValAs? Int "value"
    .ok (.litInt n)
  | "LitWord"   => do
    let n ← j.getObjValAs? Nat "value"
    .ok (.litWord n)
  | "LitFloat"  => do
    let n ← j.getObjValAs? Float "value"
    .ok (.litFloat n)
  | "LitDouble" => do
    let n ← j.getObjValAs? Float "value"
    .ok (.litDouble n)
  | "LitString" => do
    let s ← j.getObjValAs? String "value"
    .ok (.litString s)
  | "LitChar"   => do
    let s ← j.getObjValAs? String "value"
    match s.data with
    | [c] => .ok (.litChar c)
    | _   => .error s!"LitChar value must be a single-character string, got: {s}"
  | "LitLabel"  => do
    let s ← j.getObjValAs? String "value"
    .ok (.litLabel s)
  | other       => .error s!"unknown Literal tag: {other}"

def parseAltCon (j : Lean.Json) : Except String AltCon := do
  let tag ← getTag j
  match tag with
  | "DataAlt" => do
    let n ← j.getObjValAs? String "name"
    .ok (.dataCon n)
  | "LitAlt"  => do
    let litJ ← getField j "lit"
    let l ← parseLiteral litJ
    .ok (.litAlt l)
  | "DEFAULT" => .ok .default
  | other     => .error s!"unknown AltCon tag: {other}"

mutual
  partial def parseExpr (j : Lean.Json) : Except String Expr := do
    let tag ← getTag j
    match tag with
    | "Var"  => do
      let v ← parseVar (← getField j "var")
      .ok (.var v)
    | "Lit"  => do
      let l ← parseLiteral (← getField j "lit")
      .ok (.lit l)
    | "App"  => do
      let f ← parseExpr (← getField j "fun")
      let a ← parseExpr (← getField j "arg")
      .ok (.app f a)
    | "Lam"  => do
      let v ← parseVar (← getField j "binder")
      let b ← parseExpr (← getField j "body")
      .ok (.lam v b)
    | "Let"  => do
      let bnd ← parseBind (← getField j "bind")
      let b   ← parseExpr (← getField j "body")
      .ok (.let_ bnd b)
    | "Case" => do
      let scr   ← parseExpr (← getField j "scrutinee")
      let bnd   ← parseVar  (← getField j "binder")
      let ty    ← parseGHCType (← getField j "type")
      let altsA ← (← getField j "alts").getArr?
      let alts  ← altsA.toList.mapM parseAlt
      .ok (.case_ scr bnd ty alts)
    | "Cast" => do
      let e ← parseExpr (← getField j "expr")
      .ok (.cast e)
    | "Tick" => do
      let e ← parseExpr (← getField j "expr")
      .ok (.tick e)
    | "Type" => do
      let t ← parseGHCType (← getField j "type")
      .ok (.type_ t)
    | other  => .error s!"unknown Expr tag: {other}"

  partial def parseAlt (j : Lean.Json) : Except String Alt := do
    let con ← parseAltCon (← getField j "con")
    let bndA ← (← getField j "binders").getArr?
    let bnds ← bndA.toList.mapM parseVar
    let rhs ← parseExpr (← getField j "rhs")
    .ok (.mk con bnds rhs)

  partial def parseBind (j : Lean.Json) : Except String Bind := do
    let tag ← getTag j
    match tag with
    | "NonRec" => do
      let b ← parseVar  (← getField j "binder")
      let r ← parseExpr (← getField j "rhs")
      .ok (.nonRec b r)
    | "Rec"    => do
      let pairsA ← (← getField j "pairs").getArr?
      let pairs ← pairsA.toList.mapM fun pj => do
        let b ← parseVar  (← getField pj "binder")
        let r ← parseExpr (← getField pj "rhs")
        .ok (b, r)
      .ok (.rec_ pairs)
    | other    => .error s!"unknown Bind tag: {other}"
end

def parseCoreProgram (j : Lean.Json) : Except String CoreProgram := do
  let bindsA ← (← getField j "binds").getArr?
  bindsA.toList.mapM parseBind

def parseCoreProgramFromString (s : String) : Except String CoreProgram := do
  let j ← Lean.Json.parse s
  parseCoreProgram j

/-! ## Type & instance declarations (from the decl-plugin sidecar) -/

private def parseDataField (j : Lean.Json) : Except String DataField := do
  let name ← j.getObjValAs? String "name"
  let ty   ← parseGHCType (← getField j "type")
  .ok { name, ty }

private def parseDataConSpec (j : Lean.Json) : Except String DataConSpec := do
  let name    ← j.getObjValAs? String "name"
  let fieldsA ← (← getField j "fields").getArr?
  let fields  ← fieldsA.toList.mapM parseDataField
  .ok { name, fields }

def parseDataDecl (j : Lean.Json) : Except String DataDecl := do
  let name   ← j.getObjValAs? String "name"
  let kind   ← j.getObjValAs? String "kind"
  let ctorsA ← (← getField j "constructors").getArr?
  let ctors  ← ctorsA.toList.mapM parseDataConSpec
  .ok { name, kind, ctors }

def parseInstance (j : Lean.Json) : Except String Instance := do
  let className  ← j.getObjValAs? String "className"
  let headA      ← (← getField j "headTypes").getArr?
  let headTypes  ← headA.toList.mapM parseGHCType
  let dfunName   ← j.getObjValAs? String "dfunName"
  let dfunUnique ← j.getObjValAs? Nat    "dfunUnique"
  .ok { className, headTypes, dfunName, dfunUnique }

/-- Parse either the legacy `{ binds: ... }` or the extended
    `{ binds, typeDecls, instances }` shape. -/
def parseProgram (j : Lean.Json) : Except String Program := do
  let binds      ← parseCoreProgram j
  let typeDecls  ← match j.getObjVal? "typeDecls" with
    | .ok td => match td with
      | .null => .ok []
      | _ => do
        let arr ← td.getArr?
        arr.toList.mapM parseDataDecl
    | .error _ => .ok []
  let instances  ← match j.getObjVal? "instances" with
    | .ok ins => match ins with
      | .null => .ok []
      | _ => do
        let arr ← ins.getArr?
        arr.toList.mapM parseInstance
    | .error _ => .ok []
  .ok { binds, typeDecls, instances }

def parseProgramFromString (s : String) : Except String Program := do
  let j ← Lean.Json.parse s
  parseProgram j

end GHCCore
