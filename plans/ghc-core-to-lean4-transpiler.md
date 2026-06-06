# GHC Core → Lean 4 Transpiler

## Goal

Build a transpiler that takes serialized GHC Core (from a GHC plugin or `ghc-dump-core`) and emits Lean 4 source files that can be processed by Blaster, an SMT-backed automated verification tactic for Lean 4.

The purpose is to enable Blaster to verify properties of Haskell programs by working on their GHC Core representation lifted into Lean 4.

---

## Pipeline Overview

```
Haskell source
  ↓  GHC plugin (emit JSON)
GHC Core (JSON)
  ↓  transpiler (this project)
Lean 4 source (.lean)
  ↓
Blaster
```

---

## Step 1: GHC Core Serialization

Write a GHC plugin that walks a `CoreProgram` and emits JSON. Use `ghc-dump-core` on Hackage as a reference or starting point — it already serializes Core to a structured format.

The JSON schema to target:

```json
{
  "binds": [
    {
      "tag": "NonRec",
      "binder": { "name": "f", "unique": 42, "type": <GHCType> },
      "rhs": <Expr>
    },
    {
      "tag": "Rec",
      "pairs": [
        { "binder": <Var>, "rhs": <Expr> },
        ...
      ]
    }
  ]
}
```

### Expr JSON schema

```json
{ "tag": "Var",    "var": <Var> }
{ "tag": "Lit",    "lit": <Literal> }
{ "tag": "App",    "fun": <Expr>, "arg": <Expr> }
{ "tag": "Lam",    "binder": <Var>, "body": <Expr> }
{ "tag": "Let",    "bind": <Bind>, "body": <Expr> }
{ "tag": "Case",   "scrutinee": <Expr>, "binder": <Var>, "type": <GHCType>, "alts": [<Alt>] }
{ "tag": "Cast",   "expr": <Expr> }
{ "tag": "Tick",   "expr": <Expr> }
{ "tag": "Type",   "type": <GHCType> }
{ "tag": "Coerce", "expr": <Expr> }
```

Notes:
- `Cast` and `Tick` drop their secondary payload (coercions and ticks are erased).
- `Type` carries its type argument (needed for type-passing style).
- `Coerce` is kept as a transparent wrapper — semantically the identity.

### Var JSON schema

```json
{ "name": "f", "unique": 42, "type": <GHCType> }
```

### GHCType JSON schema

```json
{ "tag": "TyVar",  "name": "a" }
{ "tag": "TyApp",  "fun": <GHCType>, "arg": <GHCType> }
{ "tag": "TyFun",  "arg": <GHCType>, "res": <GHCType> }
{ "tag": "ForAll", "var": "a", "body": <GHCType> }
{ "tag": "TyCon",  "name": "Maybe", "args": [<GHCType>] }
{ "tag": "TyLit",  "value": "3", "kind": "Nat" }
```

### Literal JSON schema

```json
{ "tag": "LitInt",    "value": 42 }
{ "tag": "LitWord",   "value": 42 }
{ "tag": "LitFloat",  "value": 3.14 }
{ "tag": "LitDouble", "value": 3.14 }
{ "tag": "LitString", "value": "hello" }
{ "tag": "LitChar",   "value": "a" }
{ "tag": "LitLabel",  "value": "some_foreign_label" }
```

### Alt JSON schema

```json
{
  "con": { "tag": "DataAlt", "name": "Just" }
        | { "tag": "LitAlt",  "lit": <Literal> }
        | { "tag": "DEFAULT" },
  "binders": [<Var>],
  "rhs": <Expr>
}
```

---

## Step 2: Lean 4 AST (the target types)

Place in `GHCCore/AST.lean`.

```lean
namespace GHCCore

abbrev Name   := String
abbrev Unique := Nat

inductive GHCTyLit where
  | nat  : Nat → GHCTyLit
  | str  : String → GHCTyLit

inductive GHCType where
  | tyVar  : Name → GHCType
  | tyApp  : GHCType → GHCType → GHCType
  | tyFun  : GHCType → GHCType → GHCType
  | forAll : Name → GHCType → GHCType
  | tyCon  : Name → List GHCType → GHCType
  | tyLit  : GHCTyLit → GHCType

structure Var where
  name   : Name
  unique : Unique
  ty     : GHCType
deriving Repr

inductive Literal where
  | litInt    : Int → Literal
  | litWord   : Nat → Literal
  | litFloat  : Float → Literal
  | litDouble : Float → Literal
  | litString : String → Literal
  | litChar   : Char → Literal
  | litLabel  : String → Literal
deriving Repr

inductive AltCon where
  | dataCon : Name → AltCon
  | litAlt  : Literal → AltCon
  | default : AltCon
deriving Repr

mutual
  inductive Expr where
    | var    : Var → Expr
    | lit    : Literal → Expr
    | app    : Expr → Expr → Expr
    | lam    : Var → Expr → Expr
    | let_   : Bind → Expr → Expr
    | case_  : Expr → Var → GHCType → List Alt → Expr
    | cast   : Expr → Expr         -- coercion erased, semantically identity
    | type_  : GHCType → Expr      -- type argument
    | tick   : Expr → Expr         -- source annotation, transparent
  deriving Repr

  inductive Bind where
    | nonRec : Var → Expr → Bind
    | rec_   : List (Var × Expr) → Bind
  deriving Repr

  structure Alt where
    con   : AltCon
    bndrs : List Var
    rhs   : Expr
  deriving Repr
end

abbrev CoreProgram := List Bind

end GHCCore
```

---

## Step 3: JSON Parser

Place in `GHCCore/Parse.lean`. Parse the JSON produced in Step 1 into `GHCCore.CoreProgram`.

Use `Lean.Json` (available in the Lean 4 standard library) or emit a Python parser that produces the Lean 4 source directly (see Step 4 note).

The parser must handle:
- All `Expr` tags
- Recursive `Bind` groups (lists of pairs)
- All `GHCType` constructors
- All `Literal` variants
- `AltCon` variants

---

## Step 4: Lean 4 Code Emitter

**Recommended approach**: write the emitter in Python (or Haskell in the GHC plugin itself). It reads the JSON and directly emits `.lean` source text. This avoids bootstrapping a Lean 4 JSON parser.

Place in `transpiler/emit.py`.

### Emitter rules

#### Top-level program

```
CoreProgram → sequence of Lean 4 definitions
```

Each `Bind` in the program becomes one or more `def` declarations.

#### NonRec bind

```
NonRec v e  →  def <sanitize(v.name)> : <emitType(v.ty)> := <emitExpr(e)>
               termination_by <first_arg_or_omit>
               decreasing_by sorry
```

If `e` is a `Lam`, collect all leading lambdas as function arguments before emitting the body.

#### Rec bind

```
Rec [(v1,e1), (v2,e2), ...]  →
  mutual
    def <name1> ... := <body1>
    termination_by <first_arg>
    decreasing_by sorry

    def <name2> ... := <body2>
    termination_by <first_arg>
    decreasing_by sorry
  end
```

#### Termination annotation rules

- **Nullary definition** (no lambda arguments after collecting): emit no `termination_by` or `decreasing_by`.
- **Any function with ≥ 1 argument**: always emit `termination_by <first_arg_name>` followed by `decreasing_by sorry`.
- This applies to every `def` without exception, including inside `mutual` blocks.
- Do **not** use `partial def` under any circumstances — Blaster does not support `partial`.

#### Expr emission

| Expr | Lean 4 output |
|------|---------------|
| `Var v` | `<sanitize(v.name)>` |
| `Lit (LitInt n)` | `(<n> : Int)` |
| `Lit (LitWord n)` | `(<n> : Nat)` |
| `Lit (LitFloat f)` | `(<f> : Float)` |
| `Lit (LitDouble f)` | `(<f> : Float)` |
| `Lit (LitString s)` | `"<s>"` |
| `Lit (LitChar c)` | `'<c>'` |
| `Lit (LitLabel l)` | `GHCCore.foreignLabel "<l>"` |
| `App f x` | `(<emitExpr f>) (<emitExpr x>)` |
| `Lam v body` | `fun <sanitize(v.name)> => <emitExpr body>` |
| `Let b body` | `let <emitBind b>; <emitExpr body>` |
| `Case s bnd _ alts` | `match <emitExpr s> with\n<emitAlts alts>` |
| `Cast e` | `<emitExpr e>` |
| `Tick e` | `<emitExpr e>` |
| `Type t` | `(GHCCore.typeArg : GHCCore.GHCType)` — emit as opaque placeholder |

#### Case / Alt emission

```lean
match <scrutinee> with
| <ConName> <binders...> => <rhs>
| <ConName> <binders...> => <rhs>
| _ => <rhs>   -- DEFAULT
```

`LitAlt` becomes a literal pattern. `DEFAULT` becomes `_`.

#### Let emission (inline)

```lean
let <name> := <rhs>
<body>
```

For `Rec` lets (local mutual recursion), emit a `have` block or a local `def` — flag these as TODO in a comment for now, they are rare in practice.

#### Type emission

Types are emitted as Lean 4 terms only where Lean requires an explicit type annotation. Otherwise omit. When needed:

| GHCType | Lean 4 |
|---------|--------|
| `TyVar a` | `<a>` |
| `TyFun a b` | `<a> → <b>` |
| `TyApp f x` | `<f> <x>` |
| `ForAll a body` | `∀ (<a> : Type), <body>` |
| `TyCon "Int" []` | `Int` |
| `TyCon "Bool" []` | `Bool` |
| `TyCon "List" [a]` | `List <a>` |
| `TyCon "Maybe" [a]` | `Option <a>` |
| `TyCon "Either" [a,b]` | `Sum <a> <b>` |
| `TyCon name args` | `GHCCore.TyCon.«<name>» <args...>` |

Unknown `TyCon`s are emitted as a namespaced opaque type application. The emitter should maintain a mapping file of known GHC → Lean 4 type correspondences that can be extended.

#### Name sanitization

GHC names can contain characters illegal in Lean 4 identifiers. Apply:

- Replace `$` with `_dollar_`
- Replace `#` with `_hash_`
- Replace `.` with `_dot_` (qualified names)
- Append `_<unique>` to disambiguate shadowed names
- Wrap in `«...»` if the name is a Lean 4 keyword (`match`, `let`, `fun`, `def`, `if`, `then`, `else`, `by`, `where`, `with`, `do`, `return`, `have`, `show`, `from`, `type`, `sort`, `Prop`, `Type`)

---

## Step 5: Support Definitions

Place in `GHCCore/Prelude.lean`. These are axioms and stubs that the emitted code may reference.

```lean
namespace GHCCore

-- Opaque type for GHC types not mapped to Lean builtins
opaque TyCon (name : String) : Type

-- Foreign labels (FFI)
opaque foreignLabel (name : String) : α

-- Type argument placeholder (erased at runtime)
opaque typeArg : GHCType := GHCType.tyCon "_" []

-- Bottom / undefined
axiom ghcBottom : α

-- Unimplemented primitives (GHC built-in ops)
opaque ghcPrimOp (name : String) : α

end GHCCore
```

---

## Step 6: Output Structure

```
output/
  GHCCore/
    Prelude.lean       -- support definitions and axioms
    AST.lean           -- the GHCCore inductive types (Step 2)
  Generated/
    <ModuleName>.lean  -- one file per Haskell module
  lakefile.lean
```

The `lakefile.lean`:

```lean
import Lake
open Lake DSL

package «ghc-core-lean4» where
  name := "ghc-core-lean4"

lean_lib «GHCCore» where

lean_lib «Generated» where
```

---

## Constraints and Non-Goals

- **No `partial def`**: Blaster does not support partial definitions. Every recursive function uses `termination_by <first_arg>` + `decreasing_by sorry`.
- **No re-typechecking of GHC types**: GHC already typechecked the program. The Lean 4 output trusts GHC's types and uses `sorry` or opaque stubs for anything that cannot be mapped cleanly.
- **Coercions are erased**: `Cast` nodes are transparent. Coercion terms are never reconstructed.
- **Unfoldings and rules are dropped**: `CoreRule` and `Unfolding` payloads are not emitted.
- **Laziness is not modeled**: The emitted Lean 4 is strict. Laziness-dependent behaviors are out of scope.
- **The goal is Blaster surface area**, not a fully faithful Haskell semantics in Lean 4.

---

## Worked Example

### Input Haskell

```haskell
fib :: Int -> Int
fib 0 = 1
fib 1 = 1
fib n = fib (n - 1) + fib (n - 2)
```

### GHC Core (simplified)

```
fib = \n -> case n of
  0 -> 1
  1 -> 1
  _ -> (+) (fib ((-) n 1)) (fib ((-) n 2))
```

### Expected Lean 4 output

```lean
def fib (n : Int) : Int :=
  match n with
  | 0 => 1
  | 1 => 1
  | _ =>
    let n1 := n - 1
    let n2 := n - 2
    fib n1 + fib n2
termination_by n
decreasing_by sorry
```

---

## Suggested Implementation Order

1. Write the GHC plugin (or adapt `ghc-dump-core`) to emit JSON per the schema above.
2. Write `emit.py` for a subset: `NonRec`, `Var`, `Lit`, `App`, `Lam`, `Case` with `DEFAULT` only.
3. Test on `fib` and a handful of simple Plinth/Plutus utility functions.
4. Extend to `Rec` / `mutual`, remaining `AltCon` variants, inline `Let`.
5. Add the type mapping table and name sanitizer.
6. Wire up `GHCCore/Prelude.lean` and test that the emitted files load in Lean 4.
7. Run Blaster on a simple property (e.g. `fib 0 = 1`).
