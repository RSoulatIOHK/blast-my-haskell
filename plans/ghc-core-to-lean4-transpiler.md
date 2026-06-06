# GHC Core → Lean 4 Transpiler

## Goal

Build a transpiler that takes serialized GHC Core (from a GHC plugin or `ghc-dump-core`) and emits Lean 4 source files that can be processed by Blaster, an SMT-backed automated verification tactic for Lean 4.

The purpose is to enable Blaster to verify properties of Haskell programs by working on their GHC Core representation lifted into Lean 4.

**Implementation language: Lean 4.** The entire transpiler (JSON parsing, lowering, emission) is written in Lean and ships as the `ghccoretolean` executable already scaffolded in this repo. We use `Lean.Json` from the standard library to read the serialized Core. There is no Python in the pipeline.

---

## Pipeline Overview

```
Haskell source
  ↓  GHC plugin (emit JSON)
GHC Core (JSON)
  ↓  Lean: Parse.lean      (Lean.Json → GHCCore.CoreProgram)
GHCCore.CoreProgram
  ↓  Lean: Lower.lean      (erase types/dicts, resolve known names)
Lowered program
  ↓  Lean: Emit.lean       (program → Lean 4 source text)
Lean 4 source (.lean)
  ↓
Blaster
```

---

## Step 1: GHC Core Serialization

Use [`ghc-dump-core`](https://hackage.haskell.org/package/ghc-dump-core) (Hackage) as the GHC-side plugin: it already walks a `CoreProgram` and serializes it to a structured ADT. Write a small Haskell shim that translates the `ghc-dump-core` ADT into the JSON schema below, including computing the `role` field for each `Var`. A bespoke GHC plugin can replace the shim later if `ghc-dump-core` proves limiting, but it is **not** needed up front — the shim is what the spike (see implementation order) builds on day one.

The serializer is **faithful**: it preserves type applications, type lambdas, and dictionary arguments exactly as they appear in Core. Erasure happens later, in the Lean lowering pass (Step 4), not here — keeping the JSON faithful means the lowering decisions live in one place and stay revisable.

The JSON schema to target:

```json
{
  "binds": [
    {
      "tag": "NonRec",
      "binder": { "name": "f", "unique": 42, "type": <GHCType>, "role": "id" },
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
{ "tag": "Var",  "var": <Var> }
{ "tag": "Lit",  "lit": <Literal> }
{ "tag": "App",  "fun": <Expr>, "arg": <Expr> }
{ "tag": "Lam",  "binder": <Var>, "body": <Expr> }
{ "tag": "Let",  "bind": <Bind>, "body": <Expr> }
{ "tag": "Case", "scrutinee": <Expr>, "binder": <Var>, "type": <GHCType>, "alts": [<Alt>] }
{ "tag": "Cast", "expr": <Expr> }
{ "tag": "Tick", "expr": <Expr> }
{ "tag": "Type", "type": <GHCType> }
```

Notes:
- `Cast` and `Tick` drop their secondary payload (coercions and ticks are erased). `Cast` is the *only* coercion-related node — there is no separate `Coerce` tag.
- `Type` carries its type argument. It only ever appears as the `arg` of an `App` (a type application) and is erased during lowering.
- A `Lam` may bind a term variable, a type variable, or a dictionary; the `role` field on the binder (`Var`) tells the lowering pass which.

### Var JSON schema

```json
{ "name": "f", "unique": 42, "type": <GHCType>, "role": "id" | "tyVar" | "dict" }
```

The `role` field classifies the variable so lowering can erase the right things:
- `"id"`   — an ordinary term-level value variable.
- `"tyVar"` — a type variable (binder of a type lambda; appears in `Type` nodes).
- `"dict"`  — a typeclass dictionary (GHC names these `$d…`/`$f…`). Treated as erasable: dictionary lambdas and dictionary arguments are dropped, and dictionary-method selections are resolved to Lean operators via the name map (Step 4).

The producer (the `ghc-dump-core` shim, or a bespoke plugin if it later replaces the shim) classifies a binder as `"tyVar"` when GHC's `Var` is a `TyVar`, as `"dict"` when its type's head is a class `TyCon` (or its name has GHC's dictionary prefix), and `"id"` otherwise.

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

Place in `GhcCoreToLean/AST.lean` (the transpiler's in-process copy). The same source is also emitted verbatim to `output/GHCCore/AST.lean` so Blaster, when reading generated files, sees the same inductives under `namespace GHCCore`. Step 7 lists how these stay in sync.

```lean
namespace GHCCore

abbrev Name   := String
abbrev Unique := Nat

inductive VarRole where
  | id
  | tyVar
  | dict
deriving Repr, DecidableEq

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
  role   : VarRole
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
    | type_  : GHCType → Expr      -- type argument, erased during lowering
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

Place in `GhcCoreToLean/Parse.lean`. Parse the JSON produced in Step 1 into `GHCCore.CoreProgram` using `Lean.Json`.

The parser is a set of `fromJson?`-style functions returning `Except String α`. It must handle:
- All `Expr` tags
- Recursive `Bind` groups (lists of pairs)
- All `GHCType` constructors
- All `Literal` variants
- `AltCon` variants
- The `role` field on every `Var` (defaulting to `id` if absent, for forward compatibility)

---

## Step 4: Lowering (Core → Lean-friendly Core)

Place in `GhcCoreToLean/Lower.lean`. **This is the load-bearing step** — the gap between Core's explicitly-typed, dictionary-passing style and Lean's surface syntax lives here, and it must run before emission. It is a `CoreProgram → CoreProgram` (plus a name-resolution side table) transformation.

### 4a. Erase type abstraction and application

Core is in type-passing style: `map @a @b f xs` passes types as ordinary arguments, and polymorphic functions begin with type lambdas (`\@a -> …`). Emitting these as Lean *values* does not typecheck (`map` applied to a type value is a type error). So:

- **Type application** — when lowering `App f (Type t)`, drop the argument entirely: lower to `f`. (Detect by the argument being a `type_` node.)
- **Type lambda** — when lowering `Lam v body` where `v.role = tyVar`, drop the binder: lower to `body`. Lean infers polymorphism implicitly, so the type binder is not reintroduced.

### 4b. Erase dictionary abstraction and application

Typeclass dictionaries also appear as ordinary value arguments and lambdas in Core:

- **Dictionary lambda** — `Lam v body` with `v.role = dict`: drop the binder.
- **Dictionary argument** — `App f d` where `d` lowers to a reference to a dictionary variable (`role = dict`): drop the argument.
- **Dictionary method selection** — applications like `(==) $dEqInt x y` become, after dropping `$dEqInt`, a reference to `(==)`, which the name map (4c) resolves to Lean's `· == ·`.

### 4c. Resolve known names

Maintain extensible mapping tables (a separate `GhcCoreToLean/Maps.lean`, easy to grow):

- **Value/operator map** — GHC global Ids and class methods → Lean terms. e.g. `GHC.Num.+` / `+` → `· + ·`, `GHC.Num.-` → `· - ·`, `==` → `· == ·`, `GHC.Base.id` → `id`. Unmapped global Ids fall back to `GHCCore.ghcPrimOp "<name>"`.
- **Type constructor map** — see Step 5 table (`Maybe`→`Option`, etc.).
- **Data constructor map** — GHC data constructors → Lean constructors, e.g. `Just`→`Option.some`, `Nothing`→`Option.none`, `:`→`List.cons`, `[]`→`List.nil`, `True`→`Bool.true`, `False`→`Bool.false`. This is required for both `App` (constructor calls) and `Alt` patterns; without it `match … | Just x =>` does not resolve.

After lowering, every `var` node either resolves to a known Lean name or to a sanitized local/top-level binder name.

---

## Step 5: Lean 4 Code Emitter

Place in `GhcCoreToLean/Emit.lean`. Consumes the lowered program and produces `.lean` source text (`String`). Operates on already-lowered terms, so it no longer sees type/dict lambdas or type arguments.

### Top-level program

```
CoreProgram → sequence of Lean 4 definitions
```

Each `Bind` becomes one or more `def` declarations.

#### NonRec bind

```
NonRec v e  →  def <sanitize(v.name)> <args...> : <emitType(result)> := <emitExpr(body)>
               [decreasing_by all_goals sorry]   -- only if recursive
```

If `e` is a `Lam`, collect all leading (already type/dict-erased) lambdas as function arguments before emitting the body.

#### Rec bind

```
Rec [(v1,e1), (v2,e2), ...]  →
  mutual
    def <name1> <args...> := <body1>
    decreasing_by all_goals sorry

    def <name2> <args...> := <body2>
    decreasing_by all_goals sorry
  end
```

#### Termination annotation rules

These rules are **verified against Lean v4.24.0**:

- **Determine recursion**: a def is recursive iff its own name (for `Rec`, any name in the group) occurs free in its lowered RHS.
- **Recursive def** → emit `decreasing_by all_goals sorry` and **no** `termination_by`. Omitting `termination_by` lets Lean pick structural recursion when it can and fall back to well-founded otherwise; `all_goals sorry` discharges every residual decrease goal. (Plain `decreasing_by sorry` is **wrong**: with ≥2 recursive calls it leaves later goals unsolved — `error: unsolved goals`. The `all_goals` is required.)
- **Non-recursive def** → emit **no** termination hints. (Emitting `termination_by` here produces `warning: unused termination hints`.)
- Do **not** guess a `termination_by` measure. Core functions often begin with type/dict binders, so "the first argument" is frequently a type variable and useless as a measure; `decreasing_by all_goals sorry` sidesteps the measure entirely.
- Do **not** use `partial def` under any circumstances — Blaster does not support `partial`.

#### Expr emission

(After lowering, `var` carries an already-resolved Lean name or a mapped operator/constructor.)

| Expr | Lean 4 output |
|------|---------------|
| `Var v` (local/top) | `<resolvedName(v)>` |
| `Var v` (mapped op/ctor) | the mapped Lean term (e.g. `Option.some`, `(· + ·)` applied) |
| `Lit (LitInt n)` | `(<n> : Int)` |
| `Lit (LitWord n)` | `(<n> : Nat)` |
| `Lit (LitFloat f)` | `(<f> : Float)` |
| `Lit (LitDouble f)` | `(<f> : Float)` |
| `Lit (LitString s)` | `"<s>"` |
| `Lit (LitChar c)` | `'<c>'` |
| `Lit (LitLabel l)` | `GHCCore.foreignLabel "<l>"` |
| `App f x` | `(<emitExpr f>) (<emitExpr x>)` |
| `Lam v body` | `fun <sanitize(v.name)> => <emitExpr body>` |
| `Let b body` | `let <emitBind b>\n<emitExpr body>` |
| `Case s bnd _ alts` | `match <emitExpr s> with\n<emitAlts alts>` |
| `Cast e` | `<emitExpr e>` |
| `Tick e` | `<emitExpr e>` |
| `Type t` | should not reach the emitter (erased in Step 4); if it does, emit `(GHCCore.typeArg : GHCCore.GHCType)` as a defensive placeholder |

#### Case / Alt emission

```lean
match <scrutinee> with
| <LeanCtor> <binders...> => <rhs>
| <LeanCtor> <binders...> => <rhs>
| _ => <rhs>   -- DEFAULT
```

`DataAlt` constructor names are resolved through the data-constructor map (Step 4c). `LitAlt` becomes a literal pattern (verified: `Int` literal patterns like `| 0 =>` / `| 1 =>` compile in Lean v4.24.0). `DEFAULT` becomes `_`.

#### Let emission (inline)

```lean
let <name> := <rhs>
<body>
```

For `Rec` lets (local mutual recursion), emit a local `let rec` or hoist to a top-level `mutual`; flag as TODO in a comment for now — rare in practice.

#### Type emission

Types are emitted only where Lean requires an explicit annotation (e.g. a top-level def's argument/result types). Otherwise omit. When needed:

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
| `TyCon name args` | `(GHCCore.tyConOpaque "<name>") <args...>` |

Unknown `TyCon`s map to an opaque type via the single `tyConOpaque` family in the Prelude (see Step 6). The type-constructor map is extensible.

#### Name sanitization

GHC names can contain characters illegal in Lean 4 identifiers. Apply:

- Replace `$` with `_dollar_`
- Replace `#` with `_hash_`
- Replace `.` with `_dot_` (qualified names)
- Append `_<unique>` to disambiguate shadowed names
- Wrap in `«...»` if the name is a Lean 4 keyword (`match`, `let`, `fun`, `def`, `if`, `then`, `else`, `by`, `where`, `with`, `do`, `return`, `have`, `show`, `from`, `type`, `sort`, `Prop`, `Type`)

---

## Step 6: Support Definitions

Emitted to `output/GHCCore/Prelude.lean` — this is a target-side artifact, not a transpiler module. These are axioms and stubs the emitted code may reference. Inside the output project, `Prelude.lean` imports `GHCCore.AST` (it refers to `GHCType`).

```lean
import GHCCore.AST

namespace GHCCore

-- Opaque type family for GHC type constructors not mapped to Lean builtins.
-- Used by the emitter as `GHCCore.tyConOpaque "Name" args...`.
opaque tyConOpaque (name : String) : Type → Type

-- Foreign labels (FFI). Needs Inhabited to justify the opaque value.
opaque foreignLabel {α : Type} [Inhabited α] (name : String) : α

-- Type argument placeholder (only used if a Type node escapes lowering).
opaque typeArg : GHCType := GHCType.tyCon "_" []

-- Bottom / undefined.
axiom ghcBottom {α : Type} [Inhabited α] : α

-- Unimplemented primitives (GHC built-in ops) the name map didn't resolve.
opaque ghcPrimOp {α : Type} [Inhabited α] (name : String) : α

end GHCCore
```

Notes (verified against v4.24.0): the `{α : Type} [Inhabited α]` constraints are **required** — `opaque foreignLabel (name : String) : α` / `axiom ghcBottom : α` with a free `α` fail to compile (`failed to synthesize Inhabited α`). `tyConOpaque` is a single opaque type family applied to arguments; the emitter must use exactly this form (there is no `GHCCore.TyCon.«Name»` namespace of constructors).

---

## Step 7: Output Structure

```
GhcCoreToLean/          -- the transpiler itself (Lean source, already scaffolded)
  AST.lean              -- GHCCore inductive types (Step 2); also emitted to output/
  Parse.lean            -- Lean.Json → GHCCore.CoreProgram
  Lower.lean            -- type/dict erasure + name resolution
  Maps.lean             -- extensible GHC → Lean name/type/ctor tables
  Emit.lean             -- lowered program → Lean 4 source text
Main.lean               -- CLI: read JSON file(s), write .lean file(s)

output/                 -- generated artifacts
  GHCCore/
    Prelude.lean        -- support definitions and axioms (Step 6)
    AST.lean            -- the GHCCore inductive types (Step 2)
  Generated/
    <ModuleName>.lean   -- one file per Haskell module
  lakefile.lean
```

The generated `output/lakefile.lean`:

```lean
import Lake
open Lake DSL

package «ghc-core-lean4» where

lean_lib «GHCCore» where

lean_lib «Generated» where
```

Note: `GHCCore.AST` and `GHCCore.Prelude` are *target* modules emitted into `output/` for Blaster to consume. The transpiler's own copy of the AST (Step 2, under `GhcCoreToLean/`) and the emitted `output/GHCCore/AST.lean` are kept in sync.

---

## Constraints and Non-Goals

- **All Lean**: the transpiler is written entirely in Lean 4 using `Lean.Json`. No Python.
- **Type and dictionary erasure**: Core's type-passing and dictionary-passing style is erased during lowering (Step 4). The emitted Lean relies on Lean's own implicit-argument and typeclass inference. This is the central correctness-sensitive transformation, not a footnote.
- **No `partial def`**: Blaster does not support partial definitions. Recursive functions use `decreasing_by all_goals sorry` (and no `termination_by`).
- **No re-typechecking of GHC types**: GHC already typechecked the program. The Lean output trusts GHC's types and uses `sorry` or opaque stubs for anything that cannot be mapped cleanly.
- **Coercions are erased**: `Cast` nodes are transparent. Coercion terms are never reconstructed. There is no `Coerce` node.
- **Unfoldings and rules are dropped**: `CoreRule` and `Unfolding` payloads are not emitted.
- **Laziness is not modeled**: the emitted Lean 4 is strict. Laziness-dependent behaviors are out of scope.
- **Float is emitted but not yet verifiable**: `LitFloat`/`LitDouble` lower to Lean `Float`. Blaster does not yet support `Float` in its SMT backend; Float support will be added to Blaster later. Until then, Float-typed defs transpile and compile but Blaster cannot discharge properties over them.
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

### GHC Core (simplified, after lowering away types/dicts)

```
fib = \n -> case n of
  0 -> 1
  1 -> 1
  _ -> (+) (fib ((-) n 1)) (fib ((-) n 2))
```

`(+)`/`(-)` resolve through the value map to Lean's `+`/`-`.

### Expected Lean 4 output

```lean
def fib (n : Int) : Int :=
  match n with
  | 0 => 1
  | 1 => 1
  | _ => fib (n - 1) + fib (n - 2)
decreasing_by all_goals sorry
```

(Verified: compiles on Lean v4.24.0 with only `declaration uses 'sorry'` warnings. Note: no `termination_by`, and `all_goals sorry` — not bare `sorry`.)

---

## Suggested Implementation Order

The order is **Lean-first and spike-first**: prove the hard part (output that actually typechecks under Blaster) on day one against *real* Core, not a hand-written approximation of it.

1. **End-to-end spike.** Write a one-module `fib.hs`, build it with `ghc-dump-core` enabled, and write a minimal Haskell shim that converts the resulting dump to the JSON schema in Step 1 (including the `role` field). Build `Parse.lean` + a minimal `Lower.lean` + `Emit.lean` for the subset `NonRec`, `Var`, `Lit`, `App`, `Lam`, `Case` (`DEFAULT`/`LitAlt`). Get the emitted `fib.lean` to compile under the real lakefile with Blaster imported, then run Blaster on `fib 0 = 1`. This forces the JSON shim, the type/dict-erasure (Step 4), and the termination (Step 5) decisions all against genuine Core from day one — so the lowering pass is exercised on the actual type-passing/dict-passing shape Core produces, not on a simplified guess.
2. Build the type/dict erasure (Step 4a/4b) and the name maps (Step 4c / `Maps.lean`).
3. Extend to `Rec` / `mutual`, remaining `AltCon` variants (`DataAlt` with the ctor map), inline `Let`.
4. Add the full type mapping table and the name sanitizer.
5. Finalize `GHCCore/Prelude.lean` and confirm the emitted files load in Lean 4.
6. Extend the shim (or, if `ghc-dump-core`'s representation proves insufficient, replace it with a bespoke GHC plugin emitting the Step 1 schema directly) to cover any Core constructs the spike skipped. Then test on a handful of simple Plinth/Plutus utility functions and run Blaster on their properties.
