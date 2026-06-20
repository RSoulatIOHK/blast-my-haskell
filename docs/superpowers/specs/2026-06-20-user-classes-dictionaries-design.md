# User-defined Type Classes (from-Core reconstruction) — Design

**Status:** approved (brainstorming) — 2026-06-20
**Scope:** single-parameter type classes, methods, instances, and `C a =>`-constrained
functions, reconstructed entirely from the existing Core/sidecar dump (no GHC-plugin
changes). Emitted as **idiomatic Lean classes**.

## Problem

User-defined type classes don't transpile today. For

```haskell
class Sized a where size :: a -> Int
data Box = Box Int
instance Sized Box where size (Box n) = n
total :: Sized a => [a] -> Int
total = foldr (\x acc -> size x + acc) 0
boxTotal :: [Box] -> Int
boxTotal = total
```

the transpiler emits (verified):
- the class `Sized` is not captured → leaks as `(GHCCore.tyConOpaque "Sized")` in `total`'s type;
- the instance method body `$csize` *does* translate (a plain def);
- the selector use `size x` in `total` → dangling `size_2132`;
- the `Sized a =>` constraint stays as an un-erased dict-typed parameter.

## Decisions (brainstorming)

1. **Representation:** idiomatic Lean classes. `class Sized a` → `class Sized (a : Type) where size : a → Int`;
   `Sized a =>` → instance-implicit `[Sized a]`; `size x` → `Sized.size x`; GHC instance → Lean `instance`.
2. **Scope:** single-param classes, ≥1 method, instances, constrained functions. **Superclasses,
   multi-param classes, default methods, and same-named methods across classes are out** (follow-ups).
3. **Sourcing:** reconstruct from the Core dump + `Instance` records already captured. **No
   decl-plugin changes.** (Superclasses were dropped from scope precisely because the dump lacks
   `$p` superclass selectors / dict structure — see Reconstruction.)

## Reconstruction (what we read from the dump)

Verified available for `UserClass` (top-level binds): `$csize`, `$fSizedBox`, `total`, `boxTotal`,
plus Typeable junk. The method/superclass *selectors* are class-op Ids, **not** top-level binds.

A new `ClassDecl { name : Name, tyVar : Name, methods : List ClassMethod }` is reconstructed:

- **Class names:** from `Instance.className` (every class that has an instance).
- **Methods of class C:** collect `$c<method>` binds; associate each to its class via the
  instance's dict-builder (`$fSizedBox`'s body references `$csize`); strip `$c` → method name (`size`).
- **Method signature** (for the `class` decl): generalize the `$c<method>` instance-method type by
  abstracting the instance head type to the class type variable
  (`$csize : Box → Int` ⇒ `size : a → Int`). *This is the most heuristic step.* If the bare
  selector reference (`size` in `total`) carries a usable polymorphic type, prefer it; otherwise
  fall back to head-type abstraction. Flagged as the primary correctness risk.
- **method→class map:** `{ size ↦ Sized }`, built from the `$c` binds; used to rewrite bare selector
  references (`size` → `Sized.size`).

`ClassDecl` is added to `AST.lean` and populated in `Parse.lean`/the reconstruction pass (Lean side
only — no JSON-schema/plugin change; reconstruction runs over the parsed `Program`).

## Emission & ordering

Lean classes/instances are **not forward-visible** (established by the Ord work). So `emitFullProgram`
emits in this order:

1. **Data block:** inductives **+ `class C (a : Type) where m : …`** declarations.
2. **`$c` method defs** (concrete bodies — already translate today).
3. **Instances:** `instance : C T where m₁ := <$cm₁ ref>; …` (the Eq/Ord method-finder generalized to
   N methods of an arbitrary class).
4. **Remaining user binds** (`total`, `boxTotal`).

Rewrites:
- **Selector use:** in `emitVar`, a name in the method→class map emits `C.m` (e.g. `Sized.size`).
- **Constrained function:** a binder/def whose type carries `C a =>` gets an instance-implicit
  `[C a]` in its header; the dict is erased from explicit args; the leaked
  `(GHCCore.tyConOpaque "C") …` constraint is dropped.

## Components / interfaces

- `AST.lean`: add `ClassDecl`, `ClassMethod`; extend `Program` (or thread alongside).
- `Reconstruct` (new pass, in `Emit.lean` or a small new module): `CoreProgram × List Instance → List ClassDecl × (Name → Option Name)` (method→class map). One clear responsibility: turn dump artifacts into class info.
- `Emit.lean`: `emitClassDecl`, generalized `emitInstance` (N methods, arbitrary class), `emitVar` selector rewrite, header `[C a]` binder + dict erasure, and the new section ordering in `emitFullProgram`.

## Limitations (documented, deferred)

Superclasses; multi-parameter classes; default methods; ambiguous same-named methods across classes;
classes with no instances used only in constraints (method signatures may be under-determined). Each
is a follow-up; the first three would likely need decl-plugin support.

## Testing

- `#guard`s: ClassDecl reconstruction (names, methods, method→class map); `emitClassDecl` shape;
  generalized `emitInstance` for a 1-method user class; selector rewrite in `emitVar`.
- End-to-end: `examples/haskell/UserClass.hs` transpiles **and compiles** (definition-focused — the
  `class`, `instance`, `total`, `boxTotal` all elaborate). Per the project convention, any `[lean|]`
  property proof is the user's to write; the spike verifies definitions compile.
