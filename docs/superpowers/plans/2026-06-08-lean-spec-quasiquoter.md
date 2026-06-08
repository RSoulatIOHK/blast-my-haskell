# `[lean| … |]` Quasi-Quoter Specs — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the `{- @lean … -}` comment notation with a first-class Template Haskell quasi-quoter `[lean| … |]` that records Lean properties at compile time, so the transpiler (not a perl regex) emits the theorems and builds the diagnostic source map.

**Architecture:** A new in-repo package `lean-spec` exports a declaration quasi-quoter whose `quoteDec` captures the source line via `TH.location` and, via `runIO`, writes the raw property text to `$LEAN_SPEC_DIR/<Module>/<line>.lean` (expanding to no declarations). `transpile.sh` sets/clears `LEAN_SPEC_DIR` and adds `lean-spec` to the sandbox build. The transpiler reads those files, emits each as a theorem inside the module `namespace` (reusing the existing user-type/ctor/external-type resolution), and writes `<out>.map.json`. The `@lean` and ctor-rewrite perl passes are deleted. No GHC plugin changes.

**Tech Stack:** Haskell (GHC 9.2.7, template-haskell, directory, filepath), Lean 4 (transpiler), bash (transpile.sh).

---

## File Structure

- **Create** `shim/lean-spec/lean-spec.cabal` — package definition.
- **Create** `shim/lean-spec/src/Lean/Spec.hs` — `lean` quasi-quoter (the only new logic).
- **Modify** `transpile.sh` — add `lean-spec` dep + `cabal.project` package; set/clear `LEAN_SPEC_DIR`; delete the two perl passes; keep `end <Module>` append.
- **Modify** `GhcCoreToLean/Emit.lean` — expose `resolveSpecText` (apply the existing post-passes to one spec string).
- **Modify** `Main.lean` — read spec files, append theorems inside the namespace, write `<out>.map.json`.
- **Migrate** `examples/haskell/{Ratio.hs, OperatorCommons.hs, RatioSpec/MaxMinOverArithmetics.hs}` — `{- @lean -}` → `[lean| |]`.

---

## Task 1: `lean-spec` package + the `lean` quasi-quoter

**Files:**
- Create: `shim/lean-spec/lean-spec.cabal`
- Create: `shim/lean-spec/src/Lean/Spec.hs`

- [ ] **Step 1: Write the cabal file**

`shim/lean-spec/lean-spec.cabal`:
```cabal
cabal-version:      2.4
name:               lean-spec
version:            0.1.0.0

library
    exposed-modules:    Lean.Spec
    build-depends:      base, template-haskell, directory, filepath
    default-language:   Haskell2010
    hs-source-dirs:     src
```

- [ ] **Step 2: Write the quasi-quoter**

`shim/lean-spec/src/Lean/Spec.hs`:
```haskell
{-# LANGUAGE TemplateHaskell #-}

-- | A declaration quasi-quoter for embedding Lean property text in Haskell.
-- Usage (top level): @[lean| theorem foo : … := by blaster |]@.
-- At compile time it records the raw text to @$LEAN_SPEC_DIR/<Module>/<line>.lean@
-- and expands to no declarations. Outside the transpile sandbox (no
-- @LEAN_SPEC_DIR@) it is a no-op.
module Lean.Spec (lean) where

import Language.Haskell.TH (Dec, Loc (..), Q, location, runIO)
import Language.Haskell.TH.Quote (QuasiQuoter (..))
import System.Directory (createDirectoryIfMissing)
import System.Environment (lookupEnv)
import System.FilePath ((</>))

lean :: QuasiQuoter
lean =
  QuasiQuoter
    { quoteExp  = \_ -> fail "lean: use [lean| … |] only at top level (declaration position)"
    , quotePat  = \_ -> fail "lean: declaration-only quasi-quoter"
    , quoteType = \_ -> fail "lean: declaration-only quasi-quoter"
    , quoteDec  = leanDec
    }

leanDec :: String -> Q [Dec]
leanDec txt = do
  loc <- location
  let modName   = loc_module loc
      startLine = fst (loc_start loc)   -- the `[lean|` line
      endLine   = fst (loc_end loc)     -- the `|]` line
  runIO $ do
    mdir <- lookupEnv "LEAN_SPEC_DIR"
    case mdir of
      Nothing  -> pure ()
      Just dir -> do
        let d = dir </> modName
        createDirectoryIfMissing True d
        -- Filename encodes the full source-span lines so the transpiler can
        -- build the map's `hs` range (opener..closer) for the squiggle.
        writeFile (d </> (show startLine ++ "-" ++ show endLine ++ ".lean")) txt
  pure []
```

- [ ] **Step 3: Verify it builds**

Run: `( cd shim/lean-spec && cabal build ) 2>&1 | tail -3`
Expected: builds successfully (a `Linking`/`Built` style success, no errors).

- [ ] **Step 4: Commit**

```bash
git add shim/lean-spec
git commit -m "feat(lean-spec): TH quasi-quoter recording [lean| … |] specs via runIO"
```

---

## Task 2: Wire `lean-spec` into the sandbox build + set `LEAN_SPEC_DIR`

**Files:**
- Modify: `transpile.sh` (cabal heredoc `build-depends`; `cabal.project` heredoc `packages`; before `cabal build`)

- [ ] **Step 1: Add the dependency and package**

In `transpile.sh`, in the `transpile-sandbox.cabal` heredoc, change the `build-depends` line to:
```
    build-depends:      base, ghc-dump-core, decl-plugin, lean-spec
```
In the `cabal.project` heredoc, add the package path under `packages:`:
```
    ${REPO}/shim/decl-plugin
    ${REPO}/shim/lean-spec
```

- [ ] **Step 2: Set and clear `LEAN_SPEC_DIR` before the build**

In `transpile.sh`, immediately after the existing `export GHC_DECL_DUMP_DIR=...` line, add:
```bash
# Per-spec dump dir for the `lean` quasi-quoter. Cleared each run; the cp-staging
# of every source forces recompilation, so all specs re-dump fresh.
export LEAN_SPEC_DIR="${SANDBOX}/.leanspecs"
rm -rf "$LEAN_SPEC_DIR"
mkdir -p "$LEAN_SPEC_DIR"
```

- [ ] **Step 3: Verify the sandbox still builds an existing example**

Run: `./transpile.sh examples/haskell/Ratio.hs 2>&1 | tail -4`
Expected: still succeeds and prints `wrote …/Ratio.lean` (the old `{- @lean -}` path is untouched in this task, so Ratio still transpiles as before).

- [ ] **Step 4: Commit**

```bash
git add transpile.sh
git commit -m "build: add lean-spec to the transpile sandbox and set LEAN_SPEC_DIR"
```

---

## Task 3: Integration check — a `[lean| |]` block dumps a spec file

**Files:**
- Create (temporary): `examples/haskell/SpecSmoke.hs`

- [ ] **Step 1: Write a probe module**

`examples/haskell/SpecSmoke.hs`:
```haskell
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
module SpecSmoke where

import Lean.Spec (lean)

doubleN :: Int -> Int
doubleN n = n + n

[lean|
theorem doubleN_even : ∀ (n : Int), doubleN n = 2 * n := by blaster
|]
```

- [ ] **Step 2: Build it through the sandbox and check the dumped spec**

Run:
```bash
./transpile.sh examples/haskell/SpecSmoke.hs >/dev/null 2>&1
find .transpile-sandbox/.leanspecs/SpecSmoke -name '*.lean' -exec sh -c 'echo "== $1 =="; cat "$1"' _ {} \;
```
Expected: one file named `<start>-<end>.lean` (the `[lean|` and `|]` source lines, e.g. `9-11.lean`) whose contents are exactly:
```
theorem doubleN_even : ∀ (n : Int), doubleN n = 2 * n := by blaster
```

- [ ] **Step 3: Clean up the probe**

```bash
rm -f examples/haskell/SpecSmoke.hs GhcCoreToLean/Generated/SpecSmoke.lean*
```
(No commit — this task only verifies Tasks 1–2 wired up.)

---

## Task 4: Transpiler reads specs, emits theorems, writes the map

**Files:**
- Modify: `GhcCoreToLean/Emit.lean` (expose a spec-text resolver)
- Modify: `Main.lean` (read specs, append theorems, write `.map.json`)

- [ ] **Step 1: Expose `resolveSpecText` from Emit.lean**

In `GhcCoreToLean/Emit.lean`, immediately before `def emitFullProgram`, add (the three `resolveUserTypes`/`resolveUserCtors`/`resolveExternalTypes` already exist as `private`; this wrapper composes them and is the only new public surface):
```lean
/-- Apply the same name-resolution post-passes used on emitted bodies to a
    single user spec string: local types → bare, imported types → `M.T`,
    user ctors → `T.C`. -/
def resolveSpecText (typeDecls : List DataDecl) (extTypes : List (String × String))
    (s : String) : String :=
  resolveExternalTypes extTypes (resolveUserCtors typeDecls (resolveUserTypes typeDecls s))
```
If `resolveUserTypes`/`resolveUserCtors`/`resolveExternalTypes` are declared `private`, drop the `private` keyword on those three defs so `resolveSpecText` can call them (they remain in the `GHCCore` namespace).

- [ ] **Step 2: Verify Emit still builds**

Run: `lake build ghccoretolean 2>&1 | tail -2`
Expected: `Build completed successfully`.

- [ ] **Step 3: Add spec loading + emission + map writing to Main.lean**

In `Main.lean`, add this helper after `loadLeanImports`:
```lean
/-- Read recorded specs for `moduleName` from
    `$LEAN_SPEC_DIR/<module>/<start>-<end>.lean`, sorted by start line. Each
    entry is `(hsStartLine, hsEndLine, leanText)`. -/
def loadSpecs (moduleName : Option String) : IO (List (Nat × Nat × String)) := do
  let some m := moduleName | pure []
  let some dir ← IO.getEnv "LEAN_SPEC_DIR" | pure []
  let modDir := System.FilePath.join dir m
  if !(← modDir.pathExists) then pure [] else
  let entries ← modDir.readDir
  let mut specs : List (Nat × Nat × String) := []
  for e in entries do
    let stem := e.fileName.dropRight 5            -- strip ".lean"
    match stem.splitOn "-" with
    | [s, en] =>
      match s.toNat?, en.toNat? with
      | some sl, some el => specs := (sl, el, ← IO.FS.readFile e.path) :: specs
      | _, _             => pure ()
    | _ => pure ()
  pure (specs.toArray.qsort (·.1 < ·.1)).toList
```

Then, in `runTranspile`, replace the final write block. Find (the current code, after the cross-module work):
```lean
    let header     := s!"import Lean\nimport Blaster\n{depImports}\n"
    IO.FS.writeFile output (header ++ nsOpen ++ crib ++ body ++ "\n")
    IO.println s!"wrote {output}"
    pure 0
```
Replace with:
```lean
    let header     := s!"import Lean\nimport Blaster\n{depImports}\n"
    -- Core emitted content (everything before the appended specs).
    let pre := header ++ nsOpen ++ crib ++ body ++ "\n"
    -- Append each spec as a theorem inside the namespace; record line ranges.
    let specs ← loadSpecs moduleName
    let mut out := pre
    let mut leanCursor := (pre.splitOn "\n").length            -- 1-based next line
    let mut blocks : List (Nat × Nat × Nat × Nat) := []        -- hsS hsE leanS leanE
    for (hsStart, hsEnd, raw) in specs do
      let resolved := Emit.resolveSpecText userProg.typeDecls extTypes raw
      let nLines   := (resolved.splitOn "\n").length
      let leanS    := leanCursor + 1                            -- blank separator first
      let leanE    := leanS + nLines - 1
      out := out ++ "\n" ++ resolved ++ "\n"
      blocks := (hsStart, hsEnd, leanS, leanE) :: blocks
      leanCursor := leanCursor + 1 + nLines
    IO.FS.writeFile output out
    -- Source map sidecar (same schema the VS Code extension already consumes).
    let blockJson := String.intercalate ",\n    " (blocks.reverse.map fun (hs, he, ls, le) =>
      s!"\{ \"hs\": [{hs}, {he}], \"lean\": [{ls}, {le}] }")
    let mapJson := s!"\{\n  \"haskellPath\": \"\",\n  \"leanPath\": \"{output}\",\n  \"blocks\": [\n    {blockJson}\n  ]\n}\n"
    IO.FS.writeFile (output.toString ++ ".map.json") mapJson
    IO.println s!"wrote {output}"
    pure 0
```

- [ ] **Step 4: Verify the transpiler builds**

Run: `lake build ghccoretolean 2>&1 | tail -2`
Expected: `Build completed successfully`.

- [ ] **Step 5: Commit**

```bash
git add GhcCoreToLean/Emit.lean Main.lean
git commit -m "feat(transpiler): emit [lean| |] specs as theorems and write the source map"
```

---

## Task 5: Delete the perl passes from transpile.sh

**Files:**
- Modify: `transpile.sh` (remove the `@lean` extraction perl and the ctor-rewrite perl inside `emit_module`)

- [ ] **Step 1: Remove both perl heredocs**

In `transpile.sh`'s `emit_module` function, delete the entire first `perl - "$src" "$out" <<'PERL_EOF' … PERL_EOF` block (the `@lean` extractor + map writer) and the entire `if [[ -f "$decls" ]]; then perl - "$out" "$decls" <<'PERL_EOF' … PERL_EOF fi` block (the ctor rewriter). Keep the `LEAN_IMPORTS=… "$TRANSPILER" …` call and the `printf '\nend %s\n' "$mod" >>"$out"` line. The transpiler now produces the `.map.json` and resolves ctors itself.

- [ ] **Step 2: Verify a spec round-trips end to end**

Run (re-create the probe from Task 3, transpile, inspect):
```bash
cat > examples/haskell/SpecSmoke.hs <<'EOF'
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
module SpecSmoke where
import Lean.Spec (lean)
doubleN :: Int -> Int
doubleN n = n + n
[lean|
theorem doubleN_even : ∀ (n : Int), doubleN n = 2 * n := by blaster
|]
EOF
./transpile.sh examples/haskell/SpecSmoke.hs 2>&1 | tail -3
echo "--- generated tail ---"; tail -6 GhcCoreToLean/Generated/SpecSmoke.lean
echo "--- map ---"; cat GhcCoreToLean/Generated/SpecSmoke.lean.map.json
lake build GhcCoreToLean.Generated.SpecSmoke 2>&1 | grep -E "Valid|error" | head
```
Expected: the generated file ends with the theorem inside `namespace SpecSmoke … end SpecSmoke`; the `.map.json` has one block with plausible `hs`/`lean` ranges; `lake build` reports `✅ Valid`.

- [ ] **Step 3: Clean up the probe and commit**

```bash
rm -f examples/haskell/SpecSmoke.hs GhcCoreToLean/Generated/SpecSmoke.lean*
git add transpile.sh
git commit -m "refactor(transpile.sh): drop the @lean and ctor-rewrite perl passes"
```

---

## Task 6: Migrate the example modules

**Files:**
- Modify: `examples/haskell/Ratio.hs`, `examples/haskell/OperatorCommons.hs`, `examples/haskell/RatioSpec/MaxMinOverArithmetics.hs`

- [ ] **Step 1: Convert each `{- @lean … -}` to `[lean| … |]`**

For each file: add `{-# LANGUAGE QuasiQuotes #-}` and `{-# LANGUAGE TemplateHaskell #-}` at the top (after any existing `OPTIONS_GHC`), add `import Lean.Spec (lean)` with the other imports, and replace each `{- @lean <BODY> -}` with:
```
[lean|
<BODY>
|]
```
keeping `<BODY>` byte-for-byte (the theorem text is unchanged). Note: for the indented-layout modules (`OperatorCommons`, `MaxMinOverArithmetics`), the `[lean| … |]` must sit at the module's top-level column, same as the surrounding declarations.

- [ ] **Step 2: Verify each transpiles and builds**

Run:
```bash
for m in Ratio OperatorCommons RatioSpec/MaxMinOverArithmetics; do
  ./transpile.sh "examples/haskell/$m.hs" >/dev/null 2>&1 && echo "$m: transpiled" || echo "$m: FAILED"
done
lake build GhcCoreToLean.Generated.Ratio GhcCoreToLean.Generated.OperatorCommons GhcCoreToLean.Generated.MaxMinOverArithmetics 2>&1 | grep -E "Valid|Falsified|error" | head -20
```
Expected: all transpile; Ratio's `addRatio_correct` and the MaxMin lemmas are `✅ Valid`; `operatorFee_positive` is `❌ Falsified` unless its precondition was added (pre-existing, unrelated).

- [ ] **Step 3: Commit**

```bash
git add examples/haskell/Ratio.hs examples/haskell/OperatorCommons.hs examples/haskell/RatioSpec/MaxMinOverArithmetics.hs
git commit -m "examples: migrate {- @lean -} blocks to [lean| … |]"
```

---

## Task 7: Full verification

**Files:** none (verification only)

- [ ] **Step 1: Multi-function property proves**

Create `examples/haskell/MultiProp.hs`:
```haskell
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
module MultiProp where
import Lean.Spec (lean)
f :: Int -> Int
f x = x + 1
g :: Int -> Int
g x = x - 1
[lean|
theorem f_g_inverse : ∀ (x : Int), f (g x) = x ∧ g (f x) = x := by blaster
|]
```
Run: `./transpile.sh examples/haskell/MultiProp.hs >/dev/null 2>&1 && lake build GhcCoreToLean.Generated.MultiProp 2>&1 | grep -E "Valid|error"`
Expected: `✅ Valid` (a property naming two functions).

- [ ] **Step 2: Cross-module spec still proves with clean axioms**

Run (reuses the cross-module machinery; create a tiny importer with a `[lean| |]` calling an imported function), then:
```bash
cat > /tmp/axc.lean <<'EOF'
import GhcCoreToLean.Generated.MultiProp
#print axioms MultiProp.f_g_inverse
EOF
lake env lean /tmp/axc.lean 2>&1 | grep -iE "axiom|sorry"
```
Expected: `depends on axioms: [Blaster.Tactic.blasterProven]` — no `sorryAx`.

- [ ] **Step 3: `.map.json` correctness**

Run: `cat GhcCoreToLean/Generated/MultiProp.lean.map.json` and confirm the single block's `hs` start line equals the line of `[lean|` in `MultiProp.hs` (open the file to compare).
Expected: `hs` start matches the `[lean|` line.

- [ ] **Step 4: Whole-project regression**

Run: `lake build 2>&1 | tail -1; echo "exit $?"`
Expected: `Build completed successfully`, exit 0.

- [ ] **Step 5: Clean up probes and commit verification artifacts if any**

```bash
rm -f examples/haskell/MultiProp.hs GhcCoreToLean/Generated/MultiProp.lean* /tmp/axc.lean
```

---

## Notes for the implementer
- The VS Code extension is intentionally unchanged: it still runs `transpile.sh`, parses the `wrote <entry>.lean` line, and reads `<out>.map.json`. Only the *producer* of the map moved (perl → transpiler).
- `haskellPath` in the emitted map is left `""` because the transpiler doesn't know the original `.hs` path; if the extension requires it, pass the source path to the transpiler as a 4th arg in a follow-up (out of scope here — confirm the extension only uses `blocks`/`leanPath`).
- Out of scope: GHC type-checking of spec text; editor highlighting inside `[lean| |]`.
