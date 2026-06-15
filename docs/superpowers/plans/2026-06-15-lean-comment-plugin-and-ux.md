# `{- @lean -}` Source Plugin + Gutter/CodeLens UX — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add a first-class `{- @lean … -}` comment notation (read by a GHC source plugin, no import/pragma/dep) that coexists with the `[lean| |]` quasi-quoter, and replace the editor's wavy-underline feedback with a gutter icon plus a CodeLens that shows a falsified property's counterexample.

**Architecture:** A new in-repo GHC source plugin `GhcSpecDump` (`parsedResultAction`) lexes each module's source buffer, finds `{- @lean … -}` block comments, and `runIO`-writes their inner text to `$LEAN_SPEC_DIR/<Module>/<start>-<end>.lean` — the *same* contract the `lean` quasi-quoter already uses, so the transpiler's spec-read + `.map.json` are unchanged. The VS Code extension is refactored from "apply wavy-underline decorations" to "compute per-block outcomes → drive gutter-icon decorations + a CodeLens provider."

**Tech Stack:** Haskell (GHC 9.2.7 plugin API — `GHC.Plugins`, `GHC.Parser.Lexer`), bash (transpile.sh), TypeScript (VS Code extension API: decorations, CodeLens).

**Two independent parts.** Part A (plugin + pipeline) and Part B (extension) are separable and can be built/verified independently. Do A first (it produces the data B's CodeLens benefits from), but B does not depend on A's code.

---

## Part A — `{- @lean -}` source plugin

### File structure (Part A)
- Create `shim/spec-plugin/spec-plugin.cabal`, `shim/spec-plugin/cabal.project`, `shim/spec-plugin/GhcSpecDump.hs`.
- Modify `transpile.sh` (sandbox `build-depends`, `cabal.project` packages, `ghc-options`).

### Task A1: `spec-plugin` package + the source plugin

**Files:**
- Create: `shim/spec-plugin/spec-plugin.cabal`
- Create: `shim/spec-plugin/cabal.project`
- Create: `shim/spec-plugin/GhcSpecDump.hs`

- [ ] **Step 1: cabal files** (mirror the sibling `decl-plugin`)

`shim/spec-plugin/spec-plugin.cabal`:
```cabal
cabal-version:      2.4
name:               spec-plugin
version:            0.1.0.0
synopsis:           GHC source plugin that records {- @lean … -} block comments
                    to $LEAN_SPEC_DIR for the ghcCoreToLean transpiler.

library
    exposed-modules:    GhcSpecDump
    build-depends:      base >=4.16 && <5, directory, filepath,
                        ghc  >=9.2 && <9.3
    default-language:   Haskell2010
    ghc-options:        -Wall -Wno-unused-imports
```
`shim/spec-plugin/cabal.project`:
```
with-compiler: ghc-9.2.7

packages: .
```

- [ ] **Step 2: the plugin** `shim/spec-plugin/GhcSpecDump.hs`

> **API-VERIFY (the one fragile part):** the comment-lexing calls below are written against the GHC 9.2 API but the exact signatures of `mkParserOpts` / `lexTokenStream` / the `ITblockComment` constructor MUST be confirmed against the installed GHC 9.2.7 (`ghc` package haddock or `~/.elan`/global package db). Iterate until it compiles. The structure (lex `ms_hspp_buf`, keep comments, filter block comments, write files) is the contract; adapt the call shapes.

```haskell
{-# LANGUAGE LambdaCase #-}

-- | A GHC source plugin: for every `{- @lean <text> -}` block comment in a
-- module, write <text> to $LEAN_SPEC_DIR/<Module>/<start>-<end>.lean (the same
-- contract the `lean` quasi-quoter uses). No-op when LEAN_SPEC_DIR is unset, so
-- the plugin is harmless outside the transpile sandbox.
module GhcSpecDump (plugin) where

import Data.Char        (isSpace)
import Data.List        (stripPrefix)
import Data.Maybe       (mapMaybe)
import System.Directory (createDirectoryIfMissing)
import System.Environment (lookupEnv)
import System.FilePath  ((</>))

import GHC.Plugins
import GHC.Parser.Lexer   (lexTokenStream, ParseResult(..), mkParserOpts)
import GHC.Data.StringBuffer (StringBuffer)
import GHC.Types.SrcLoc
import GHC.Parser.Errors.Ppr ()  -- may be unneeded; remove if it doesn't resolve

plugin :: Plugin
plugin = defaultPlugin
  { pluginRecompile    = purePlugin
  , parsedResultAction = \_ ms pm -> do
      dflags <- getDynFlags
      liftIO (dumpSpecs dflags ms)
      pure pm
  }

dumpSpecs :: DynFlags -> ModSummary -> IO ()
dumpSpecs dflags ms =
  lookupEnv "LEAN_SPEC_DIR" >>= \case
    Nothing  -> pure ()
    Just dir -> case ms_hspp_buf ms of
      Nothing  -> pure ()
      Just buf -> do
        let modName = moduleNameString (moduleName (ms_mod ms))
            file    = ms_hspp_file ms
            loc     = mkRealSrcLoc (mkFastString file) 1 1
            -- VERIFY: mkParserOpts arity in 9.2.7. The intent is "lexer opts
            -- that keep comments". In 9.2 it is roughly:
            --   mkParserOpts warningFlags extensionFlags
            --                safeImports keepRawTokenStream rawTokenStream warnIsError
            -- Use the module's flags; set the comment-keeping Bool True.
            popts   = mkParserOpts (warningFlags dflags) (extensionFlags dflags)
                                   False True True False
        case lexTokenStream popts buf loc of
          POk _ toks -> do
            let specs = mapMaybe leanComment toks
            mapM_ (writeSpec dir modName) specs
          PFailed _  -> pure ()

-- A located block comment that starts with `@lean`. Returns (startLine, endLine, innerText).
leanComment :: Located Token -> Maybe (Int, Int, String)
leanComment (L l tok) = case tok of
  ITblockComment s _ -> do            -- VERIFY: constructor name/arity in 9.2.7
    let body = stripBlock s           -- drop `{-` … `-}`
    rest <- stripPrefix "@lean" (dropWhile isSpace body)
    rsl  <- realSpan l
    Just (srcSpanStartLine rsl, srcSpanEndLine rsl, trim rest)
  _ -> Nothing
 where
  realSpan sp = case sp of RealSrcSpan r _ -> Just r; _ -> Nothing

-- Strip the leading `{-` and trailing `-}` (if present) from a raw block-comment lexeme.
stripBlock :: String -> String
stripBlock s0 =
  let s1 = maybe s0 id (stripPrefix "{-" s0)
      s2 = reverse (maybe (reverse s1) id (stripPrefix "}-" (reverse s1)))
  in s2

trim :: String -> String
trim = f . f where f = reverse . dropWhile isSpace

writeSpec :: FilePath -> String -> (Int, Int, String) -> IO ()
writeSpec dir modName (s, e, txt) = do
  let d = dir </> modName
  createDirectoryIfMissing True d
  writeFile (d </> (show s ++ "-" ++ show e ++ ".lean")) txt
```

- [ ] **Step 3: build the package.** Run: `( cd shim/spec-plugin && cabal build ) 2>&1 | tail -5`
Expected: builds. **If the lexer calls don't compile, this is the expected hard part — adjust `mkParserOpts`/`lexTokenStream`/`ITblockComment` to the real 9.2.7 signatures (check `ghc` haddock) until it builds.** Report the final shapes you used.

- [ ] **Step 4: commit**
```bash
git add shim/spec-plugin
git commit -m "feat(spec-plugin): GHC source plugin recording {- @lean -} comments"
```

### Task A2: wire the plugin into transpile.sh and verify end-to-end

**Files:** Modify `transpile.sh`.

- [ ] **Step 1: add dep, package, and ghc-options.**
- In the `transpile-sandbox.cabal` heredoc, change `build-depends` to include `spec-plugin`:
  ```
      build-depends:      base, ghc-dump-core, decl-plugin, lean-spec, spec-plugin
  ```
- In the `cabal.project` heredoc `packages:` list, add:
  ```
      ${REPO}/shim/spec-plugin
  ```
- In the same heredoc's `ghc-options`, add the comment-keeping flag and the plugin:
  ```
      ghc-options:        -fplugin GhcDump.Plugin -fplugin GhcDeclDump -fplugin GhcSpecDump -fkeep-raw-token-stream
  ```

- [ ] **Step 2: verify a comment-only module round-trips (no import/pragma/dep).**
```bash
cat > examples/haskell/CommentProbe.hs <<'EOF'
module CommentProbe where

tripleN :: Int -> Int
tripleN n = n + n + n

{- @lean
theorem tripleN_eq : ∀ (n : Int), tripleN n = 3 * n := by blaster
-}
EOF
./transpile.sh examples/haskell/CommentProbe.hs 2>&1 | tail -3
echo "--- dumped spec ---"; find .transpile-sandbox/.leanspecs/CommentProbe -type f -exec cat {} \;
echo "--- generated tail ---"; tail -6 GhcCoreToLean/Generated/CommentProbe.lean
echo "--- map ---"; cat GhcCoreToLean/Generated/CommentProbe.lean.map.json
lake build GhcCoreToLean.Generated.CommentProbe 2>&1 | grep -E "Valid|error" | head
```
Expected: the dumped spec file contains exactly `theorem tripleN_eq : ∀ (n : Int), tripleN n = 3 * n := by blaster`; the generated `.lean` has that theorem inside `namespace CommentProbe … end CommentProbe`; the `.map.json` `blocks` is non-empty with `hs` spanning the comment's opener→closer lines (7–9); `lake build` → `✅ Valid`. Crucially the probe has **no `import`, no `LANGUAGE` pragma, no dep** — proving the comment path is self-contained.

If nothing is dumped, the plugin isn't extracting comments — return to A1 Step 2 and fix the lexer API against 9.2.7 (this is where the API risk surfaces).

- [ ] **Step 3: clean up + commit.**
```bash
rm -f examples/haskell/CommentProbe.hs GhcCoreToLean/Generated/CommentProbe.lean*
git add transpile.sh
git commit -m "build: inject GhcSpecDump plugin + -fkeep-raw-token-stream into the sandbox"
```

### Task A3: coexistence test (both notations in one file)

**Files:** none committed (verification only).

- [ ] **Step 1: a file using BOTH `{- @lean -}` and `[lean| |]`.**
```bash
cat > examples/haskell/BothNotations.hs <<'EOF'
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
module BothNotations where
import Lean.Spec (lean)

f :: Int -> Int
f x = x + 1

{- @lean
theorem f_succ : ∀ (x : Int), f x = x + 1 := by blaster
-}

[lean|
theorem f_succ2 : ∀ (x : Int), f x - 1 = x := by blaster
|]
EOF
./transpile.sh examples/haskell/BothNotations.hs >/dev/null 2>&1
echo "specs: $(ls .transpile-sandbox/.leanspecs/BothNotations | wc -l | tr -d ' ')"
echo "theorems in output: $(grep -c '^theorem' GhcCoreToLean/Generated/BothNotations.lean)"
lake build GhcCoreToLean.Generated.BothNotations 2>&1 | grep -c "✅ Valid"
rm -f examples/haskell/BothNotations.hs GhcCoreToLean/Generated/BothNotations.lean*
```
Expected: `specs: 2`, `theorems in output: 2`, and `2` Valid — both recorders feed the same dir, both theorems emit and prove. (No commit; this validates A1+A2.)

---

## Part B — Extension UX (gutter icon + CodeLens counterexample)

### File structure (Part B)
- Create `vscode-extension/media/pass.svg`, `vscode-extension/media/fail.svg`.
- Modify `vscode-extension/src/extension.ts` (decoration types; per-block outcome capture; CodeLens provider; provider registration in `activate`).
- Recompile to `vscode-extension/out/extension.js` (`npm run compile`).

> Read `vscode-extension/src/extension.ts` fully first. Known anchors: `successDecoration`/`failureDecoration` (wavy `textDecoration`, ~lines 25–34); the per-block decoration application loop (~lines 200–266) that already computes which blocks passed/failed from the mapped Lean diagnostics; `readSourceMap`; the per-`.hs`-URI decoration cache (re-applied on editor switch). VS Code UI cannot be unit-tested here — verification is `tsc` compile + the manual steps in B3.

### Task B1: gutter icons replace the wavy underline

**Files:** Create `vscode-extension/media/pass.svg`, `vscode-extension/media/fail.svg`; Modify `vscode-extension/src/extension.ts`.

- [ ] **Step 1: add SVG assets.**
`vscode-extension/media/pass.svg`:
```svg
<svg xmlns="http://www.w3.org/2000/svg" width="16" height="16" viewBox="0 0 16 16"><path fill="#2ecc71" d="M6.4 11.2 3.2 8l1.13-1.13L6.4 8.94l5.27-5.27L12.8 4.8z"/></svg>
```
`vscode-extension/media/fail.svg`:
```svg
<svg xmlns="http://www.w3.org/2000/svg" width="16" height="16" viewBox="0 0 16 16"><path fill="#e74c3c" d="M12 4.4 11.6 4 8 7.6 4.4 4 4 4.4 7.6 8 4 11.6l.4.4L8 8.4l3.6 3.6.4-.4L8.4 8z"/></svg>
```

- [ ] **Step 2: replace the decoration types** in `extension.ts`. Change `successDecoration`/`failureDecoration` from wavy underline to gutter icons (keep the overview-ruler tick):
```ts
const successDecoration = vscode.window.createTextEditorDecorationType({
  gutterIconPath: vscode.Uri.file(path.join(__dirname, '..', 'media', 'pass.svg')),
  gutterIconSize: 'contain',
  overviewRulerColor: 'rgba(46, 204, 113, 0.7)',
  overviewRulerLane: vscode.OverviewRulerLane.Right,
});
const failureDecoration = vscode.window.createTextEditorDecorationType({
  gutterIconPath: vscode.Uri.file(path.join(__dirname, '..', 'media', 'fail.svg')),
  gutterIconSize: 'contain',
  overviewRulerColor: 'rgba(231, 76, 60, 0.7)',
  overviewRulerLane: vscode.OverviewRulerLane.Right,
});
```

- [ ] **Step 3: apply the gutter decoration to the block's FIRST line only** (a gutter icon shows once per line; applying to the whole range would icon every line). In the decoration-application loop, build each decoration's range as a single-line range at `block.hs[0] - 1` (0-based) instead of the whole `hs[0]..hs[1]` span. Concretely, where the code currently pushes a range spanning the block, replace with:
```ts
const firstLine = Math.max(0, block.hs[0] - 1);
const gutterRange = new vscode.Range(firstLine, 0, firstLine, 0);
// push gutterRange into successRanges/failureRanges by outcome (as today)
```

- [ ] **Step 4: compile.** Run: `( cd vscode-extension && npm run compile ) 2>&1 | tail -2`
Expected: compiles (the pre-existing `setTimeout` type warnings are unrelated and don't block emit; confirm `out/extension.js` updated).

- [ ] **Step 5: commit.**
```bash
git add vscode-extension/media/pass.svg vscode-extension/media/fail.svg vscode-extension/src/extension.ts vscode-extension/out/extension.js
git commit -m "feat(extension): gutter ✓/✗ icons instead of wavy underline"
```

### Task B2: CodeLens with the counterexample above each property

**Files:** Modify `vscode-extension/src/extension.ts`.

- [ ] **Step 1: capture per-block outcomes.** Where the loop currently decides pass/fail per block from the mapped Lean diagnostics, also record the failure message. Add a module-level cache keyed by `.hs` URI string:
```ts
interface BlockOutcome { hsStartLine: number; ok: boolean; detail: string }  // detail = one-line counterexample/message
const outcomesByUri = new Map<string, BlockOutcome[]>();
```
In the loop, push `{ hsStartLine: block.hs[0], ok, detail }` where `detail` is the matched Lean diagnostic message compacted to one line (`msg.replace(/\s+/g, ' ').trim().slice(0, 200)`); for passing blocks `detail = ''`. After the loop, `outcomesByUri.set(doc.uri.toString(), outcomes)` and fire the CodeLens change emitter (Step 2).

- [ ] **Step 2: register a CodeLens provider** (add near `activate`):
```ts
const codeLensEmitter = new vscode.EventEmitter<void>();
class SpecCodeLensProvider implements vscode.CodeLensProvider {
  onDidChangeCodeLenses = codeLensEmitter.event;
  provideCodeLenses(doc: vscode.TextDocument): vscode.CodeLens[] {
    const outcomes = outcomesByUri.get(doc.uri.toString()) ?? [];
    return outcomes.map((o) => {
      const line = Math.max(0, o.hsStartLine - 1);
      const range = new vscode.Range(line, 0, line, 0);
      const title = o.ok ? '✓ Valid' : `✗ Falsified — ${o.detail}`;
      return new vscode.CodeLens(range, { title, command: '' });
    });
  }
}
```
In `activate(context)` register it and wire the emitter so `outcomesByUri` updates refresh the lenses:
```ts
context.subscriptions.push(
  vscode.languages.registerCodeLensProvider({ language: 'haskell', scheme: 'file' }, new SpecCodeLensProvider()),
);
```
(`codeLensEmitter.fire()` is called at the end of Step 1's outcome update.)

- [ ] **Step 3: compile.** Run: `( cd vscode-extension && npm run compile ) 2>&1 | tail -2` → compiles, `out/extension.js` updated.

- [ ] **Step 4: commit.**
```bash
git add vscode-extension/src/extension.ts vscode-extension/out/extension.js
git commit -m "feat(extension): CodeLens shows ✓ Valid / ✗ Falsified + counterexample above each property"
```

### Task B3: manual verification (VS Code UI)

**Files:** none. (VS Code decorations/CodeLens have no headless test; verify by hand.)

- [ ] **Step 1: build an example with a known pass and a known fail.** Use `examples/haskell/OperatorCommons.hs`: with `maxFee > 0 →` present it proves; commented out it falsifies. Transpile + `lake build` both ways to populate diagnostics.
- [ ] **Step 2: in VS Code** (Extension Development Host or installed build), open the `.hs`, run the verify command, and confirm:
  - A green ✓ gutter icon (line-number margin) on a passing property's first line; a red ✗ on a failing one; **no wavy underline**.
  - A CodeLens above each property: `✓ Valid` for the pass, `✗ Falsified — <counterexample>` for the fail.
  - Switch to another editor and back: icons + CodeLenses re-appear (persisted via `outcomesByUri`).
- [ ] **Step 3:** if all three hold, the feature is done. (No commit.)

---

## Notes for the implementer
- The `lean-spec` quasi-quoter and the transpiler/`.map.json` path are unchanged — both notations write the identical `<Module>/<start>-<end>.lean` files, and force-recompile in transpile.sh already guarantees the plugin re-fires each run.
- Part A's only real risk is the GHC 9.2.7 lexer API (A1 Step 2 / A2 Step 2). Budget iteration there; everything else is mechanical.
- Part B can't be unit-tested; rely on `tsc` compile + the B3 manual checks. Keep the pre-existing `setTimeout` diagnostics out of scope.
