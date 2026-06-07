# GHC Core → Lean Verifier (VS Code extension)

Runs the spike's GHC→Lean pipeline on the active `.hs` file, opens the
generated `.lean` invisibly so the Lean LSP processes it, then mirrors
Lean's diagnostics (✅ Valid, ❌ Falsified + counterexample, errors)
back to the original `.hs` as inline underlines on the corresponding
`{- @lean ... -}` annotation. Hovering on the annotation shows the
full Lean output (incl. counterexamples) in a popover.

## Architecture

```
.hs file
  ↓ command "Verify @lean annotations via Blaster"
transpile.sh
  ↓
.lean file + .lean.map.json (source map: .hs line ranges ↔ .lean line ranges)
  ↓ (extension opens .lean — Lean4 LSP picks it up)
Lean LSP diagnostics (per-line, on the .lean URI)
  ↓ (extension maps each diagnostic back to its source .hs block)
inline diagnostics + hover on the original .hs annotation
```

The source map is what makes the round trip work: `transpile.sh` writes
`${OUT}.map.json` next to the emitted `.lean`, with one entry per
`{- @lean ... -}` block recording `[startLine, endLine]` in both files.

## Setup

```bash
cd vscode-extension
npm install
npm run compile
```

Then either:

- **From the repo**: open the project in VS Code, press `F5` to launch
  an Extension Development Host with the extension loaded.
- **Permanent install**: `vsce package` to make a `.vsix`, then
  `code --install-extension ghccoretolean-vscode-0.1.0.vsix`.

## Use

1. Open the workspace root in VS Code.
2. Ensure the [Lean4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4)
   is installed — its LSP is what produces the underlying diagnostics.
3. Open a `.hs` file with at least one `{- @lean ... -}` block.
4. Command Palette → **GHC Core → Lean: Verify @lean annotations via Blaster**.

## Settings

| key | default | meaning |
|---|---|---|
| `ghcCoreLean.scriptPath` | `transpile.sh` | path to the pipeline driver (relative to workspace root, or absolute) |
| `ghcCoreLean.leanDiagnosticQuietMs` | `2000` | ms of LSP silence before considering diagnostics stable |
| `ghcCoreLean.leanDiagnosticTimeoutMs` | `60000` | upper bound on the wait |

## Known limitations

- Cold-start of `cabal build` + Lean LSP can be 1-2 minutes. Warm runs
  are ~3-5 s. The command is manual on purpose — no auto-run on save.
- Diagnostics are anchored to the **whole `@lean` block**, not to the
  specific line within it that the Lean LSP flagged. The hover shows
  the full text so the line is recoverable visually.
- Multiple `@lean` blocks per file are supported, but if a single
  Lean line lies outside any block it's silently ignored (this shouldn't
  happen — the transpiler-emitted portion is below the blocks — but
  surface as a TODO if it does).
