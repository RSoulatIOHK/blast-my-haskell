# GHC Core → Lean Verifier (VS Code extension)

Verify Haskell `{- @lean ... -}` annotations through the audited CLI. The
extension waits for a completed `verify.sh --json` result, then shows per-block
CodeLens, gutter icons, and hover details in the original Haskell documents.
It does not use the Lean language server to decide whether verification passed.

## Build and use

From the repository root:

```bash
lake build GhcCoreToLean ghccoretolean
(cd shim && cabal build)
cd vscode-extension
npm ci
npm test
npx @vscode/vsce package --no-dependencies --skip-license
code --install-extension ghccoretolean-vscode-0.5.3.vsix --force
```

Reload the VS Code window after reinstalling. Open the repository as a trusted
workspace, open `tests/fixtures/verification/PureInteger.hs`, and run
**GHC Core → Lean: Verify @lean annotations** from the Command Palette. A
successful check shows `✓ Proved · Lean model (conservative)`.

The active document is saved before verification. Save other modified Haskell
documents first so imported sources match the editor. Use the notification's
**Cancel** action to stop work. The notification shows the current stage and
elapsed seconds; the output channel prints stage changes immediately and a
heartbeat every 15 seconds during longer steps. **Clear Lean diagnostics** also cancels pending
verification. Click a CodeLens to open the full run output.

The Lean4 extension is optional. The host running this extension needs Bash,
Python, the pinned GHC/Lean toolchains, and built project binaries. Z3 is needed
for Blaster tactics. Use macOS/Linux or a VS Code remote host such as a Linux
dev container/WSL; native Windows execution is not tested. **Check Environment**
reports prerequisites and build instructions.

## Read the results

| Display | Meaning |
|---|---|
| Green `Proved · Lean model` | Audited theorem with only allowed standard axioms, in an accepted run |
| Amber `SMT valid` | Solver-backed result; label states whether SMT trust is enabled or required |
| Amber `Admitted` / `Assumed` | Depends on `sorryAx` / another additional axiom; never accepted |
| Red `Refuted · Lean model` | Blaster refuted a property of the generated model |
| Red `Verification error` / `Not verified` | Compilation, proof, or protocol failure; not a refutation claim |
| Amber unsupported, missing theorem, or incomplete status | No accepted verification |

Hover anywhere within an annotation for its theorem names, transitive axioms,
semantic policy, and available Lean output/counterexample. Compiler errors
outside annotations appear at the top of the corresponding Haskell document,
with their original generated-code diagnostic retained. Failures in imports
also produce a summary on the requested entry file.

Every result concerns a **Lean model**. Translation correctness from Haskell
is not certified. Approximate semantics can prove claims that are false in
Haskell. A proved block in a run rejected for another property stays amber;
SMT results stay amber even when explicitly accepted.

## Settings

Settings apply to the active Haskell file's workspace folder, including in
multi-root workspaces.

| Setting | Default | Meaning |
|---|---|---|
| `ghcCoreLean.verifyScriptPath` | `verify.sh` | Audited driver, relative to the file's workspace folder or absolute |
| `ghcCoreLean.semantics` | `conservative` | Refuse known approximations; `approximate` enables exploratory mappings |
| `ghcCoreLean.trustSmt` | `false` | Explicitly accept Blaster results without proof reconstruction |
| `ghcCoreLean.timeoutSeconds` | `600` | Whole-run deadline in seconds, greater than 0 and at most 86400 |

For example, `SmtInteger.hs` reports SMT valid but unaccepted by default.
Enabling `ghcCoreLean.trustSmt` accepts that model result, with its trust label
still visible. `Admitted.hs` remains rejected with either setting. `Overflow.hs`
is refused under conservative semantics.

The old `scriptPath`, `leanDiagnosticQuietMs`, and `leanDiagnosticTimeoutMs`
settings are deprecated and ignored. Set `verifyScriptPath` if the verifier is
outside the workspace root. A custom driver must implement CLI schema version
1, preserve the requested policy, and support SIGTERM cleanup. Point it at
`verify.sh`; `transpile.sh` exports Lean files and is not a verification driver.

## Completion and stale results

The process must finish, output one valid JSON report, and agree with its
reported acceptance through its exit code. The extension validates theorem
statuses against their axiom lists and checks source hashes before publishing.
Unsupported schemas, malformed/truncated output, and missing audits cannot
become editor success markers.

A new run cancels the previous run. Editing any Haskell buffer, changing a
watched Haskell file, clearing diagnostics, or changing verification settings
clears old results and invalidates pending results. Returned imported sources
are watched even outside workspace folders. Invalidation is deliberately broad:
unrelated Haskell edits also clear results. Verification is manual; save does
not automatically trigger a new run.

## Development and checks

```bash
npm test                 # protocol, subprocess, and mocked editor lifecycle tests
npm run test:integration # real GHC → Lean runs through the extension runner
npm run test:host        # installed VS Code, isolated profile and scratch sources
```

The integration checks require the project/toolchain builds above. They cover
proved, trusted/untrusted SMT, admitted, refuted, unsupported, timeout, and
cancelled runs. The editor tests exercise registered commands, hovers, CodeLens,
source edits, imported-buffer changes, late completions, and source hashing at
the VS Code API boundary. The host smoke test opens an isolated VS Code instance
without Lean4 installed and checks proved/SMT/admitted CodeLens, assumption
hovers, and edit invalidation against real CLI runs. It discovers the installed
`code` executable; set `VSCODE_EXECUTABLE` to an explicit VS Code application
executable if needed. Scratch data is deleted on success and retained for
failure diagnosis.

The CLI's semantic and proof policies are documented in the repository's
`docs/verification.md`. The current driver synthesizes a
small Cabal library; arbitrary Cabal project integration remains future work.
