# Design: devcontainer + extension environment-check (zero-setup sharing)

Date: 2026-06-18
Status: approved (pending spec review)

## Motivation

Sharing the repo with friends is hard because the toolchain is heavy and
multi-language: Lean v4.24.0 (+ the Blaster git dependency), GHC 9.2.7 + cabal,
Python 3, and several built binaries (the Lean transpiler, the Core→JSON shim).
A VS Code extension can't auto-install those (Marketplace extensions are just
JS/assets and shell out to tools that must already exist), and the extension is
repo-bound (it runs the workspace's `transpile.sh` + Lean project). Today a new
contributor faces manual `ghcup`/`elan` setup and a cryptic `transpile.sh failed`
if anything is missing.

Goal: a friend opens the repo and everything works — and, for people running
natively, clear actionable diagnostics instead of opaque failures.

## Decisions (from brainstorming)

- **Dockerfile devcontainer** (ghcup + elan), not Nix.
- **Env-check command**: detect + guide for system tools; **auto-build** (one-click) the repo-local binaries; no silent system installs.
- **Distribution**: the devcontainer **builds and installs the extension from source**; no Marketplace (deferred), no committed binaries.

## Non-goals

Marketplace publishing; Nix; auto-installing system toolchains (ghcup/elan) from the editor; bundling prebuilt native binaries in a VSIX.

## Design

### Component 1 — `.devcontainer/`

**`Dockerfile`** — based on `mcr.microsoft.com/devcontainers/base:ubuntu`:
- `apt-get install` build deps: `curl git build-essential libgmp-dev libtinfo-dev python3 python3-minimal`. Node.js + npm via the devcontainer node feature or apt (needed for the extension build + `vsce`).
- Install **ghcup** non-interactively (`BOOTSTRAP_HASKELL_NONINTERACTIVE=1`), then `ghcup install ghc 9.2.7 --set` and `ghcup install cabal --set`.
- Install **elan** non-interactively (`elan-init.sh -y`); the specific Lean toolchain is fetched lazily from `lean-toolchain` on first `lake` invocation (in postCreate).
- `ENV PATH` includes `~/.ghcup/bin` and `~/.elan/bin`; run installs as the non-root `vscode` user so the toolchains live in that user's home.

**`devcontainer.json`**:
- `build.dockerfile: Dockerfile`.
- `customizations.vscode.extensions`: `["leanprover.lean4"]` — **required**, the verify flow reads Lean LSP diagnostics. (Our own extension is installed via postCreate, since `extensions` only accepts Marketplace IDs.)
- `postCreateCommand: "bash .devcontainer/postCreate.sh"`.
- Reasonable `remoteUser: vscode`.

**`.devcontainer/postCreate.sh`** (idempotent; runs once after the repo is mounted):
1. `lake build` — builds the transpiler `ghccoretolean`, pulls Blaster, and verifies the committed `Spike/` examples.
2. `( cd shim && cabal build )` — the `ghc-core-shim` binary.
3. Build + install our extension:
   `( cd vscode-extension && npm ci && npm run compile && npx --yes @vscode/vsce package --no-dependencies && code --install-extension ghccoretolean-vscode-*.vsix --force )`.
4. Echo a short "ready" message.

The container therefore comes up fully built with both editor extensions present.

### Component 2 — extension environment-check command

Add to `vscode-extension/`:
- **`package.json`**: register command `ghcCoreLean.checkEnvironment`, title `GHC Core → Lean: Check Environment`, in `contributes.commands` (and the command palette).
- **`src/extension.ts`**:
  - A pure-ish helper `describeEnvironment(): EnvReport` shape that gathers checks; keep the *probing* (which/exec/fs) in thin wrappers so the formatting/decision logic is testable.
  - Checks (each → `{ name, ok, fix }`):
    - `lean` / `elan` on PATH (`elan --version` / `lean --version`).
    - `ghc` is 9.2.7 reachable (`ghcup whereis ghc 9.2.7` or `ghc-9.2.7 --version`).
    - `cabal` on PATH.
    - `python3` on PATH.
    - shim binary exists (`find shim/dist-newstyle -name ghc-core-shim -perm -u+x`, mirroring `transpile.sh`).
    - transpiler binary exists (`.lake/build/bin/ghccoretolean`).
  - Output: write the ✓/✗ report (with `fix` strings for missing system tools) to the existing output channel and show it.
  - If system toolchains are present but the **binaries** are missing, `showWarningMessage(..., 'Build now')`; on click, run `lake build` and `cd shim && cabal build` in an integrated terminal (visible progress), not a silent spawn.
  - `runPipeline`'s failure path (`verify`) gains a hint: on failure, suggest running **Check Environment**.

### Component 3 — distribution / docs

- No new distribution mechanism beyond the devcontainer (Component 1, step 3).
- **README**: add a "Quick start (devcontainer)" section — "Reopen in Container; everything builds and the extension installs automatically" — above the manual build steps, which stay for native users.

## Data flow (new-contributor path)
```
clone → "Reopen in Container"
  → Dockerfile: ghcup(GHC 9.2.7, cabal) + elan + node + python
  → postCreate: lake build · shim cabal build · build+install our extension
  → leanprover.lean4 auto-installed
  → open a .hs, run verify → works
(native users: run "Check Environment" → ✓/✗ + fixes / one-click Build now)
```

## Testing / acceptance
- `Dockerfile` / `devcontainer.json` / `postCreate.sh` are syntactically valid (shellcheck-clean script; valid JSON; schema-sane devcontainer).
- Extension still compiles (`tsc --noEmit` clean); the `checkEnvironment` command is registered and runs, producing a correct ✓/✗ report on the current (already-set-up) machine, and the "Build now" path launches the builds.
- **Manual (run once by the user):** "Dev Containers: Rebuild Container", then confirm inside the container that `lake build` and `cd shim && cabal build` succeeded during postCreate, the extension is installed, `leanprover.lean4` is present, and `transpile.sh examples/haskell/Ratio.hs` + verify yields `✅ Valid`. (A full container build can't be run in the authoring environment.)

## Risks / open items
- Container image is large and the build is slow (GHC + Lean toolchains); acceptable for a dev environment, but document the first-build time.
- `code --install-extension` must target the container's VS Code Server in postCreate — standard in devcontainers, but verify in the manual run.
- ghcup/elan non-interactive install flags occasionally change; pin the documented install one-liners and verify in the manual container build.
- Node provisioning: prefer the devcontainer "node" feature over apt if the base image's node is too old for `@vscode/vsce`.
