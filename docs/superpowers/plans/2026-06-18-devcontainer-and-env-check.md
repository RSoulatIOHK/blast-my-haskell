# Devcontainer + Extension Environment-Check — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make the repo zero-setup to share — a `.devcontainer/` that provisions the full toolchain and auto-builds/installs everything (incl. the VS Code extension), plus an extension "Check Environment" command that diagnoses native setups and one-click-builds the binaries.

**Architecture:** A Dockerfile devcontainer installs GHC 9.2.7/cabal (ghcup) + Lean (elan) + Python + Node, and a `postCreate.sh` runs `lake build`, `cd shim && cabal build`, and builds+installs our extension from source. The extension gains a `ghcCoreLean.checkEnvironment` command that probes prerequisites and offers a "Build now" action.

**Tech Stack:** Docker / VS Code Dev Containers, bash, TypeScript (VS Code API).

**Note on testing:** `vscode-extension/` has no test harness, and the container can't be built in the authoring environment. Verification is therefore `tsc --noEmit` + config validation + a one-time manual container rebuild (Task 4). Each task says exactly what to check.

---

## File structure
- Create: `.devcontainer/Dockerfile`, `.devcontainer/devcontainer.json`, `.devcontainer/postCreate.sh`
- Modify: `vscode-extension/package.json` (new command), `vscode-extension/src/extension.ts` (command impl + verify hint)
- Modify: `README.md` (Quick start section)

---

## Task 1: Extension "Check Environment" command

**Files:**
- Modify: `vscode-extension/package.json`
- Modify: `vscode-extension/src/extension.ts`

- [ ] **Step 1: register the command in `package.json`**

In `contributes.commands` (which already has `ghcCoreLean.verify` and `ghcCoreLean.clearDiagnostics`), add a third entry:
```json
{
  "command": "ghcCoreLean.checkEnvironment",
  "title": "Check Environment",
  "category": "GHC Core → Lean"
}
```

- [ ] **Step 2: add the implementation in `src/extension.ts`**

Add these helpers (place them above `function activate`):
```ts
function tryExec(cmd: string): string | null {
  try {
    return cp.execSync(cmd, { stdio: ['ignore', 'pipe', 'ignore'] }).toString().trim();
  } catch {
    return null;
  }
}

interface EnvCheck { name: string; ok: boolean; detail: string; fix: string }

function gatherEnvChecks(ws: string): EnvCheck[] {
  const checks: EnvCheck[] = [];

  const lean = tryExec('lean --version');
  checks.push({ name: 'Lean (elan)', ok: !!lean, detail: lean ?? 'not found',
    fix: 'Install elan: curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh' });

  const ghc = tryExec('ghc-9.2.7 --version')
    ?? (tryExec('ghcup whereis ghc 9.2.7') ? 'ghc 9.2.7 (via ghcup)' : null);
  checks.push({ name: 'GHC 9.2.7', ok: !!ghc, detail: ghc ?? 'not found',
    fix: 'ghcup install ghc 9.2.7 --set' });

  const cabal = tryExec('cabal --version');
  checks.push({ name: 'cabal', ok: !!cabal, detail: cabal?.split('\n')[0] ?? 'not found',
    fix: 'ghcup install cabal --set' });

  const py = tryExec('python3 --version');
  checks.push({ name: 'python3', ok: !!py, detail: py ?? 'not found',
    fix: 'Install Python 3 (e.g. apt install python3 / brew install python3)' });

  const shimDir = path.join(ws, 'shim', 'dist-newstyle');
  const shim = tryExec(`find ${JSON.stringify(shimDir)} -type f -name ghc-core-shim -perm -u+x 2>/dev/null | head -1`);
  checks.push({ name: 'shim binary (ghc-core-shim)', ok: !!(shim && shim.length), detail: shim && shim.length ? shim : 'not built',
    fix: '( cd shim && cabal build )' });

  const transp = path.join(ws, '.lake', 'build', 'bin', 'ghccoretolean');
  const transpOk = fs.existsSync(transp);
  checks.push({ name: 'transpiler binary (ghccoretolean)', ok: transpOk, detail: transpOk ? transp : 'not built',
    fix: 'lake build' });

  return checks;
}

async function checkEnvironment(): Promise<void> {
  const ws = vscode.workspace.workspaceFolders?.[0]?.uri.fsPath;
  if (!ws) {
    vscode.window.showWarningMessage('Open the GhcCoreToLean workspace folder first.');
    return;
  }
  channel.show(true);
  channel.appendLine('--- GHC Core → Lean: environment check ---');
  const checks = gatherEnvChecks(ws);
  for (const c of checks) {
    channel.appendLine(`${c.ok ? '✓' : '✗'} ${c.name}: ${c.detail}`);
    if (!c.ok) channel.appendLine(`    fix: ${c.fix}`);
  }

  const toolsOk = checks.slice(0, 4).every((c) => c.ok);   // lean, ghc, cabal, python3
  const binsOk = checks.slice(4).every((c) => c.ok);       // shim + transpiler
  if (toolsOk && binsOk) {
    vscode.window.showInformationMessage('GHC Core → Lean: environment looks good ✅');
  } else if (toolsOk && !binsOk) {
    const pick = await vscode.window.showWarningMessage(
      'Toolchains present, but the project binaries are not built yet.', 'Build now');
    if (pick === 'Build now') {
      const term = vscode.window.createTerminal('GHC Core → Lean build');
      term.show();
      term.sendText('lake build && ( cd shim && cabal build ) && echo "✅ build complete — run Verify"');
    }
  } else {
    vscode.window.showWarningMessage('Missing toolchains — see the "GHC Core → Lean" output channel for install commands.');
  }
}
```

- [ ] **Step 3: register the command in `activate`**

In `activate`, the `ctx.subscriptions.push(...)` that registers commands already lists `ghcCoreLean.verify` and `ghcCoreLean.clearDiagnostics`. Add alongside them:
```ts
    vscode.commands.registerCommand('ghcCoreLean.checkEnvironment', checkEnvironment),
```

- [ ] **Step 4: add a hint to the verify-failure path**

In `verify`, the `catch` block currently reads:
```ts
  } catch (e) {
    vscode.window.showErrorMessage(`transpile.sh failed: ${(e as Error).message}`);
    return;
  }
```
Change the message to point at the new command:
```ts
  } catch (e) {
    vscode.window.showErrorMessage(
      `transpile.sh failed: ${(e as Error).message} — run "GHC Core → Lean: Check Environment".`);
    return;
  }
```

- [ ] **Step 5: compile and self-check**

Run: `( cd vscode-extension && npx tsc -p ./ --noEmit )`
Expected: no output (clean). Then `( cd vscode-extension && npm run compile )` and confirm `grep -c checkEnvironment out/extension.js` ≥ 1.

- [ ] **Step 6: bump version + commit**

Bump `vscode-extension/package.json` `version` (e.g. `0.4.3` → `0.5.0`).
```bash
cd /Users/romainsoulat/ghcCore-to-lean
git add vscode-extension/package.json vscode-extension/src/extension.ts
git commit -m "feat(extension): Check Environment command (detect prerequisites + Build now)"
```

---

## Task 2: Devcontainer

**Files:**
- Create: `.devcontainer/Dockerfile`
- Create: `.devcontainer/devcontainer.json`
- Create: `.devcontainer/postCreate.sh`

- [ ] **Step 1: `.devcontainer/Dockerfile`**
```dockerfile
FROM mcr.microsoft.com/devcontainers/base:ubuntu-22.04

# System build deps for the GHC/Lean toolchains and the project.
RUN apt-get update && export DEBIAN_FRONTEND=noninteractive \
 && apt-get install -y --no-install-recommends \
      curl git build-essential libgmp-dev libtinfo-dev libncurses-dev \
      python3 ca-certificates \
 && apt-get clean && rm -rf /var/lib/apt/lists/*

USER vscode
ENV PATH=/home/vscode/.ghcup/bin:/home/vscode/.elan/bin:$PATH

# GHC 9.2.7 + cabal via ghcup (non-interactive).
RUN export BOOTSTRAP_HASKELL_NONINTERACTIVE=1 \
      BOOTSTRAP_HASKELL_GHC_VERSION=9.2.7 \
      BOOTSTRAP_HASKELL_INSTALL_NO_STACK=1 \
 && curl --proto '=https' --tlsv1.2 -sSf https://get-ghcup.haskell.org | sh \
 && ghcup install cabal --set

# Lean via elan; the v4.24.0 toolchain (from lean-toolchain) is fetched on first lake use.
RUN curl --proto '=https' --tlsv1.2 -sSf \
      https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
      | sh -s -- -y --default-toolchain none
```

- [ ] **Step 2: `.devcontainer/devcontainer.json`**
```json
{
  "name": "GhcCoreToLean",
  "build": { "dockerfile": "Dockerfile" },
  "features": {
    "ghcr.io/devcontainers/features/node:1": {}
  },
  "customizations": {
    "vscode": {
      "extensions": ["leanprover.lean4"]
    }
  },
  "remoteUser": "vscode",
  "postCreateCommand": "bash .devcontainer/postCreate.sh"
}
```

- [ ] **Step 3: `.devcontainer/postCreate.sh`**
```bash
#!/usr/bin/env bash
set -euo pipefail

echo "→ lake build (transpiler + Blaster + verify Spike examples)…"
lake build

echo "→ building the Core→JSON shim…"
( cd shim && cabal build )

echo "→ building + installing the VS Code extension…"
( cd vscode-extension \
  && npm ci \
  && npm run compile \
  && npx --yes @vscode/vsce package --no-dependencies \
  && code --install-extension ghccoretolean-vscode-*.vsix --force )

echo "✅ GhcCoreToLean devcontainer ready — open a .hs and run 'GHC Core → Lean: Verify'."
```
Make it executable: `chmod +x .devcontainer/postCreate.sh`.

- [ ] **Step 4: validate the config (no container build here)**

Run:
```bash
cd /Users/romainsoulat/ghcCore-to-lean
python3 -c "import json; json.load(open('.devcontainer/devcontainer.json')); print('devcontainer.json: valid JSON')"
bash -n .devcontainer/postCreate.sh && echo "postCreate.sh: valid bash"
command -v shellcheck >/dev/null && shellcheck .devcontainer/postCreate.sh || echo "(shellcheck not installed — skipped)"
```
Expected: valid JSON; valid bash; shellcheck clean if available.

- [ ] **Step 5: commit**
```bash
git add .devcontainer
git commit -m "feat: devcontainer (ghcup+elan) that builds everything and installs the extension"
```

---

## Task 3: README quick-start

**Files:** Modify `README.md`.

- [ ] **Step 1: insert a Quick start section**

Immediately **after** the "How it works" section and **before** "## Prerequisites", insert:
```markdown
## Quick start (devcontainer) — recommended

If you have Docker + the VS Code **Dev Containers** extension: open this repo in
VS Code and run **"Dev Containers: Reopen in Container"**. The container installs
the full toolchain (GHC 9.2.7, Lean v4.24.0, cabal, Python, Node), then its
`postCreate` runs `lake build`, builds the shim, and builds + installs this
project's VS Code extension. When it finishes, open any `examples/haskell/*.hs`
and run **"GHC Core → Lean: Verify"**. (First build takes a few minutes — it
compiles Blaster and both toolchains.)

Running natively instead? Follow Prerequisites + Build below, and use the
**"GHC Core → Lean: Check Environment"** command to see what's missing.
```

- [ ] **Step 2: commit**
```bash
git add README.md
git commit -m "docs: add devcontainer quick-start to the README"
```

---

## Task 4: Manual container verification (run once by the user)

**Files:** none. This step needs Docker + the Dev Containers extension and can't run in the authoring environment.

- [ ] **Step 1:** In VS Code, "Dev Containers: Rebuild Container" on this repo.
- [ ] **Step 2:** Watch the postCreate output — confirm `lake build` ends with the `Spike/` examples `✅ Valid`, `cabal build` produces `ghc-core-shim`, and the extension `vsce package` + `code --install-extension` succeed.
- [ ] **Step 3:** Confirm both extensions are present (`leanprover.lean4` and `iohk-spike.ghccoretolean-vscode`).
- [ ] **Step 4:** Open `examples/haskell/Ratio.hs`, run **Verify**, and confirm `addRatio_correct` shows the green ✓ gutter + `✓ Valid` CodeLens.
- [ ] **Step 5:** Run **Check Environment** and confirm every line is ✓.

If any step fails, report the exact output — the likely culprits are the ghcup/elan non-interactive flags (Dockerfile) or `code --install-extension` targeting (postCreate); fix and rebuild.

---

## Notes for the implementer
- `vscode-extension/package-lock.json` exists, so `npm ci` is correct in postCreate.
- Tasks 1–3 are independent and individually committable; Task 4 is user-run validation.
- Don't attempt to build the Docker image as part of automated verification — it's large/slow and not available here.
