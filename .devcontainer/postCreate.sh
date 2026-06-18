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
