#!/usr/bin/env bash
set -euo pipefail

echo "→ building the transpiler, verification audit, and Lean tests…"
lake build GhcCoreToLean ghccoretolean

echo "→ building the Core→JSON shim…"
( cd shim && cabal build )

echo "→ building + installing the VS Code extension…"
( cd vscode-extension \
  && npm ci \
  && npm run compile \
  && npx --yes @vscode/vsce package --no-dependencies --skip-license \
  && code --install-extension ghccoretolean-vscode-*.vsix --force )

echo "✅ GhcCoreToLean devcontainer ready — open a .hs and run 'GHC Core → Lean: Verify'."
