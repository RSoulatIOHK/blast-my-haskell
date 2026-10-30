#!/usr/bin/env bash
set -euo pipefail
[ -f "$HOME/.ghcup/env" ] && . "$HOME/.ghcup/env" || true
export PATH="$HOME/.ghcup/bin:$HOME/.cabal/bin:$HOME/.elan/bin:$HOME/.local/bin:/opt/homebrew/bin:/usr/local/bin:$PATH"
REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
exec python3 "$REPO/scripts/verify.py" "$@"
