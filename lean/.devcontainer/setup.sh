#!/usr/bin/env bash
# Codespaces / devcontainer setup: elan, the pinned toolchain, the Mathlib build cache, one build.
set -euo pipefail
cd "$(dirname "$0")/.."
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
export PATH="$HOME/.elan/bin:$PATH"
lake exe cache get          # Mathlib's compiled oleans (≈7 GB unpacked); the one slow step
lake build                  # FrcLedger: seconds once the cache is in place
echo "ready: open FrcLedger/Algebra.lean — the infoview shows goal states at the cursor"
