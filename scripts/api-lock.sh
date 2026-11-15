#!/usr/bin/env bash
# Prints the public API of Inkproof.Viewport, one line per declaration; CI compares it with API.lock.
# Regenerate with: scripts/api-lock.sh > API.lock
set -euo pipefail
cd "$(dirname "$0")/../test"
lake build InkproofViewport inkproof-tools/api-lock >&2
lake exe inkproof-tools/api-lock Inkproof.Viewport Inkproof.Viewport.Proofs
