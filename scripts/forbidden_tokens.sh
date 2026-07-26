#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

if grep -nE '\b(sorry|admit|native_decide)\b|\b(unsafe|partial) (def|instance|theorem|lemma)\b|^[[:space:]]*axiom\b|@\[implemented_by' Boc/*.lean Boc.lean; then
  echo "GATE: forbidden token found (see matches above)"
  exit 1
fi
exit 0
