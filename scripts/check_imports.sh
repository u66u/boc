#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

declare -A allowed=(
  [Boc/Scheduler.lean]=""
  [Boc/Heap.lean]="Boc.Scheduler"
  [Boc/Deadlock.lean]="Boc.Scheduler"
  [Boc/Semantics.lean]="Boc.Scheduler"
  [Boc/Progress.lean]="Boc.Semantics"
  [Boc/Theorems.lean]="Boc.Deadlock Boc.Heap Boc.Semantics"
)

fail=0
for f in Boc/*.lean; do
  if [[ ! -v "allowed[$f]" ]]; then
    echo "GATE: $f not in the import DAG table (scripts/check_imports.sh)"
    fail=1
    continue
  fi
  while read -r imp; do
    [[ -z "$imp" ]] && continue
    ok=0
    for a in ${allowed[$f]}; do
      [[ "$imp" == "$a" ]] && ok=1
    done
    if [[ $ok -eq 0 ]]; then
      echo "GATE: $f imports $imp — not in its allowlist (${allowed[$f]:-<none>})"
      fail=1
    fi
  done < <(grep -oE '^import Boc\.[A-Za-z0-9.]*' "$f" | sed 's/^import //')
done
exit $fail
