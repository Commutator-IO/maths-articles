#!/usr/bin/env bash
# Checks every lecons/**/*.lean file against this project's Mathlib.
#
#   cd lean && ./check.sh
#
# Warnings are errors (a `sorry` is one), and `sorry`, `native_decide` and
# `axiom` are refused before compiling anything: `native_decide` trusts the
# compiler, and an `axiom` is an assumption.
set -euo pipefail
cd "$(dirname "$0")"

# A loop rather than mapfile: macOS's bash (3.2) does not have it.
files=()
while IFS= read -r f; do files+=("$f"); done < <(find ../lecons -name '*.lean' | sort)
if [ ${#files[@]} -eq 0 ]; then
  echo "No .lean file under lecons/."
  exit 0
fi

if grep -nE '\b(sorry|native_decide)\b|^axiom ' "${files[@]}"; then
  echo "::error::every proof must be complete and checked by the kernel."
  exit 1
fi

status=0
for f in "${files[@]}"; do
  echo "→ $f"
  if ! lake env lean -DwarningAsError=true "$f"; then
    echo "::error file=${f#../}::Lean check failed"
    status=1
  fi
done
exit $status
