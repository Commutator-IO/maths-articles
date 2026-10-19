#!/usr/bin/env bash
# Vérifie chaque fichier lecons/**/*.lean contre le Mathlib de ce projet.
#
#   cd lean && ./check.sh
#
# Les avertissements sont des erreurs (un `sorry` en est un), et `sorry`,
# `native_decide` et `axiom` sont refusés avant même la compilation :
# `native_decide` fait confiance au compilateur, un `axiom` est une hypothèse.
set -euo pipefail
cd "$(dirname "$0")"

# Boucle plutôt que mapfile : le bash de macOS (3.2) ne le connaît pas.
files=()
while IFS= read -r f; do files+=("$f"); done < <(find ../lecons -name '*.lean' | sort)
if [ ${#files[@]} -eq 0 ]; then
  echo "Aucun fichier .lean sous lecons/."
  exit 0
fi

if grep -nE '\b(sorry|native_decide)\b|^axiom ' "${files[@]}"; then
  echo "::error::une preuve doit être démontrée et vérifiée par le noyau."
  exit 1
fi

status=0
for f in "${files[@]}"; do
  echo "→ $f"
  if ! lake env lean -DwarningAsError=true "$f"; then
    echo "::error file=${f#../}::échec de la vérification Lean"
    status=1
  fi
done
exit $status
