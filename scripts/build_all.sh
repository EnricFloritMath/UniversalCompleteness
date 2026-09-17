#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)

packages=(
  "UniversalCompleteness"
  "NullPerturbations"
  "IntegerFrequencies"
  "PeriodicWeakGaps"
)

for package in "${packages[@]}"; do
  echo "==> lake build ${package}"
  (cd "${repo_root}/${package}" && lake build)
done
