#!/usr/bin/env bash
set -euo pipefail

run_build="false"

while [[ "$#" -gt 0 ]]; do
  case "$1" in
    --build) run_build="true" ;;
    *) echo "usage: $0 [--build]" >&2; exit 2 ;;
  esac
  shift
done

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
package_dir="$(cd "$script_dir/.." && pwd)"

for command_name in jq rg; do
  command -v "$command_name" >/dev/null 2>&1 || {
    echo "missing required command: $command_name" >&2
    exit 1
  }
done

for file in lean-toolchain lakefile.lean lake-manifest.json \
    Audit/AxiomAudit.lean ProofAudit/Challenge.lean ProofAudit/Solution.lean \
    ProofAudit/config.json ProofAudit/toolchain.env ProofAudit/trusted-imports.txt; do
  [[ -f "$package_dir/$file" ]] || {
    echo "missing package artifact: $package_dir/$file" >&2
    exit 1
  }
done

jq empty "$package_dir/lake-manifest.json" \
  "$package_dir/ProofAudit/config.json"

wip_imports="$(rg -n --glob '*.lean' --glob '!.lake/**' \
  --glob '!.proof-audit-tools/**' \
  '^[[:space:]]*import[[:space:]].*(WIP_|WiP_|wip_)' "$package_dir" || true)"
if [[ -n "$wip_imports" ]]; then
  echo "WIP imports are forbidden:" >&2
  echo "$wip_imports" >&2
  exit 1
fi

placeholder_hits="$(rg -n --glob '*.lean' --glob '!**/WIP_*.lean' \
  --glob '!**/ProofAudit/Challenge.lean' --glob '!**/.lake/**' \
  --glob '!**/.proof-audit-tools/**' \
  'sorryAx|(^|[[:space:]])(sorry|admit)([[:space:];]|$)|^[[:space:]]*(axiom|unsafe)[[:space:]]' \
  "$package_dir" || true)"

[[ -z "$placeholder_hits" ]] || {
  echo "Lean source contains placeholder/axiom candidates:" >&2
  echo "$placeholder_hits" >&2
  exit 1
}

if [[ "$run_build" == "true" ]]; then
  (cd "$package_dir" && lake build UniversalCompletenessHD.Basic Audit.AxiomAudit)
fi

printf 'universal-completeness HD source audit passed\n'
