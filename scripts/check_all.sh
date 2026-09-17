#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)

"$repo_root/scripts/build_all.sh"

for package in UniversalCompleteness NullPerturbations IntegerFrequencies PeriodicWeakGaps; do
  echo "==> checking $package/showcase.lean"
  (cd "$repo_root/$package" && lake env lean showcase.lean)
done

(cd "$repo_root/UniversalCompleteness" &&
  ./Audit/check_source.sh &&
  lake env lean Audit/AxiomAudit.lean)
(cd "$repo_root/IntegerFrequencies" &&
  ./Audit/check_source.sh &&
  lake env lean Audit/AxiomAudit.lean)
(cd "$repo_root/NullPerturbations" &&
  lake build Audit.ProjectAxioms Audit.FinalAxiomAllowlist &&
  lake env lean Audit/PrintAxioms.lean)
(cd "$repo_root/PeriodicWeakGaps" &&
  lake env lean Audit/AxiomAudit.lean)
