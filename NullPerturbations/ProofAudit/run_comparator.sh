#!/usr/bin/env bash
set -euo pipefail

if [[ "$#" -gt 1 ]]; then
  echo "usage: $0 [path-to-config.json]" >&2
  exit 2
fi

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
project_root="$(cd "$script_dir/.." && pwd)"
config_file="${1:-$script_dir/config.json}"
comparator_binary="$project_root/.proof-audit-tools/bin/comparator"
trusted_imports_file="$script_dir/trusted-imports.txt"

if [[ "$(uname -s)" != "Linux" ]]; then
  echo "high-assurance comparator wrapper requires Linux" >&2
  exit 1
fi
if [[ "${EUID:-$(id -u)}" -eq 0 ]]; then
  echo "do not run comparator as a privileged user" >&2
  exit 1
fi

for command_name in awk find grep jq lake landrun lean4export nanoda_bin sha256sum systemd-run; do
  if ! command -v "$command_name" >/dev/null 2>&1; then
    echo "missing required command: $command_name" >&2
    exit 1
  fi
done
if [[ ! -x "$comparator_binary" ]]; then
  echo "missing comparator binary; run ProofAudit/setup_tools.sh first" >&2
  exit 1
fi
if [[ ! -f "$config_file" ]]; then
  echo "missing comparator configuration: $config_file" >&2
  exit 1
fi
if [[ ! -f "$trusted_imports_file" ]]; then
  echo "missing trusted import list: $trusted_imports_file" >&2
  exit 1
fi

jq -e '
  (.challenge_module | type == "string" and length > 0) and
  (.solution_module | type == "string" and length > 0) and
  (.theorem_names | type == "array" and length > 0) and
  (.permitted_axioms | type == "array")
' "$config_file" >/dev/null

challenge_module="$(jq -r '.challenge_module' "$config_file")"
solution_module="$(jq -r '.solution_module' "$config_file")"
challenge_source="$project_root/${challenge_module//./\/}.lean"
solution_source="$project_root/${solution_module//./\/}.lean"

if [[ ! -f "$challenge_source" || ! -f "$solution_source" ]]; then
  echo "challenge or solution source path does not match config modules" >&2
  echo "expected: $challenge_source" >&2
  echo "expected: $solution_source" >&2
  exit 1
fi

while IFS= read -r imported_module; do
  [[ -z "$imported_module" ]] && continue
  if ! grep -Fxq "$imported_module" "$trusted_imports_file"; then
    echo "challenge imports module not listed as trusted: $imported_module" >&2
    exit 1
  fi
done < <(awk '/^[[:space:]]*import[[:space:]]/ { for (i = 2; i <= NF; i++) { if ($i ~ /^--/) break; print $i } }' "$challenge_source")

while IFS= read -r imported_module; do
  if [[ "$imported_module" == "$challenge_module" ]]; then
    echo "solution must not import the challenge module" >&2
    exit 1
  fi
done < <(awk '/^[[:space:]]*import[[:space:]]/ { for (i = 2; i <= NF; i++) { if ($i ~ /^--/) break; print $i } }' "$solution_source")

solution_path="${solution_module//./\/}"
solution_artifact=""
if [[ -L "$project_root/.lake" ]]; then
  echo "protected Comparator rejects symlinked .lake: $project_root/.lake" >&2
  exit 1
fi
if [[ -d "$project_root/.lake" ]]; then
  set +e
  solution_artifact="$(find -L "$project_root/.lake" \
    \( -path "*/$solution_path.olean" -o -path "*/$solution_path.ilean" \) \
    -print -quit 2>/dev/null)"
  solution_scan_status=$?
  set -e
  if [[ "$solution_scan_status" -ne 0 ]]; then
    echo "protected Comparator rejects unsafe symlink traversal under .lake" >&2
    exit 1
  fi
fi
if [[ -n "$solution_artifact" ]]; then
  echo "solution Lean artifact already exists in this environment; use a fresh checkout: $solution_artifact" >&2
  exit 1
fi

echo "Proof-audit input hashes:"
sha256sum "$challenge_source" "$solution_source" "$config_file" \
  "$trusted_imports_file" "$script_dir/toolchain.env" \
  "$project_root/lean-toolchain"

echo "Running comparator in the documented systemd socket-family guard."
echo "Confirm this environment is fresh and the challenge import closure is trusted."

cd "$project_root"
systemd-run \
  --property=RestrictAddressFamilies=~AF_UNIX \
  --user \
  --pty \
  -E "PATH=$PATH" \
  --working-directory "$project_root" \
  -- bash -c 'lake env "$1" "$2"' bash "$comparator_binary" "$config_file"
