#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
project_root="$(cd "$script_dir/.." && pwd)"
config_file="$script_dir/toolchain.env"

# Use an unprivileged, project-local Go installation. This keeps the proof
# audit independent of any unpinned system Go installation.
local_go_bin="$project_root/.proof-audit-tools/go/bin"

if [[ ! -f "$config_file" ]]; then
  echo "missing tracked tool configuration: $config_file" >&2
  exit 1
fi

# shellcheck disable=SC1090
source "$config_file"

required_vars=(
  COMPARATOR_REPOSITORY COMPARATOR_COMMIT
  LEAN4EXPORT_REPOSITORY LEAN4EXPORT_COMMIT
  LANDRUN_MODULE LANDRUN_COMMIT
  NANODA_REPOSITORY NANODA_COMMIT
  GO_VERSION GO_LINUX_AMD64_SHA256
)

for name in "${required_vars[@]}"; do
  value="${!name:-}"
  if [[ -z "$value" || "$value" == REPLACE_* ]]; then
    echo "tool pin $name is unset or still a placeholder" >&2
    exit 1
  fi
done

for command_name in cargo cp curl git lake sha256sum tar; do
  if ! command -v "$command_name" >/dev/null 2>&1; then
    echo "missing required command: $command_name" >&2
    exit 1
  fi
done

tools_dir="$project_root/.proof-audit-tools"
source_dir="$tools_dir/src"
binary_dir="$tools_dir/bin"
mkdir -p "$source_dir" "$binary_dir"

if [[ "$(uname -s)" != "Linux" || "$(uname -m)" != "x86_64" ]]; then
  echo "the pinned local Go bootstrap requires Linux x86_64" >&2
  exit 1
fi

expected_go_version="go version go${GO_VERSION} linux/amd64"
if [[ ! -x "$local_go_bin/go" ]] ||
    [[ "$($local_go_bin/go version 2>/dev/null || true)" != "$expected_go_version" ]]; then
  go_archive="$tools_dir/go${GO_VERSION}.linux-amd64.tar.gz"
  go_stage="$tools_dir/go-stage"
  curl --fail --location --output "$go_archive" \
    "https://go.dev/dl/go${GO_VERSION}.linux-amd64.tar.gz"
  printf '%s  %s\n' "$GO_LINUX_AMD64_SHA256" "$go_archive" | sha256sum --check
  rm -rf "$go_stage"
  mkdir -p "$go_stage"
  tar -C "$go_stage" -xzf "$go_archive"
  rm -rf "$tools_dir/go"
  mv "$go_stage/go" "$tools_dir/go"
  rmdir "$go_stage"
  rm "$go_archive"
fi
export PATH="$local_go_bin:$PATH"

if [[ "$(go version)" != "$expected_go_version" ]]; then
  echo "failed to select the pinned local Go toolchain" >&2
  exit 1
fi

checkout_tool() {
  local repository="$1"
  local destination="$2"
  local commit="$3"

  if [[ ! -d "$destination/.git" ]]; then
    git clone "$repository" "$destination"
  fi
  git -C "$destination" fetch origin "$commit"
  git -C "$destination" checkout --detach "$commit"
  if [[ "$(git -C "$destination" rev-parse HEAD)" != "$commit" ]]; then
    echo "resolved commit does not match requested pin for $destination" >&2
    exit 1
  fi
}

comparator_source="$source_dir/comparator"
exporter_source="$source_dir/lean4export"
nanoda_source="$source_dir/nanoda"

checkout_tool "$COMPARATOR_REPOSITORY" "$comparator_source" "$COMPARATOR_COMMIT"
checkout_tool "$LEAN4EXPORT_REPOSITORY" "$exporter_source" "$LEAN4EXPORT_COMMIT"
checkout_tool "$NANODA_REPOSITORY" "$nanoda_source" "$NANODA_COMMIT"

cp "$project_root/lean-toolchain" "$exporter_source/lean-toolchain"
cp "$project_root/lean-toolchain" "$comparator_source/lean-toolchain"

(
  cd "$exporter_source"
  lake build lean4export
)
(
  cd "$comparator_source"
  lake build comparator
)

cp "$exporter_source/.lake/build/bin/lean4export" "$binary_dir/lean4export"
cp "$comparator_source/.lake/build/bin/comparator" "$binary_dir/comparator"

GOBIN="$binary_dir" go install "$LANDRUN_MODULE@$LANDRUN_COMMIT"

(
  cd "$nanoda_source"
  cargo build --release --locked
)
cp "$nanoda_source/target/release/nanoda_bin" "$binary_dir/nanoda_bin"

printf 'Installed pinned proof-audit tools in %s\n' "$binary_dir"
printf 'Review ProofAudit/README.md before running untrusted solution code.\n'
