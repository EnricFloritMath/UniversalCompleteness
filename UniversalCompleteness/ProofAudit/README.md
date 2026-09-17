# Optional proof comparison

[`Challenge.lean`](Challenge.lean) states the type of the underlying
`UniversalCompletenessHD.universal_completeness_higher_dimension_basic`
theorem without importing its proof. [`Solution.lean`](Solution.lean) supplies
that proof from the library. The challenge includes a quantitative count
estimate absent from the current paper-facing
[`showcase.lean`](../showcase.lean). This comparison checks the library theorem,
not the match between the showcase and the paper.

The challenge contains an intentional placeholder. It is outside the default
proof build and is not imported by the showcase.

To run the protected comparison, use a fresh, non-privileged Linux x86_64
checkout with a real `.lake` directory and a working user `systemd` manager.
From this package root:

```bash
./ProofAudit/setup_tools.sh
export PATH="$PWD/.proof-audit-tools/bin:$PATH"
./ProofAudit/run_comparator.sh
```

The scripts use the pinned versions in [`toolchain.env`](toolchain.env) and
[`config.json`](config.json). Do not compile `ProofAudit.Solution` in that
checkout before running the comparator.
