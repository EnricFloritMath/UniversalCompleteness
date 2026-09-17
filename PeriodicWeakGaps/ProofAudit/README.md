# Optional proof comparison

[`Challenge.lean`](Challenge.lean) states the protected challenge for the
`SpectralGapsPrelim.HigherDim.higher_dimensional_nonuniqueness_basic` library
theorem, expressed with internal definitions. It imports only
`PeriodicWeakGapsHD.HigherDim.Definitions` and its dependencies, without the
completed proof. [`Solution.lean`](Solution.lean) applies that proved theorem
to the same statement.

This comparison checks the underlying library theorem. The paper-facing
[`showcase.lean`](../showcase.lean) states the nonuniqueness conclusions for
Section 6 item (4) and the `α = 0` case relevant to item (5). The comparator
does not check the translation to the showcase or its match with the paper.

The challenge contains an intentional placeholder. It is outside the default
proof build and is not imported by the showcase.

## Run

From `PeriodicWeakGaps/` in a fresh, non-privileged Linux x86_64 checkout with
a real `.lake` directory and a working user `systemd` manager, run:

```bash
./ProofAudit/setup_tools.sh
export PATH="$PWD/.proof-audit-tools/bin:$PATH"
./ProofAudit/run_comparator.sh
```

The scripts use the pinned versions in [`toolchain.env`](toolchain.env) and
[`config.json`](config.json). Review the challenge and
[`trusted-imports.txt`](trusted-imports.txt) before running the comparator.
Do not compile `ProofAudit.Solution` in that checkout before running it.
