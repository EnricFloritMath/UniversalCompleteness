# Optional proof comparison

[`Challenge.lean`](Challenge.lean) states the type of the underlying
`AsymptoticallyIntegerHD.theorem_1_4_higher_dimension` theorem without
importing its proof. [`Solution.lean`](Solution.lean) applies that library
theorem to the identical statement. The challenge imports
`AsymptoticallyIntegerHD.Completeness`, which defines the restricted `L²`
completeness predicate but does not import the target proof.

This comparison checks the library theorem. The paper-facing
[`showcase.lean`](../showcase.lean) uses a different presentation of the decay
condition and completeness predicate; the comparator does not check that
translation or the match between the showcase and the paper.

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
[`config.json`](config.json). Review the challenge and
[`trusted-imports.txt`](trusted-imports.txt) before running the comparator.
Do not compile `ProofAudit.Solution` in that checkout before running it.
