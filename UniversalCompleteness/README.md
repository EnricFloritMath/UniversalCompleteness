# Universal completeness

The reviewer-facing [showcase.lean](showcase.lean) states Section 6, item (1)
of the paper. It defines the frequency set
`Λ = {n + β ({n · α} − 1/2) : n ∈ ℤᵈ}` and all the predicates used in the
theorem, so the statement can be read without following the proof imports.

Under the stated rational-independence conditions and `‖β‖₂ < 1/2`, this
same set is uniformly discrete, has uniform density one, is an `L¹`
Fourier-uniqueness set, and has complete exponentials in `Lᵖ(S)` for every
measurable `S` with `|S| < 1` and every finite `p ≥ 1`.

## Read the statement

In `UniversalCompleteness.universal_completeness`, `Independent` and
`Nonresonant` express the arithmetic hypotheses, while `δ` and `Λ` define
the perturbation. `E Λ` is the family of positive exponentials
`x ↦ exp(2πi ξ · x)`. `UniformlyDiscrete` uses Euclidean separation;
`UniformDensity` counts points in translated half-open cubes and normalizes
by the cube volume. `L1Uniqueness` uses the negative Fourier-sampling sign.
`Complete` and `UniversallyComplete` assert density of the complex linear
span of these exponentials in the relevant `Lᵖ(S)` spaces.

Read the definitions and theorem through `:= by` to compare the precise
Lean statement with the paper.

## Follow the proof

- [Internal/UniversalCompletenessHD/Basic.lean](Internal/UniversalCompletenessHD/Basic.lean)
  exports the library theorem applied by the showcase.
- [Internal/UniversalCompletenessHD/PublicAssembly.lean](Internal/UniversalCompletenessHD/PublicAssembly.lean)
  assembles the higher-dimensional result.
- [GeometryDensity.lean](Internal/UniversalCompletenessHD/GeometryDensity.lean),
  [RecoveryUniqueness.lean](Internal/UniversalCompletenessHD/RecoveryUniqueness.lean),
  and [LpCompleteness.lean](Internal/UniversalCompletenessHD/LpCompleteness.lean)
  contain the density, `L¹` uniqueness, and `Lᵖ` completeness arguments.
- [Internal/OneDimensional/](Internal/OneDimensional/) contains imported
  analytic lemmas.
- [Audit/AxiomAudit.lean](Audit/AxiomAudit.lean) checks and prints the axioms of the
  main library declarations. [ProofAudit/](ProofAudit/) contains a separate
  protected comparison of an underlying library theorem; its
  [README](ProofAudit/README.md) explains the scope and command.

## Check with Lean

From the repository root:

```bash
cd UniversalCompleteness
lake build
lake env lean showcase.lean
lake env lean Audit/AxiomAudit.lean
./Audit/check_source.sh
```

This is an independent Lake project pinned to Lean and Mathlib `v4.31.0`.
The `#print axioms` command in the showcase reports the dependencies of its
public theorem. The protected comparison concerns the underlying library
theorem and does not compare the showcase statement with the paper.
