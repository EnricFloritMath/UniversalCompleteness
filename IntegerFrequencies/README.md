# Integer frequencies

The reviewer-facing [showcase.lean](showcase.lean) states Section 6, item (3)
of the paper. For rationally independent `1, α₁, …, α_d` and
`0 ≤ v ≤ 1`, it selects
`Λᵥ = {n ∈ ℤᵈ : {n · α} ∈ [1 − v, 1)}`. It proves uniform density `v`,
`L¹` Fourier uniqueness, and completeness of its exponentials in `Lᵖ(S)`
for every measurable `S ⊆ [0,1]ᵈ` with `|S| < v` and every finite `p ≥ 1`.

## Read the statement

`IntegerFrequencies.integer_frequencies` uses `Independent` for the arithmetic
hypothesis, `integerΛ` for selected integer vectors, and `Λ` for their real
embedding. `E Λ` is the family of positive exponentials
`x ↦ exp(2πi ξ · x)`. `UniformDensity` counts points in translated half-open
cubes and normalizes by their volume. `L1UniquenessOnUnitCube` uses the
negative Fourier-sampling sign. `Complete` and
`UniversallyCompleteOnUnitCube` assert density of the complex linear span
of these exponentials in the relevant `Lᵖ(S)` spaces.

Read the definitions and theorem through `:= by` to compare the precise
Lean statement with the paper.

## Follow the proof

- [Internal/IntegerFrequenciesHD/Basic.lean](Internal/IntegerFrequenciesHD/Basic.lean)
  exports the library theorem applied by the showcase.
- [Internal/IntegerFrequenciesHD/PublicAssembly.lean](Internal/IntegerFrequenciesHD/PublicAssembly.lean)
  assembles density, `L¹` uniqueness, and `Lᵖ` completeness.
- [CubicalFrequencyDensity.lean](Internal/IntegerFrequenciesHD/CubicalFrequencyDensity.lean),
  [L1Uniqueness.lean](Internal/IntegerFrequenciesHD/L1Uniqueness.lean), and
  [LpCompleteness.lean](Internal/IntegerFrequenciesHD/LpCompleteness.lean)
  contain the three principal arguments.
- [Internal/OneDimensional/](Internal/OneDimensional/) contains imported
  analytic lemmas.
- [Audit/AxiomAudit.lean](Audit/AxiomAudit.lean) checks and prints the axioms of the
  main library declarations. [ProofAudit/](ProofAudit/) contains a separate
  protected comparison of an underlying library theorem; its
  [README](ProofAudit/README.md) explains the scope and command.

## Check with Lean

From the repository root:

```bash
cd IntegerFrequencies
lake build
lake env lean showcase.lean
lake env lean Audit/AxiomAudit.lean
./Audit/check_source.sh
```

This is an independent Lake project pinned to Lean and Mathlib `v4.31.0`.
The `#print axioms` command in the showcase reports the dependencies of its
public theorem. The protected comparison concerns the underlying library
theorem and does not compare the showcase statement with the paper.
