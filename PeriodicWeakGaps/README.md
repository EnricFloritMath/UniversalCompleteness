# Periodic weak gaps

The reviewer-facing [showcase.lean](showcase.lean) states Sobolev
nonuniqueness from Section 6, item (4), and its `α = 0` case relevant to
item (5). It uses `S = A + ℤᵈ`, where `A ⊆ [0,1]ᵈ` is measurable and
`0 < |A| < 1`.

For `0 ≤ α ≤ d/2`, every uniformly discrete set `Λ` fails to determine all
continuous functions in `PWalpha α S`: given `x₀ ∉ Λ`, the theorem produces
a function in that class which vanishes on `Λ` and equals `1` at `x₀`.
The second theorem sets `α = 0` and obtains the nonuniqueness conclusion
for `PW S`.

## Read the statements

`PeriodicWeakGaps.sobolev_nonuniqueness` and
`PeriodicWeakGaps.endpoint_nonuniqueness` use `unitCube` for `[0,1]ᵈ`,
`periodicSpectrum` for `A + ℤᵈ`, and `UniformlyDiscrete` for a positive
Euclidean separation between distinct points. `w`, `PWalpha`, and `PW`
define the Sobolev weight, weighted Fourier class, and its `α = 0` case.

Read the definitions and both theorems through `:= by` to compare the
precise Lean conclusions with the paper.

## Follow the proof

- [Internal/PeriodicWeakGapsHD/HigherDim/Basic.lean](Internal/PeriodicWeakGapsHD/HigherDim/Basic.lean)
  exports `SpectralGapsPrelim.HigherDim.Hermite`, the library theorem applied
  by the showcase.
- [Definitions.lean](Internal/PeriodicWeakGapsHD/HigherDim/Definitions.lean)
  and [Setup.lean](Internal/PeriodicWeakGapsHD/HigherDim/Setup.lean) introduce
  the Fourier-space definitions and geometric setup.
- [RecursiveCorrections.lean](Internal/PeriodicWeakGapsHD/HigherDim/RecursiveCorrections.lean)
  constructs the limiting function that vanishes on `Λ`.
- [Internal/OneDimensional/](Internal/OneDimensional/) contains an imported
  exponential-independence result.
- [Audit/AxiomAudit.lean](Audit/AxiomAudit.lean) checks and prints the axioms of the
  main library declarations.
- [ProofAudit/](ProofAudit/) contains an optional protected comparison of the
  underlying library theorem. It does not compare the showcase with the paper.

## Check with Lean

From the repository root:

```bash
cd PeriodicWeakGaps
lake build
lake env lean showcase.lean
lake env lean Audit/AxiomAudit.lean
```

This is an independent Lake project pinned to Lean and Mathlib `v4.31.0`.
The `#print axioms` commands in the showcase report the dependencies of
the two public theorems. For the optional protected comparison, follow
[ProofAudit/README.md](ProofAudit/README.md).
