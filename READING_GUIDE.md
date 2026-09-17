# Reading the paper and Lean statements together

Compare the paper's higher-dimensional statements in Section 6, items
(1)–(5), with the four reviewer-facing `showcase.lean` files. The article
text is not part of this Lean repository.

| Section 6 item | Showcase | Declaration | What Lean establishes |
| --- | --- | --- | --- |
| (1) | [Universal completeness](UniversalCompleteness/showcase.lean) | `UniversalCompleteness.universal_completeness` | Separation, uniform density one, L¹ uniqueness, and Lᵖ completeness on all measurable sets of measure below one |
| (2) | [Null perturbations](NullPerturbations/showcase.lean) | `NullPerturbations.null_perturbations` | A small-measure witness on which the perturbed frequencies are incomplete in L² |
| (3) | [Integer frequencies](IntegerFrequencies/showcase.lean) | `IntegerFrequencies.integer_frequencies` | Uniform density `v`, L¹ uniqueness, and Lᵖ completeness for subsets of the unit cube |
| (4) | [Sobolev nonuniqueness](PeriodicWeakGaps/showcase.lean) | `PeriodicWeakGaps.sobolev_nonuniqueness` | Nonuniqueness at and below `α = d/2` for every admissible periodic spectrum and uniformly discrete set |
| (5) | [Same showcase](PeriodicWeakGaps/showcase.lean) | `PeriodicWeakGaps.endpoint_nonuniqueness` | The `α = 0` nonuniqueness consequence for every admissible `A` |

## How to read a showcase

Each file explains the mathematical construction, then defines every
project-specific object appearing in its theorem. Read the theorem down to
`:= by` to compare it with the paper. The code after that point proves the
displayed statement from the internal library. Lean checks that connection;
the reader checks that the displayed definitions and quantifiers express the
intended paper claim.

## Notation and quantifiers

The first three showcases represent a real vector as `Fin d → ℝ`; the last
uses Mathlib's Euclidean-space type. Both represent `d` coordinates, and each
theorem assumes `0 < d`. In the first three files, `dot` is the Euclidean
scalar product, `e ξ x` is `exp(2πi ξ·x)`, and `E Λ` is the set of these
positive exponentials. The negative sign in a Fourier sample is expressed by
`star (g x)` for `g ∈ E Λ`.

`Complete Λ S p hp` says that the complex span of the exponential functions
is dense in `Lᵖ(S)`. Its generators are almost-everywhere classes of the
functions in `E Λ`. Items (1) and (3) quantify over every measurable `S` below
their measure threshold and every finite `p ≥ 1`; item (2) produces one `S`
for each positive `ε` and negates completeness at `p = 2`. The `hp` argument
supplies the lower bound needed for the `Lᵖ` topology.

`UniformDensity` in items (1) and (3) uses the same normalized formula: the count
in `x + [0,R)^d`, divided by `R^d`, tends to `D` uniformly in `x`.
Finiteness of the counted set is included so that `ncard` is the ordinary
point count. `L1Uniqueness` and `L1UniquenessOnUnitCube` have different domains
of quantification.

In the fourth showcase, `periodicSpectrum A` denotes `A + ℤᵈ`, and
`PWalpha α S` describes the weighted Fourier-side Paley–Wiener class.
`PW S` is its `α = 0` case. The theorem asks for a continuous representative,
so its value at a chosen point and its vanishing on `Λ` are pointwise claims.

## Check with Lean

Each result folder has its own `lean-toolchain`, `lakefile.lean`, and
`README.md`. From that folder, run `lake build` and then
`lake env lean showcase.lean`. The `#print axioms` commands at the end of
the showcases should report only `propext`, `Classical.choice`, and
`Quot.sound`. The `Audit/` files provide additional local checks. The
`ProofAudit/` comparators in all four result folders concern their underlying
library theorems rather than the paper-facing showcase types.
