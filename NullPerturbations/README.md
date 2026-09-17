# Null perturbations

The reviewer-facing [showcase.lean](showcase.lean) states Section 6, item (2)
of the paper. Let `δₙ → 0` as `|n| → ∞` and let
`Λ = {n + δₙ : n ∈ ℤᵈ}`. For every `ε > 0`, the theorem produces a measurable
set `S` with `|S| < ε` on which the exponentials with frequencies in `Λ`
are not complete in `L²(S)`. The set may depend on `ε` and need not be
bounded. Repeated frequencies are allowed.

## Read the statement

`NullPerturbations.null_perturbations` defines `dot`, `e`, and `E` for the
Euclidean scalar product and the exponential family
`x ↦ exp(2πi ξ · x)`. `norm₂` is Euclidean length;
`NullPerturbation` states decay of `δ` at infinity; and `Complete` states
density of the complex span of the restricted exponentials in `Lᵖ(S)`.
The conclusion negates `Complete` at `p = 2`.

Read the definitions and theorem through `:= by` to compare the precise
Lean statement with the paper.

## Follow the proof

- [PublicAssembly.lean](Internal/AsymptoticallyIntegerHD/PublicAssembly.lean)
  defines the library theorem applied by the showcase.
- [Basic.lean](Internal/AsymptoticallyIntegerHD/Basic.lean)
  checks that theorem in an anonymous example.
- [InfiniteAssembly.lean](Internal/AsymptoticallyIntegerHD/InfiniteAssembly.lean)
  constructs the annihilating witness, and
  [NonCompleteness.lean](Internal/AsymptoticallyIntegerHD/NonCompleteness.lean)
  derives the failure of completeness.
- [Audit/](Audit/) contains Lean checks for project-owned axioms and the
  foundational axiom allowlist, plus a printable axiom report. These checks
  are outside the proof-library import closure.
- [ProofAudit/](ProofAudit/) contains an optional protected comparison of the
  underlying library theorem; its [README](ProofAudit/README.md) explains
  the scope and command.

## Check with Lean

From the repository root:

```bash
cd NullPerturbations
lake build
lake env lean showcase.lean
lake env lean Audit/ProjectAxioms.lean
lake env lean Audit/FinalAxiomAllowlist.lean
lake env lean Audit/PrintAxioms.lean
```

This is an independent Lake project pinned to Lean and Mathlib `v4.31.0`.
The `#print axioms` command in the showcase reports the dependencies of its
public theorem. The protected comparison concerns the underlying library
theorem and does not compare the showcase statement with the paper.
