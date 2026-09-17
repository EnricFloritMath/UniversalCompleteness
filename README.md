# Higher-dimensional spectral gaps in Lean

This repository contains four Lean 4 proof projects for the higher-dimensional
statements in Section 6 of the paper. The `showcase.lean` in each result folder
is the reviewer-facing entry point: it gives the definitions and theorem
statement needed to compare the formal claim with the paper.

The internal Lean files may use different numbering and definitions for
concepts. To assess the correctness of the claimed statements as stated in
the paper, the reader need only check the showcase files.

| Section 6 item | Lean statement | Result |
| --- | --- | --- |
| (1) | [UniversalCompleteness/showcase.lean](UniversalCompleteness/showcase.lean) | Universal completeness of a perturbed lattice |
| (2) | [NullPerturbations/showcase.lean](NullPerturbations/showcase.lean) | Noncompleteness for perturbations tending to zero |
| (3) | [IntegerFrequencies/showcase.lean](IntegerFrequencies/showcase.lean) | Universal integer frequencies of prescribed density |
| (4), (5) | [PeriodicWeakGaps/showcase.lean](PeriodicWeakGaps/showcase.lean) | Sobolev nonuniqueness for periodic spectra |

The first three showcases state all conclusions of their corresponding
Section 6 items. The fourth proves the nonuniqueness conclusion for periodic
weak gaps at and below the critical Sobolev exponent `α = d/2` in item (4),
together with its `α = 0` case relevant to item (5). The
[reading guide](READING_GUIDE.md) spells out the scope and notation of each
Lean statement.

Each folder is an independent Lake project with a pinned Lean toolchain and
Mathlib dependency:

- `showcase.lean` gives the public statement and proves it from the library.
- `Internal/` contains the Lean proof. Supporting imported lemmas, where needed,
  are under `Internal/OneDimensional/`.
- `Audit/` contains Lean axiom checks and, in some folders, a source check.
- `ProofAudit/` in each result folder contains
  an optional protected comparison of the underlying library theorem. These
  comparisons do not check the paper-facing showcase types themselves.

## Build and check

From the repository root, build all four projects with:

```bash
./scripts/build_all.sh
```

To build all projects and check every showcase and the standard source and
axiom audits, run:

```bash
./scripts/check_all.sh
```

The source checks in `check_all.sh` also require `jq` and `rg` (ripgrep).

To check one public statement, run from its result folder, for example:

```bash
cd IntegerFrequencies
lake build
lake env lean showcase.lean
```

The same two Lake commands work in the other result folders. Each showcase
ends with `#print axioms` commands; the expected reported axioms are
`propext`, `Classical.choice`, and `Quot.sound`. The result-folder READMEs
give the corresponding proof entry points and further audit commands.

## Reading order

1. Read the relevant item among the higher-dimensional statements in Section 6
   of the paper.
2. Read the matching `showcase.lean` through its theorem statement, before
   `:= by`. Compare the definitions and quantifiers with the paper.
3. Follow that folder's `README.md` to the proof modules in `Internal/`.

Lean checks the proof of the displayed statement. Comparing that displayed
statement with the paper remains the reader's mathematical review task.
