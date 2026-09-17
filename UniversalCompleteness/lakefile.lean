import Lake

open Lake DSL

package "UniversalCompletenessHDVerification" where
  version := v!"0.1.0"

require "leanprover-community" / "mathlib" @ git "v4.31.0"

/-- One-dimensional completeness and uniqueness lemmas. -/
lean_lib «Theorem12» where
  srcDir := "Internal/OneDimensional"
  globs := #[.submodules `Theorem12]

/-- One-dimensional Fourier and density lemmas. -/
lean_lib «Theorem14» where
  srcDir := "Internal/OneDimensional"
  globs := #[.submodules `Theorem14]

/-- Pointwise ergodic lemmas for torus rotations. -/
lean_lib «SpectralGapsPrelim» where
  srcDir := "Internal/OneDimensional"
  globs := #[.submodules `SpectralGapsPrelim]

/-- Higher-dimensional torus, Fourier, and ergodic lemmas. -/
lean_lib «IntegerFrequenciesHD» where
  srcDir := "Internal"
  globs := #[.submodules `IntegerFrequenciesHD]

@[default_target]
lean_lib «UniversalCompletenessHD» where
  srcDir := "Internal"
  globs := #[.submodules `UniversalCompletenessHD]

/-- Axiom checks are outside the proof-library import closure. -/
lean_lib «Audit» where
  globs := #[.submodules `Audit]

/-- Trusted challenge and thin solution wrapper for protected comparison. -/
lean_lib «ProofAudit» where
  globs := #[.submodules `ProofAudit]
