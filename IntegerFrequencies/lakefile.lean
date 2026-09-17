import Lake

open Lake DSL

package "IntegerFrequenciesHDVerification" where
  version := v!"0.1.0"

require "leanprover-community" / "mathlib" @ git "v4.31.0"

/-- One-dimensional finite-`Lp` lemmas. -/
lean_lib «Theorem12» where
  srcDir := "Internal/OneDimensional"
  globs := #[.submodules `Theorem12]

/-- One-dimensional analytic lemmas for Fourier uniqueness. -/
lean_lib «Theorem14» where
  srcDir := "Internal/OneDimensional"
  globs := #[.submodules `Theorem14]

/-- Pointwise ergodic lemmas for torus rotations. -/
lean_lib «SpectralGapsPrelim» where
  srcDir := "Internal/OneDimensional"
  globs := #[.submodules `SpectralGapsPrelim]

@[default_target]
lean_lib «IntegerFrequenciesHD» where
  srcDir := "Internal"
  globs := #[.submodules `IntegerFrequenciesHD]

/-- Axiom checks are outside the proof-library import closure. -/
lean_lib «Audit» where
  -- Lean files live under Audit/.
  globs := #[.submodules `Audit]

/-- Trusted challenge and thin solution wrapper for protected comparison. -/
lean_lib «ProofAudit» where
  -- These modules are built explicitly, never by the default proof target.
  globs := #[.submodules `ProofAudit]
