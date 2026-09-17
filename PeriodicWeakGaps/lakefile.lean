import Lake
open Lake DSL

package "SpectralGapsPrelim" where
  version := v!"0.1.0"

require "leanprover-community" / "mathlib" @ git "v4.31.0"

@[default_target]
lean_lib «PeriodicWeakGapsHD» where
  srcDir := "Internal"
  globs := #[.submodules `PeriodicWeakGapsHD]

/-- The one-dimensional exponential-independence result imported by the higher-dimensional proof. -/
lean_lib «OneDimensional» where
  -- Keep this after the broader library so Lake resolves the shared module prefix here.
  srcDir := "Internal/OneDimensional"
  roots := #[`SpectralGapsPrelim.Theorem112]
  globs := #[.submodules `SpectralGapsPrelim.Theorem112]

/-- Axiom checks are outside the proof-library import closure. -/
lean_lib «Audit» where
  globs := #[.submodules `Audit]

/-- Trusted challenge and thin solution wrapper for protected comparison. -/
lean_lib «ProofAudit» where
  globs := #[.submodules `ProofAudit]
