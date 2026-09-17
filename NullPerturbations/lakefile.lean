import Lake

open Lake DSL

package "AsymptoticallyIntegerHDVerification" where
  version := v!"0.1.0"

require "leanprover-community" / "mathlib" @ git "v4.31.0"

@[default_target]
lean_lib «AsymptoticallyIntegerHD» where
  srcDir := "Internal"
  globs := #[.andSubmodules `AsymptoticallyIntegerHD]

/-- Axiom checks are outside the proof-library import closure. -/
lean_lib «Audit» where
  globs := #[.one `Audit.NoSorry, .one `Audit.ProjectAxioms,
    .one `Audit.PrintAxioms]

/-- Check that the finished theorems use only the permitted foundational axioms. -/
lean_lib «FinalAudit» where
  globs := #[.one `Audit.FinalAxiomAllowlist]

/-- Optional protected theorem comparison, outside the default proof build. -/
lean_lib «ProofAudit» where
  globs := #[.submodules `ProofAudit]
