import AsymptoticallyIntegerHD
import Lean.Util.CollectAxioms

/-!
# Final axiom-closure audit

The three audited dependency closures must use only the foundational axioms
listed below.
-/

open Lean Elab Command

private def allowedFoundationalAxioms : Array Name :=
  #[`propext, `Classical.choice, `Quot.sound]

private def auditedTargets : Array Name :=
  #[`AsymptoticallyIntegerHD.theorem_1_4_higher_dimension,
    `AsymptoticallyIntegerHD.exists_small_annihilator_hd,
    `AsymptoticallyIntegerHD.not_complete_of_annihilator_hd]

run_cmd do
  for target in auditedTargets do
    let used ← collectAxioms target
    let rejected := used.filter fun ax => !allowedFoundationalAxioms.contains ax
    unless rejected.isEmpty do
      throwError "{target} uses non-allowlisted axioms: {rejected}"
