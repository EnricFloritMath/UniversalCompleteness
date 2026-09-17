import UniversalCompletenessHD.Basic
import Lean.Util.CollectAxioms

/-!
Final axiom audit for the arbitrary-dimensional universal-completeness theorem.
This module is deliberately outside the production proof import closure.
-/

#check UniversalCompletenessHD.universal_completeness_higher_dimension
#check UniversalCompletenessHD.universal_completeness_higher_dimension_basic

#print axioms UniversalCompletenessHD.universal_completeness_higher_dimension
#print axioms UniversalCompletenessHD.universal_completeness_higher_dimension_basic

open Lean Elab Command

private def allowedFoundationalAxioms : Array Name :=
  #[`propext, `Classical.choice, `Quot.sound]

private def auditedTargets : Array Name :=
  #[`UniversalCompletenessHD.universal_completeness_higher_dimension,
    `UniversalCompletenessHD.universal_completeness_higher_dimension_basic]

run_cmd do
  for target in auditedTargets do
    let used ← collectAxioms target
    let rejected := used.filter fun ax => !allowedFoundationalAxioms.contains ax
    unless rejected.isEmpty do
      throwError "{target} uses non-allowlisted axioms: {rejected}"
