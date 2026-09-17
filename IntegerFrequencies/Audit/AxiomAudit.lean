import IntegerFrequenciesHD.Basic
import Lean.Util.CollectAxioms

/-!
Final axiom audit for the arbitrary-dimensional integer-frequency theorem.
This module is deliberately outside the proof-library import closure.
-/

#check IntegerFrequenciesHD.integer_frequencies_higher_dimension
#check IntegerFrequenciesHD.integer_frequencies_higher_dimension_density
#check IntegerFrequenciesHD.integer_frequencies_higher_dimension_l1
#check IntegerFrequenciesHD.integer_frequencies_higher_dimension_completeLp
#check IntegerFrequenciesHD.integer_frequencies_higher_dimension_basic

#print axioms IntegerFrequenciesHD.integer_frequencies_higher_dimension
#print axioms IntegerFrequenciesHD.integer_frequencies_higher_dimension_density
#print axioms IntegerFrequenciesHD.integer_frequencies_higher_dimension_l1
#print axioms IntegerFrequenciesHD.integer_frequencies_higher_dimension_completeLp
#print axioms IntegerFrequenciesHD.integer_frequencies_higher_dimension_basic

open Lean Elab Command

private def allowedFoundationalAxioms : Array Name :=
  #[`propext, `Classical.choice, `Quot.sound]

private def auditedTargets : Array Name :=
  #[`IntegerFrequenciesHD.integer_frequencies_higher_dimension,
    `IntegerFrequenciesHD.integer_frequencies_higher_dimension_density,
    `IntegerFrequenciesHD.integer_frequencies_higher_dimension_l1,
    `IntegerFrequenciesHD.integer_frequencies_higher_dimension_completeLp,
    `IntegerFrequenciesHD.integer_frequencies_higher_dimension_basic]

run_cmd do
  for target in auditedTargets do
    let used ← collectAxioms target
    let rejected := used.filter fun ax => !allowedFoundationalAxioms.contains ax
    unless rejected.isEmpty do
      throwError "{target} uses non-allowlisted axioms: {rejected}"
