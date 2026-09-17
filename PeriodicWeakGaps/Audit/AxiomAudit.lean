import PeriodicWeakGapsHD.HigherDim.Basic
import Lean.Util.CollectAxioms

#check SpectralGapsPrelim.HigherDim.Hermite
#check SpectralGapsPrelim.HigherDim.higher_dimensional_nonuniqueness_basic
#check SpectralGapsPrelim.HigherDim.higher_dimensional_nonuniqueness

#print axioms SpectralGapsPrelim.HigherDim.Hermite
#print axioms SpectralGapsPrelim.HigherDim.higher_dimensional_nonuniqueness_basic
#print axioms SpectralGapsPrelim.HigherDim.higher_dimensional_nonuniqueness

open Lean Elab Command

private def allowedFoundationalAxioms : Array Name :=
  #[`propext, `Classical.choice, `Quot.sound]

private def auditedTargets : Array Name :=
  #[`SpectralGapsPrelim.HigherDim.Hermite,
    `SpectralGapsPrelim.HigherDim.higher_dimensional_nonuniqueness_basic,
    `SpectralGapsPrelim.HigherDim.higher_dimensional_nonuniqueness]

run_cmd do
  for target in auditedTargets do
    let used ← collectAxioms target
    let rejected := used.filter fun ax => !allowedFoundationalAxioms.contains ax
    unless rejected.isEmpty do
      throwError "{target} uses non-allowlisted axioms: {rejected}"
