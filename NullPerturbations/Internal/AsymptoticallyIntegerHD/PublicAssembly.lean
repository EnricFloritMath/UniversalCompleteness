import AsymptoticallyIntegerHD.Definitions
import AsymptoticallyIntegerHD.Completeness
import AsymptoticallyIntegerHD.InfiniteAssembly
import AsymptoticallyIntegerHD.NonCompleteness

/-!
# Library theorem for Section 6, item (2)

This module defines the library theorem used by
`NullPerturbations/showcase.lean`. Its type retains the finite-measure
witness and adds no injectivity, separation, rate, nonvanishing, or
boundedness assumption.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace AsymptoticallyIntegerHD

/- Proof idea: construct `W` with `exists_small_annihilator_hd`, return its exact
carrier and finite-measure witness, and apply
`not_complete_of_annihilator_hd`. -/
theorem theorem_1_4_higher_dimension
    (d : Nat) (hd : 0 < d)
    (delta : IntVec d → RealVec d)
    (hdelta : TendsToZeroAtIntVecInfinity delta)
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∃ (S : Set (RealVec d))
      (hSmeas : MeasurableSet S) (hSfinite : volume S ≠ ∞),
      volume S < ENNReal.ofReal epsilon ∧
        ¬ ExponentialCompleteInL2HD
          (frequencySet delta) S hSmeas hSfinite := by
  let W : SmallAnnihilatorHD delta epsilon :=
    exists_small_annihilator_hd d hd delta hdelta epsilon hepsilon
  exact ⟨W.S, W.S_measurable, W.measure_ne_top, W.measure_lt,
    not_complete_of_annihilator_hd W⟩

end AsymptoticallyIntegerHD
