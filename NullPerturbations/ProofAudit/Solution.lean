import AsymptoticallyIntegerHD.PublicAssembly

/-! # Thin solution wrapper for protected comparison -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ProofAudit

theorem target_null_perturbations_higher_dimension
    (d : Nat) (hd : 0 < d)
    (delta : AsymptoticallyIntegerHD.IntVec d →
      AsymptoticallyIntegerHD.RealVec d)
    (hdelta : AsymptoticallyIntegerHD.TendsToZeroAtIntVecInfinity delta)
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∃ (S : Set (AsymptoticallyIntegerHD.RealVec d))
      (hSmeas : MeasurableSet S) (hSfinite : volume S ≠ ∞),
      volume S < ENNReal.ofReal epsilon ∧
        ¬ AsymptoticallyIntegerHD.ExponentialCompleteInL2HD
          (AsymptoticallyIntegerHD.frequencySet delta)
          S hSmeas hSfinite := by
  exact AsymptoticallyIntegerHD.theorem_1_4_higher_dimension
    d hd delta hdelta epsilon hepsilon

end ProofAudit
