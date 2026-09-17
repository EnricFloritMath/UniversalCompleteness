import PeriodicWeakGapsHD.HigherDim.Definitions

/-!
# Trusted challenge: higher-dimensional Sobolev nonuniqueness

This file contains the trusted comparison statement. Comparator compares it
with the separately built solution. The challenge imports only the definitions
module and no module from the solution proof chain.
-/

noncomputable section

open MeasureTheory

namespace ProofAudit

theorem target_higher_dimensional_nonuniqueness_basic
    {d : Nat} (hd_pos : 0 < d)
    {A Lambda : Set (SpectralGapsPrelim.HigherDim.E d)}
    {alpha : Real} {x0 : SpectralGapsPrelim.HigherDim.E d}
    (hA_meas : MeasurableSet A)
    (hA_sub : A ⊆ SpectralGapsPrelim.HigherDim.unitCube d)
    (hA_pos : 0 < volume A)
    (hA_lt_one : volume A < 1)
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_le_dim : 2 * alpha ≤ (d : Real))
    (hLambda : SpectralGapsPrelim.HigherDim.UniformlyDiscrete Lambda)
    (hx0 : x0 ∉ Lambda) :
    ∃ f : SpectralGapsPrelim.HigherDim.E d → Complex,
      SpectralGapsPrelim.HigherDim.WeightedPW alpha A f ∧
      Continuous f ∧
      f x0 = 1 ∧
      ∀ lambda ∈ Lambda, f lambda = 0 := by
  sorry

end ProofAudit
