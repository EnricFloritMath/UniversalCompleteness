import UniversalCompletenessHD.Definitions

/-! # Multitorus `L1` Fourier uniqueness adapter -/

noncomputable section

open MeasureTheory

namespace UniversalCompletenessHD.Internal

local instance fuMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance fuIsAddHaarMeasureUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance fuIsProbabilityMeasureUnitAddCircle :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/- Re-export the proved product-Fejer uniqueness theorem:
an integrable function with every native multitorus coefficient zero is zero
almost everywhere under normalized standard Haar measure. -/
theorem ae_zero_of_mFourierCoeff_zero_L1 {d : Nat}
    {F : Torus d → Complex} (hF : Integrable F volume)
    (hzero : ∀ n : IntVec d, mFourierCoeffHD F n = 0) :
    F =ᵐ[volume] (fun _ ↦ (0 : Complex)) := by
  change ∀ n : IntVec d,
    UnitAddTorus.mFourierCoeff F n = 0 at hzero
  exact IntegerFrequenciesHD.Internal.ae_zero_of_mFourierCoeff_zero_L1
    hF hzero

end UniversalCompletenessHD.Internal
