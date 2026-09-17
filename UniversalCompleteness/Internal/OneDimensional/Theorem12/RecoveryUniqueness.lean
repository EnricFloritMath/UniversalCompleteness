import Theorem12.GenericAuxiliary
import Theorem12.SupportSlicing
import Theorem12.PoleCoordinates
import Theorem12.PoleDensity
import Theorem12.JensenContradiction

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Theorem12.Internal

/- Proof idea: a nonzero residue at `(j,q)` would define an inhabitant of the active subtype,
contradicting the supplied `IsEmpty` certificate. -/
theorem residueCoord_eq_zero_of_isEmpty_active {alpha : ℝ} {beta : ℚ} {S : Set ℝ}
    {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f) (x : AddCircle (1 : ℝ))
    (hEmpty : IsEmpty (ActiveIndex data x)) (j q : ℤ) :
    residueCoord data alpha beta x j q = 0 := by
  by_contra hres
  exact (@IsEmpty.false (ActiveIndex data x) hEmpty)
    (⟨(j, q), hres⟩ : ActiveIndex data x)

/- Proof idea: this choice makes `uCoordClass` equal `x`; combine residue vanishing with the
off-bad residue/support equivalence to force the slice value to vanish. -/
theorem slice_eq_zero_of_isEmpty_active {alpha : ℝ} {beta : ℚ} {S : Set ℝ}
    {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f) (x : AddCircle (1 : ℝ))
    (hxBad : x ∉ sineBad alpha beta) (hEmpty : IsEmpty (ActiveIndex data x))
    (j : ℤ) : slice data j x = 0 := by
  let q : ℤ := -floorBeta beta j
  have hu : uCoordClass alpha beta x j q = x := by
    simp [q, uCoordClass]
  by_contra hslice
  have hmem : uCoordClass alpha beta x j q ∈ sliceSupport data j := by
    simpa only [sliceSupport, Set.mem_setOf_eq, hu] using hslice
  have hres : residueCoord data alpha beta x j q ≠ 0 :=
    (residueCoord_ne_zero_iff data x hxBad j q).mpr hmem
  exact hres (residueCoord_eq_zero_of_isEmpty_active data x hEmpty j q)

/- Proof idea: on the conull pole-good set apply Jensen emptiness and then `slice_eq_zero_of_isEmpty_active` for every
integer slice index at the same fixed parameter. -/
theorem slice_all_eq_zero_ae {alpha : ℝ} {beta : ℚ} {S : Set ℝ} {f : ℝ → ℂ}
    (data : PositiveInputData alpha beta S f) (hAlpha : Irrational alpha)
    (hbeta0 : beta ≠ 0) (hbetaSmall : |(beta : ℝ)| < 1 / 2)
    (hSlt : volume S < 1) :
    ∀ᵐ x : AddCircle (1 : ℝ) ∂AddCircle.haarAddCircle,
      ∀ j : ℤ, slice data j x = 0 := by
  filter_upwards [poleGoodParameter_ae data hAlpha hbeta0 hbetaSmall hSlt] with x hx
  intro j
  exact slice_eq_zero_of_isEmpty_active data x hx.fourierGood.analytic.1
    (activeIndex_isEmpty data x hAlpha hbeta0 hSlt hx) j

/- Proof idea: turn `slice_all_eq_zero_ae` into AE-zero for each integer cell and apply the generic
integer-slice reconstruction theorem to the strongly measurable `data.g`. -/
theorem positiveRepresentative_ae_eq_zero {alpha : ℝ} {beta : ℚ} {S : Set ℝ}
    {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f) (hAlpha : Irrational alpha)
    (hbeta0 : beta ≠ 0) (hbetaSmall : |(beta : ℝ)| < 1 / 2)
    (hSlt : volume S < 1) : data.g =ᵐ[volume] (fun _ => 0) := by
  have hall := slice_all_eq_zero_ae data hAlpha hbeta0 hbetaSmall hSlt
  apply Theorem12.Generic.ae_of_ae_all_int_slices data.g data.stronglyMeasurable_g
  intro j
  exact hall.mono fun x hx => hx j

/- Proof idea: apply the recovery field of the fixed `PositiveInputData` to the whole-line
AE-zero representative obtained in `positiveRepresentative_ae_eq_zero`. -/
theorem originalInput_ae_eq_zero {alpha : ℝ} {beta : ℚ} {S : Set ℝ}
    {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f) (hAlpha : Irrational alpha)
    (hbeta0 : beta ≠ 0) (hbetaSmall : |(beta : ℝ)| < 1 / 2)
    (hSlt : volume S < 1) : f =ᵐ[volume.restrict S] (fun _ => 0) := by
  exact data.recovery
    (positiveRepresentative_ae_eq_zero data hAlpha hbeta0 hbetaSmall hSlt)

/- Proof idea: construct one `PositiveInputData` from the indexed negative Fourier samples and
apply `originalInput_ae_eq_zero` to recover the original restricted-measure function. -/
theorem l1_uniqueness_fixed (alpha : ℝ) (hAlpha : Irrational alpha) (beta : ℚ)
    (hbeta0 : beta ≠ 0) (hbetaSmall : |(beta : ℝ)| < 1 / 2) (S : Set ℝ)
    (hSmeas : MeasurableSet S) (hSlt : volume S < 1) (f : ℝ → ℂ)
    (hf : Integrable f (volume.restrict S))
    (hsample : ∀ n : ℤ, fourierSampleOn S f (frequency alpha beta n) = 0) :
    f =ᵐ[volume.restrict S] (fun _ => 0) := by
  let data := Classical.choice
    (exists_positiveInputData alpha beta S hSmeas hSlt f hf hsample)
  exact originalInput_ae_eq_zero data hAlpha hbeta0 hbetaSmall hSlt

end Theorem12.Internal

namespace Theorem12

/- Proof idea: unfold `UniversalL1Uniqueness`, convert each range-set sample hypothesis to its
indexed frequency, and invoke `l1_uniqueness_fixed` for the arbitrary admissible input. -/
theorem frequencySet_universalL1 (alpha : ℝ) (hAlpha : Irrational alpha) (beta : ℚ)
    (hbeta0 : beta ≠ 0) (hbetaSmall : |(beta : ℝ)| < 1 / 2) :
    UniversalL1Uniqueness (frequencySet alpha beta) := by
  intro S hSmeas hSlt f hf hsample
  apply Internal.l1_uniqueness_fixed alpha hAlpha beta hbeta0 hbetaSmall
    S hSmeas hSlt f hf
  intro n
  exact hsample (frequency alpha beta n) ⟨n, rfl⟩

end Theorem12
