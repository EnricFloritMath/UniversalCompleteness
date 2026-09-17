import IntegerFrequenciesHD.ProductFejerApproximation
import IntegerFrequenciesHD.TorusRotationErgodic
import Theorem14.Window

/-!
# Weighted-orbit summability

This module proves weighted-orbit summability by adapting the
one-dimensional Tonelli argument to the product torus.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology

local instance weightedOrbitMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance weightedOrbitIsAddHaarMeasureUnitAddCircle : Measure.IsAddHaarMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance weightedOrbitIsProbabilityMeasureUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace IntegerFrequenciesHD.Internal

/- Establish termwise a.e. measurability, use nonnegative
Tonelli, factor the fixed window coefficient norm, and transport each orbit
norm by the measure-preserving torus subtraction.  Stay in ENNReal until both
factors are known finite. -/
theorem lintegral_weightedOrbitENNRealMassHD {d : Nat}
    {epsilon : Real} {alpha : RealVec d} {F : Torus d → Complex}
    (hF : Integrable F volume) (he0 : 0 < epsilon) (he1 : epsilon < 1) :
    (∫⁻ x, weightedOrbitENNRealMassHD epsilon alpha F x) =
      (∑' k : Int, (‖Theorem14.Internal.windowCoeff epsilon k‖₊ : ENNReal)) *
        ∫⁻ x, (‖F x‖₊ : ENNReal) := by
  have hwindow := Theorem14.Internal.summable_windowCoeff_and_tsum_norm
    epsilon he0 he1
  have hwindowFinite :
      (∑' k : Int,
        (‖Theorem14.Internal.windowCoeff epsilon k‖₊ : ENNReal)) < ∞ := by
    rw [lt_top_iff_ne_top]
    simpa only [enorm_eq_nnnorm] using
      (tsum_enorm_ne_top_iff_summable_norm
        (f := fun k : Int => Theorem14.Internal.windowCoeff epsilon k)).2 hwindow.1
  have hFFinite : (∫⁻ x, (‖F x‖₊ : ENNReal) ∂volume) < ∞ := by
    have h := hF.hasFiniteIntegral
    change (∫⁻ x, ‖F x‖ₑ ∂volume) < ∞ at h
    simpa only [enorm_eq_nnnorm] using h
  have hnormAe : AEMeasurable (fun x => (‖F x‖₊ : ENNReal)) volume := by
    simpa only [enorm_eq_nnnorm] using hF.aestronglyMeasurable.enorm
  have htermAe (k : Int) : AEMeasurable
      (fun x => (‖weightedOrbitCoeffHD epsilon alpha F x k‖₊ : ENNReal))
        volume := by
    let a : Torus d := k • alphaTorus alpha
    have hcomp := hF.aestronglyMeasurable.comp_quasiMeasurePreserving
      (measurePreserving_torus_sub a).quasiMeasurePreserving
    have he := hcomp.enorm.const_mul
      (‖Theorem14.Internal.windowCoeff epsilon k‖₊ : ENNReal)
    simpa only [weightedOrbitCoeffHD, enorm_eq_nnnorm, nnnorm_mul,
      ENNReal.coe_mul, Function.comp_apply, a] using he
  have htranslate (k : Int) :
      (∫⁻ x, (‖F (x - k • alphaTorus alpha)‖₊ : ENNReal) ∂volume) =
        ∫⁻ x, (‖F x‖₊ : ENNReal) ∂volume := by
    let a : Torus d := k • alphaTorus alpha
    let g : Torus d → Torus d := fun x => x - a
    have hmp := measurePreserving_torus_sub a
    have hnormMap : AEMeasurable (fun x => (‖F x‖₊ : ENNReal))
        (Measure.map g volume) := by
      rw [hmp.map_eq]
      exact hnormAe
    have hmap := lintegral_map' hnormMap hmp.measurable.aemeasurable
    rw [hmp.map_eq] at hmap
    simpa only [g, a] using hmap.symm
  change (∫⁻ x, ∑' k : Int,
      (‖weightedOrbitCoeffHD epsilon alpha F x k‖₊ : ENNReal) ∂volume) = _
  rw [lintegral_tsum htermAe]
  simp_rw [weightedOrbitCoeffHD, nnnorm_mul, ENNReal.coe_mul]
  have hterm (k : Int) :
      (∫⁻ x, (‖Theorem14.Internal.windowCoeff epsilon k‖₊ : ENNReal) *
          (‖F (x - k • alphaTorus alpha)‖₊ : ENNReal) ∂volume) =
        (‖Theorem14.Internal.windowCoeff epsilon k‖₊ : ENNReal) *
          ∫⁻ x, (‖F x‖₊ : ENNReal) ∂volume := by
    rw [lintegral_const_mul'' _]
    · rw [htranslate]
    · have hcomp := hF.aestronglyMeasurable.comp_quasiMeasurePreserving
        (measurePreserving_torus_sub
          (k • alphaTorus alpha)).quasiMeasurePreserving
      simpa only [enorm_eq_nnnorm, Function.comp_apply] using hcomp.enorm
  simp_rw [hterm]
  exact ENNReal.tsum_mul_right

/- The exact mass identity has finite lintegral; therefore the
ENNReal coefficient mass is finite almost everywhere.  Only then convert its
series to summability of the real norm series. -/
theorem ae_summable_weightedOrbitCoeffHD {d : Nat}
    {epsilon : Real} {alpha : RealVec d} {F : Torus d → Complex}
    (hF : Integrable F volume) (he0 : 0 < epsilon) (he1 : epsilon < 1) :
    ∀ᵐ x ∂volume, Summable (fun k : Int =>
      ‖weightedOrbitCoeffHD epsilon alpha F x k‖) := by
  have hwindow := Theorem14.Internal.summable_windowCoeff_and_tsum_norm
    epsilon he0 he1
  have hwindowFinite :
      (∑' k : Int,
        (‖Theorem14.Internal.windowCoeff epsilon k‖₊ : ENNReal)) < ∞ := by
    rw [lt_top_iff_ne_top]
    simpa only [enorm_eq_nnnorm] using
      (tsum_enorm_ne_top_iff_summable_norm
        (f := fun k : Int => Theorem14.Internal.windowCoeff epsilon k)).2 hwindow.1
  have hFFinite : (∫⁻ x, (‖F x‖₊ : ENNReal) ∂volume) < ∞ := by
    have h := hF.hasFiniteIntegral
    change (∫⁻ x, ‖F x‖ₑ ∂volume) < ∞ at h
    simpa only [enorm_eq_nnnorm] using h
  have hmassInt :
      (∫⁻ x, weightedOrbitENNRealMassHD epsilon alpha F x ∂volume) < ∞ := by
    rw [lintegral_weightedOrbitENNRealMassHD hF he0 he1]
    exact ENNReal.mul_lt_top hwindowFinite hFFinite
  have htermAe (k : Int) : AEMeasurable
      (fun x => (‖weightedOrbitCoeffHD epsilon alpha F x k‖₊ : ENNReal))
        volume := by
    let a : Torus d := k • alphaTorus alpha
    have hcomp := hF.aestronglyMeasurable.comp_quasiMeasurePreserving
      (measurePreserving_torus_sub a).quasiMeasurePreserving
    have he := hcomp.enorm.const_mul
      (‖Theorem14.Internal.windowCoeff epsilon k‖₊ : ENNReal)
    simpa only [weightedOrbitCoeffHD, enorm_eq_nnnorm, nnnorm_mul,
      ENNReal.coe_mul, Function.comp_apply, a] using he
  have hmassAe : AEMeasurable
      (weightedOrbitENNRealMassHD epsilon alpha F) volume := by
    unfold weightedOrbitENNRealMassHD
    exact AEMeasurable.tsum htermAe
  filter_upwards [ae_lt_top' hmassAe hmassInt.ne] with x hx
  apply (tsum_enorm_ne_top_iff_summable_norm
    (f := fun k : Int => weightedOrbitCoeffHD epsilon alpha F x k)).1
  simpa only [weightedOrbitENNRealMassHD, enorm_eq_nnnorm] using hx.ne

/- Each literal product-Fejer stage is continuous and
integrable, so every literal stage error is integrable by `hF`.  Apply the
exact ENNReal mass identity to all stage errors, sum first nonnegatively over
the stage index, use `A.summable_error`, and convert finiteness only at the
end. -/
theorem ae_summable_weightedApproximationErrorsHD {d : Nat}
    {epsilon : Real} {alpha : RealVec d} {F : Torus d → Complex}
    (hF : Integrable F volume) (A : ProductFejerApproximation F)
    (he0 : 0 < epsilon) (he1 : epsilon < 1) :
    ∀ᵐ x ∂volume, Summable (fun j => ∑' k : Int,
      ‖weightedOrbitCoeffHD epsilon alpha
        (fun y => productFejerMean (A.index j) F y - F y) x k‖) := by
  let err : Nat → Torus d → Complex := fun j y =>
    productFejerMean (A.index j) F y - F y
  have hstageInt (j : Nat) :
      Integrable (productFejerMean (A.index j) F) volume := by
    simpa [IntegrableOn] using
      (productFejerMean (A.index j) F).continuous.continuousOn.integrableOn_compact
        (μ := volume) isCompact_univ
  have herrInt (j : Nat) : Integrable (err j) volume := by
    change Integrable
      ((productFejerMean (A.index j) F : Torus d → Complex) - F) volume
    exact (hstageInt j).sub hF
  have herror : ∀ᵐ x ∂volume, ∀ j,
      Summable (fun k : Int =>
        ‖weightedOrbitCoeffHD epsilon alpha (err j) x k‖) := by
    rw [ae_all_iff]
    intro j
    exact ae_summable_weightedOrbitCoeffHD
      (epsilon := epsilon) (alpha := alpha) (herrInt j) he0 he1
  have hwindow := Theorem14.Internal.summable_windowCoeff_and_tsum_norm
    epsilon he0 he1
  have hwindowFinite :
      (∑' k : Int,
        (‖Theorem14.Internal.windowCoeff epsilon k‖₊ : ENNReal)) < ∞ := by
    rw [lt_top_iff_ne_top]
    simpa only [enorm_eq_nnnorm] using
      (tsum_enorm_ne_top_iff_summable_norm
        (f := fun k : Int => Theorem14.Internal.windowCoeff epsilon k)).2 hwindow.1
  have herrorIntegral (j : Nat) :
      (∫⁻ y, (‖err j y‖₊ : ENNReal) ∂volume) =
        ENNReal.ofReal
          (∫ y, ‖productFejerMean (A.index j) F y - F y‖ ∂volume) := by
    have h := ofReal_integral_eq_lintegral_ofReal (herrInt j).norm
      (Eventually.of_forall fun y => norm_nonneg (err j y))
    symm
    simpa only [err, ofReal_norm, enorm_eq_nnnorm] using h
  have herrorIntegralSum :
      (∑' j : Nat, ∫⁻ y, (‖err j y‖₊ : ENNReal) ∂volume) < ∞ := by
    have h := A.summable_error.tsum_ofReal_lt_top
    simpa only [herrorIntegral] using h
  have hmassAe (j : Nat) : AEMeasurable
      (weightedOrbitENNRealMassHD epsilon alpha (err j)) volume := by
    unfold weightedOrbitENNRealMassHD
    apply AEMeasurable.tsum
    intro k
    let a : Torus d := k • alphaTorus alpha
    have hcomp := (herrInt j).aestronglyMeasurable.comp_quasiMeasurePreserving
      (measurePreserving_torus_sub a).quasiMeasurePreserving
    have he := hcomp.enorm.const_mul
      (‖Theorem14.Internal.windowCoeff epsilon k‖₊ : ENNReal)
    simpa only [weightedOrbitCoeffHD, enorm_eq_nnnorm, nnnorm_mul,
      ENNReal.coe_mul, Function.comp_apply, a] using he
  have hdoubleInt :
      (∫⁻ x, ∑' j : Nat,
          weightedOrbitENNRealMassHD epsilon alpha (err j) x ∂volume) =
        (∑' k : Int,
          (‖Theorem14.Internal.windowCoeff epsilon k‖₊ : ENNReal)) *
          ∑' j : Nat, ∫⁻ y, (‖err j y‖₊ : ENNReal) ∂volume := by
    rw [lintegral_tsum hmassAe]
    simp_rw [lintegral_weightedOrbitENNRealMassHD
      (epsilon := epsilon) (alpha := alpha) (herrInt _) he0 he1]
    exact ENNReal.tsum_mul_left
  have hdoubleIntFinite :
      (∫⁻ x, ∑' j : Nat,
          weightedOrbitENNRealMassHD epsilon alpha (err j) x ∂volume) < ∞ := by
    rw [hdoubleInt]
    exact ENNReal.mul_lt_top hwindowFinite herrorIntegralSum
  have hdoubleAe : AEMeasurable
      (fun x => ∑' j : Nat,
        weightedOrbitENNRealMassHD epsilon alpha (err j) x) volume :=
    AEMeasurable.tsum hmassAe
  have hdouble : ∀ᵐ x ∂volume,
      (∑' j : Nat,
        weightedOrbitENNRealMassHD epsilon alpha (err j) x) < ∞ :=
    ae_lt_top' hdoubleAe hdoubleIntFinite.ne
  filter_upwards [herror, hdouble] with x hxError hxDouble
  let q : Nat → Int → Complex := fun j k =>
    weightedOrbitCoeffHD epsilon alpha (err j) x k
  let inner : Nat → NNReal := fun j => ∑' k : Int, ‖q j k‖₊
  have hinnerSummable (j : Nat) : Summable (fun k : Int => ‖q j k‖₊) := by
    apply NNReal.summable_coe.mp
    simpa only [coe_nnnorm, q] using hxError j
  have houterENN : (∑' j : Nat, (inner j : ENNReal)) ≠ ∞ := by
    have hxDouble' := hxDouble.ne
    change (∑' j : Nat, ∑' k : Int, (‖q j k‖₊ : ENNReal)) ≠ ∞ at hxDouble'
    have hfun : (fun j : Nat => (inner j : ENNReal)) =
        fun j : Nat => ∑' k : Int, (‖q j k‖₊ : ENNReal) := by
      funext j
      exact ENNReal.coe_tsum (hinnerSummable j)
    rw [hfun]
    exact hxDouble'
  have houterNN : Summable inner :=
    ENNReal.tsum_coe_ne_top_iff_summable.mp houterENN
  have houterReal : Summable (fun j => (inner j : Real)) :=
    NNReal.summable_coe.mpr houterNN
  convert houterReal using 1
  funext j
  dsimp [inner, q]
  rw [NNReal.coe_tsum]
  simp only [coe_nnnorm, err]

/- Intersect the conull target, all-stage, all-stage-error, and
summable-error events.  Construct one `WeightedApproximationAtHD` containing
every invariant required later by broadening. -/
theorem weightedApproximationAtHD_ae {d : Nat}
    {epsilon : Real} {alpha : RealVec d} {F : Torus d → Complex}
    (hF : Integrable F volume) (A : ProductFejerApproximation F)
    (he0 : 0 < epsilon) (he1 : epsilon < 1) :
    ∀ᵐ x ∂volume, WeightedApproximationAtHD epsilon alpha F A x := by
  let err : Nat → Torus d → Complex := fun j y =>
    productFejerMean (A.index j) F y - F y
  have hstageInt (j : Nat) :
      Integrable (productFejerMean (A.index j) F) volume := by
    simpa [IntegrableOn] using
      (productFejerMean (A.index j) F).continuous.continuousOn.integrableOn_compact
        (μ := volume) isCompact_univ
  have herrInt (j : Nat) : Integrable (err j) volume := by
    change Integrable
      ((productFejerMean (A.index j) F : Torus d → Complex) - F) volume
    exact (hstageInt j).sub hF
  have htarget := ae_summable_weightedOrbitCoeffHD
    (epsilon := epsilon) (alpha := alpha) hF he0 he1
  have hstage : ∀ᵐ x ∂volume, ∀ j,
      Summable (fun k : Int =>
        ‖weightedOrbitCoeffHD epsilon alpha
          (productFejerMean (A.index j) F) x k‖) := by
    rw [ae_all_iff]
    intro j
    exact ae_summable_weightedOrbitCoeffHD
      (epsilon := epsilon) (alpha := alpha) (hstageInt j) he0 he1
  have herror : ∀ᵐ x ∂volume, ∀ j,
      Summable (fun k : Int =>
        ‖weightedOrbitCoeffHD epsilon alpha (err j) x k‖) := by
    rw [ae_all_iff]
    intro j
    exact ae_summable_weightedOrbitCoeffHD
      (epsilon := epsilon) (alpha := alpha) (herrInt j) he0 he1
  have hsum := ae_summable_weightedApproximationErrorsHD
    (epsilon := epsilon) (alpha := alpha) hF A he0 he1
  filter_upwards [htarget, hstage, herror, hsum]
    with x hxTarget hxStage hxError hxSum
  refine ⟨hxTarget, hxStage, ?_, hxSum⟩
  simpa only [err] using hxError

end IntegerFrequenciesHD.Internal
