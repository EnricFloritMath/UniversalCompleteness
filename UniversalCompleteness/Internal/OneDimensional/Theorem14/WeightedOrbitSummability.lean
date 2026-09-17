import Theorem14.Window
import Theorem14.FejerApproximation
import Theorem12.GenericAuxiliary

/-! # Theorem 1.4: weighted-orbit ENNReal summability -/

noncomputable section

open Filter MeasureTheory
open scoped BigOperators ENNReal Topology

namespace Theorem14.Internal

/- Proof idea: work wholly in ENNReal and prove both factors finite before conversion. -/
private theorem lintegral_weightedOrbitENNRealMass
    {epsilon alpha : ℝ} {f : AddCircle (1 : ℝ) → ℂ}
    (hf : Integrable f AddCircle.haarAddCircle)
    (he0 : 0 < epsilon) (he1 : epsilon < 1) :
    (∫⁻ x, weightedOrbitENNRealMass epsilon alpha f x
      ∂AddCircle.haarAddCircle) =
      (∑' k : ℤ, (‖windowCoeff epsilon k‖₊ : ENNReal)) *
        ∫⁻ x, (‖f x‖₊ : ENNReal) ∂AddCircle.haarAddCircle := by
  /- Proof idea: Establish termwise a.e. measurability, apply `lintegral_tsum`, factor the fixed window norm,
  and transport each orbit norm by Haar-preserving subtraction. Prove both ENNReal factors on
  the right are below `⊤` before any a.e.-finiteness argument. -/
  have hwindow := summable_windowCoeff_and_tsum_norm epsilon he0 he1
  have hwindowFinite :
      (∑' k : ℤ, (‖windowCoeff epsilon k‖₊ : ENNReal)) < ∞ := by
    rw [lt_top_iff_ne_top]
    simpa only [enorm_eq_nnnorm] using
      (tsum_enorm_ne_top_iff_summable_norm
        (f := fun k : ℤ => windowCoeff epsilon k)).2 hwindow.1
  have hfFinite :
      (∫⁻ x, (‖f x‖₊ : ENNReal) ∂AddCircle.haarAddCircle) < ∞ := by
    have h := hf.hasFiniteIntegral
    change (∫⁻ x, ‖f x‖ₑ ∂AddCircle.haarAddCircle) < ∞ at h
    simpa only [enorm_eq_nnnorm] using h
  have hnormAe : AEMeasurable
      (fun x => (‖f x‖₊ : ENNReal)) AddCircle.haarAddCircle := by
    simpa only [enorm_eq_nnnorm] using hf.aestronglyMeasurable.enorm
  have htermAe (k : ℤ) : AEMeasurable
      (fun x => (‖weightedOrbitCoeff epsilon alpha f x k‖₊ : ENNReal))
        AddCircle.haarAddCircle := by
    let a : AddCircle (1 : ℝ) :=
      ((((k : ℤ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ))
    have hcomp := hf.aestronglyMeasurable.comp_quasiMeasurePreserving
      (Theorem12.Generic.measurePreserving_addCircle_sub a).quasiMeasurePreserving
    have he := hcomp.enorm.const_mul
      (‖windowCoeff epsilon k‖₊ : ENNReal)
    simpa only [weightedOrbitCoeff, enorm_eq_nnnorm, nnnorm_mul,
      ENNReal.coe_mul, Function.comp_apply, a] using he
  have htranslate (k : ℤ) :
      (∫⁻ x, (‖f (x - ((((k : ℤ) : ℝ) * alpha : ℝ) :
          AddCircle (1 : ℝ)))‖₊ : ENNReal) ∂AddCircle.haarAddCircle) =
        ∫⁻ x, (‖f x‖₊ : ENNReal) ∂AddCircle.haarAddCircle := by
    let a : AddCircle (1 : ℝ) :=
      ((((k : ℤ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ))
    let g : AddCircle (1 : ℝ) → AddCircle (1 : ℝ) := fun x => x - a
    have hmp := Theorem12.Generic.measurePreserving_addCircle_sub a
    have hnormMap : AEMeasurable (fun x => (‖f x‖₊ : ENNReal))
        (Measure.map g AddCircle.haarAddCircle) := by
      rw [hmp.map_eq]
      exact hnormAe
    have hmap := lintegral_map' hnormMap hmp.measurable.aemeasurable
    rw [hmp.map_eq] at hmap
    simpa only [g, a] using hmap.symm
  change (∫⁻ x, ∑' k : ℤ,
      (‖weightedOrbitCoeff epsilon alpha f x k‖₊ : ENNReal)
      ∂AddCircle.haarAddCircle) = _
  rw [lintegral_tsum htermAe]
  simp_rw [weightedOrbitCoeff, nnnorm_mul, ENNReal.coe_mul]
  have hterm (k : ℤ) :
      (∫⁻ x, (‖windowCoeff epsilon k‖₊ : ENNReal) *
          (‖f (x - ((((k : ℤ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ)))‖₊ :
            ENNReal) ∂AddCircle.haarAddCircle) =
        (‖windowCoeff epsilon k‖₊ : ENNReal) *
          ∫⁻ x, (‖f x‖₊ : ENNReal) ∂AddCircle.haarAddCircle := by
    rw [lintegral_const_mul'' _]
    · rw [htranslate]
    · have hcomp := hf.aestronglyMeasurable.comp_quasiMeasurePreserving
        (Theorem12.Generic.measurePreserving_addCircle_sub
          ((((k : ℤ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ))).quasiMeasurePreserving
      simpa only [enorm_eq_nnnorm, Function.comp_apply] using hcomp.enorm
  simp_rw [hterm]
  exact ENNReal.tsum_mul_right

/- Proof idea: obtain finite mass a.e. and only then form the real norm series. -/
private theorem ae_summable_weightedOrbitCoeff
    {epsilon alpha : ℝ} {f : AddCircle (1 : ℝ) → ℂ}
    (hf : Integrable f AddCircle.haarAddCircle)
    (he0 : 0 < epsilon) (he1 : epsilon < 1) :
    ∀ᵐ x ∂AddCircle.haarAddCircle,
      Summable (fun k : ℤ => ‖weightedOrbitCoeff epsilon alpha f x k‖) := by
  /- Proof idea: Obtain finite mass a.e. from the finite lintegral and convert each finite ENNReal sum to
  `Summable` of real norms. -/
  have hwindow := summable_windowCoeff_and_tsum_norm epsilon he0 he1
  have hwindowFinite :
      (∑' k : ℤ, (‖windowCoeff epsilon k‖₊ : ENNReal)) < ∞ := by
    rw [lt_top_iff_ne_top]
    simpa only [enorm_eq_nnnorm] using
      (tsum_enorm_ne_top_iff_summable_norm
        (f := fun k : ℤ => windowCoeff epsilon k)).2 hwindow.1
  have hfFinite :
      (∫⁻ x, (‖f x‖₊ : ENNReal) ∂AddCircle.haarAddCircle) < ∞ := by
    have h := hf.hasFiniteIntegral
    change (∫⁻ x, ‖f x‖ₑ ∂AddCircle.haarAddCircle) < ∞ at h
    simpa only [enorm_eq_nnnorm] using h
  have hmassInt :
      (∫⁻ x, weightedOrbitENNRealMass epsilon alpha f x
        ∂AddCircle.haarAddCircle) < ∞ := by
    rw [lintegral_weightedOrbitENNRealMass hf he0 he1]
    exact ENNReal.mul_lt_top hwindowFinite hfFinite
  have htermAe (k : ℤ) : AEMeasurable
      (fun x => (‖weightedOrbitCoeff epsilon alpha f x k‖₊ : ENNReal))
        AddCircle.haarAddCircle := by
    let a : AddCircle (1 : ℝ) :=
      ((((k : ℤ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ))
    have hcomp := hf.aestronglyMeasurable.comp_quasiMeasurePreserving
      (Theorem12.Generic.measurePreserving_addCircle_sub a).quasiMeasurePreserving
    have he := hcomp.enorm.const_mul
      (‖windowCoeff epsilon k‖₊ : ENNReal)
    simpa only [weightedOrbitCoeff, enorm_eq_nnnorm, nnnorm_mul,
      ENNReal.coe_mul, Function.comp_apply, a] using he
  have hmassAe : AEMeasurable
      (weightedOrbitENNRealMass epsilon alpha f) AddCircle.haarAddCircle := by
    unfold weightedOrbitENNRealMass
    exact AEMeasurable.tsum htermAe
  filter_upwards [ae_lt_top' hmassAe hmassInt.ne] with x hx
  apply (tsum_enorm_ne_top_iff_summable_norm
    (f := fun k : ℤ => weightedOrbitCoeff epsilon alpha f x k)).1
  simpa only [weightedOrbitENNRealMass, enorm_eq_nnnorm] using hx.ne

/- Proof idea: use double ENNReal Tonelli, then intersect target/stage/error events. -/
theorem weightedApproximationAt_ae
    {epsilon alpha : ℝ} {f : AddCircle (1 : ℝ) → ℂ}
    (hf : Integrable f AddCircle.haarAddCircle)
    (A : FejerApproximation f)
    (he0 : 0 < epsilon) (he1 : epsilon < 1) :
    ∀ᵐ x ∂AddCircle.haarAddCircle,
      WeightedApproximationAt epsilon alpha f A x := by
  /- Proof idea: Apply `ae_summable_weightedOrbitCoeff` to target, stages, and errors. Use `A.summable_error` and the exact window
  norm identity in an ENNReal double-Tonelli computation to show the sum over `j` of orbit `l1`
  errors is finite a.e.; only then convert each layer to real summability and intersect the
  countably many conull events. -/
  let err : ℕ → AddCircle (1 : ℝ) → ℂ := fun j y =>
    fejerMean (A.index j) f y - f y
  have hstageInt (j : ℕ) :
      Integrable (fejerMean (A.index j) f) AddCircle.haarAddCircle := by
    simpa [IntegrableOn] using
      (fejerMean (A.index j) f).continuous.continuousOn.integrableOn_compact
        (μ := AddCircle.haarAddCircle) isCompact_univ
  have herrInt (j : ℕ) : Integrable (err j) AddCircle.haarAddCircle := by
    change Integrable
      ((fejerMean (A.index j) f : AddCircle (1 : ℝ) → ℂ) - f)
        AddCircle.haarAddCircle
    exact (hstageInt j).sub hf
  have htarget := ae_summable_weightedOrbitCoeff
    (epsilon := epsilon) (alpha := alpha) hf he0 he1
  have hstage : ∀ᵐ x ∂AddCircle.haarAddCircle, ∀ j,
      Summable (fun k : ℤ =>
        ‖weightedOrbitCoeff epsilon alpha (fejerMean (A.index j) f) x k‖) := by
    rw [ae_all_iff]
    intro j
    exact ae_summable_weightedOrbitCoeff
      (epsilon := epsilon) (alpha := alpha) (hstageInt j) he0 he1
  have herror : ∀ᵐ x ∂AddCircle.haarAddCircle, ∀ j,
      Summable (fun k : ℤ =>
        ‖weightedOrbitCoeff epsilon alpha (err j) x k‖) := by
    rw [ae_all_iff]
    intro j
    exact ae_summable_weightedOrbitCoeff
      (epsilon := epsilon) (alpha := alpha) (herrInt j) he0 he1
  have hwindow := summable_windowCoeff_and_tsum_norm epsilon he0 he1
  have hwindowFinite :
      (∑' k : ℤ, (‖windowCoeff epsilon k‖₊ : ENNReal)) < ∞ := by
    rw [lt_top_iff_ne_top]
    simpa only [enorm_eq_nnnorm] using
      (tsum_enorm_ne_top_iff_summable_norm
        (f := fun k : ℤ => windowCoeff epsilon k)).2 hwindow.1
  have herrorIntegral (j : ℕ) :
      (∫⁻ y, (‖err j y‖₊ : ENNReal) ∂AddCircle.haarAddCircle) =
        ENNReal.ofReal
          (∫ y, ‖fejerMean (A.index j) f y - f y‖
            ∂AddCircle.haarAddCircle) := by
    have h := ofReal_integral_eq_lintegral_ofReal (herrInt j).norm
      (Eventually.of_forall fun y => norm_nonneg (err j y))
    symm
    simpa only [err, ofReal_norm, enorm_eq_nnnorm] using h
  have herrorIntegralSum :
      (∑' j : ℕ, ∫⁻ y, (‖err j y‖₊ : ENNReal)
        ∂AddCircle.haarAddCircle) < ∞ := by
    have h := A.summable_error.tsum_ofReal_lt_top
    simpa only [herrorIntegral] using h
  have hmassAe (j : ℕ) : AEMeasurable
      (weightedOrbitENNRealMass epsilon alpha (err j))
        AddCircle.haarAddCircle := by
    unfold weightedOrbitENNRealMass
    apply AEMeasurable.tsum
    intro k
    let a : AddCircle (1 : ℝ) :=
      ((((k : ℤ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ))
    have hcomp := (herrInt j).aestronglyMeasurable.comp_quasiMeasurePreserving
      (Theorem12.Generic.measurePreserving_addCircle_sub a).quasiMeasurePreserving
    have he := hcomp.enorm.const_mul
      (‖windowCoeff epsilon k‖₊ : ENNReal)
    simpa only [weightedOrbitCoeff, enorm_eq_nnnorm, nnnorm_mul,
      ENNReal.coe_mul, Function.comp_apply, a] using he
  have hdoubleInt :
      (∫⁻ x, ∑' j : ℕ,
          weightedOrbitENNRealMass epsilon alpha (err j) x
        ∂AddCircle.haarAddCircle) =
      (∑' k : ℤ, (‖windowCoeff epsilon k‖₊ : ENNReal)) *
        ∑' j : ℕ, ∫⁻ y, (‖err j y‖₊ : ENNReal)
          ∂AddCircle.haarAddCircle := by
    rw [lintegral_tsum hmassAe]
    simp_rw [lintegral_weightedOrbitENNRealMass
      (epsilon := epsilon) (alpha := alpha) (herrInt _) he0 he1]
    exact ENNReal.tsum_mul_left
  have hdoubleIntFinite :
      (∫⁻ x, ∑' j : ℕ,
          weightedOrbitENNRealMass epsilon alpha (err j) x
        ∂AddCircle.haarAddCircle) < ∞ := by
    rw [hdoubleInt]
    exact ENNReal.mul_lt_top hwindowFinite herrorIntegralSum
  have hdoubleAe : AEMeasurable
      (fun x => ∑' j : ℕ,
        weightedOrbitENNRealMass epsilon alpha (err j) x)
        AddCircle.haarAddCircle :=
    AEMeasurable.tsum hmassAe
  have hdouble : ∀ᵐ x ∂AddCircle.haarAddCircle,
      (∑' j : ℕ, weightedOrbitENNRealMass epsilon alpha (err j) x) < ∞ :=
    ae_lt_top' hdoubleAe hdoubleIntFinite.ne
  filter_upwards [htarget, hstage, herror, hdouble]
    with x hxTarget hxStage hxError hxDouble
  refine ⟨hxTarget, hxStage, ?_, ?_⟩
  · simpa only [err] using hxError
  · let q : ℕ → ℤ → ℂ := fun j k =>
      weightedOrbitCoeff epsilon alpha (err j) x k
    let inner : ℕ → NNReal := fun j => ∑' k : ℤ, ‖q j k‖₊
    have hinnerSummable (j : ℕ) : Summable (fun k : ℤ => ‖q j k‖₊) := by
      apply NNReal.summable_coe.mp
      simpa only [coe_nnnorm, q] using hxError j
    have houterENN : (∑' j : ℕ, (inner j : ENNReal)) ≠ ∞ := by
      have hxDouble' := hxDouble.ne
      change (∑' j : ℕ, ∑' k : ℤ, (‖q j k‖₊ : ENNReal)) ≠ ∞ at hxDouble'
      have hfun : (fun j : ℕ => (inner j : ENNReal)) =
          fun j : ℕ => ∑' k : ℤ, (‖q j k‖₊ : ENNReal) := by
        funext j
        exact ENNReal.coe_tsum (hinnerSummable j)
      rw [hfun]
      exact hxDouble'
    have houterNN : Summable inner :=
      ENNReal.tsum_coe_ne_top_iff_summable.mp houterENN
    have houterReal : Summable (fun j => (inner j : ℝ)) :=
      NNReal.summable_coe.mpr houterNN
    convert houterReal using 1
    funext j
    dsimp [inner, q]
    rw [NNReal.coe_tsum]
    simp only [coe_nnnorm, err]

end Theorem14.Internal
