import Theorem12.FourierUniqueness
import Theorem12.SupportSlicing
import Theorem12.PoleCoordinates
import Theorem12.Summability
import Theorem12.SincIdentity
import Theorem12.MeromorphicSeries

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace Theorem12.Internal

/- Proof idea: transparently set the exceptional branch to zero and otherwise retain the
literal parity, slice, sine, and reciprocal-difference factors in their order. -/
def intEvalSummand {alpha : ℝ} {beta : ℚ} {S : Set ℝ} {f : ℝ → ℂ}
    (data : PositiveInputData alpha beta S f) (k : ℤ) (x : AddCircle (1 : ℝ))
    (a : ℤ × ℤ) : ℂ := open Classical in
  if x ∈ sineBad alpha beta then 0
  else
    intParity (floorBeta beta a.1) *
      slice data a.1 (uCoordClass alpha beta x a.1 a.2) *
      ((Real.sin (Real.pi * tCoord alpha beta x a.1 a.2) : ℝ) : ℂ) /
      (Real.pi : ℂ) *
      (((tCoord alpha beta x a.1 a.2 - (a.2 : ℝ) + (k : ℝ) : ℝ) : ℂ)⁻¹ -
        ((tCoord alpha beta x a.1 a.2 - (a.2 : ℝ) : ℝ) : ℂ)⁻¹)

/- Proof idea: transparently take the complex `tsum` over the fixed type `ℤ × ℤ`,
never over the parameter-dependent active subtype. -/
def intEvaluator {alpha : ℝ} {beta : ℚ} {S : Set ℝ} {f : ℝ → ℂ}
    (data : PositiveInputData alpha beta S f) (k : ℤ)
    (x : AddCircle (1 : ℝ)) : ℂ :=
  ∑' a : ℤ × ℤ, intEvalSummand data k x a

/- Proof idea: prove the bad branch measurable and close the good coordinate expression
under AE-measurable arithmetic and piecewise selection, retaining the fixed index type. -/
theorem aemeasurable_intEvalSummand {alpha : ℝ} {beta : ℚ}
    {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f)
    (k : ℤ) (a : ℤ × ℤ) :
    AEMeasurable (fun x : AddCircle (1 : ℝ) => intEvalSummand data k x a)
      AddCircle.haarAddCircle := by
  classical
  have hunit : Measurable Theorem12.Generic.unitRep := by
    apply measurable_of_continuousOn_compl_singleton (0 : AddCircle (1 : ℝ))
    intro y hy
    exact (continuousAt_subtype_val.comp
      (AddCircle.continuousAt_equivIco (1 : ℝ) 0 hy)).continuousWithinAt
  have huClass (j q : ℤ) : Measurable (fun x : AddCircle (1 : ℝ) =>
      uCoordClass alpha beta x j q) := by
    unfold uCoordClass
    fun_prop
  have ht (j q : ℤ) : Measurable (fun x : AddCircle (1 : ℝ) =>
      tCoord alpha beta x j q) := by
    unfold tCoord uCoord
    exact (measurable_const.mul
      ((hunit.comp (huClass j q)).add measurable_const)).sub measurable_const
  have hbad : MeasurableSet (sineBad alpha beta) := by
    rw [sineBad]
    simp only [Set.setOf_exists]
    exact MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun q =>
      MeasurableSet.iUnion fun ell => measurableSet_eq_fun (ht j q) measurable_const
  have hslice : Measurable (fun x : AddCircle (1 : ℝ) =>
      slice data a.1 (uCoordClass alpha beta x a.1 a.2)) := by
    unfold slice
    exact data.stronglyMeasurable_g.measurable.comp
      (measurable_const.add (hunit.comp (huClass a.1 a.2)))
  apply Measurable.aemeasurable
  unfold intEvalSummand
  apply Measurable.ite hbad measurable_const
  have hsin : Measurable (fun x : AddCircle (1 : ℝ) =>
      ((Real.sin (Real.pi * tCoord alpha beta x a.1 a.2) : ℝ) : ℂ)) :=
    (((measurable_const.mul (ht a.1 a.2)).sin).complex_ofReal)
  have hleft : Measurable (fun x : AddCircle (1 : ℝ) =>
      (((tCoord alpha beta x a.1 a.2 - (a.2 : ℝ) + (k : ℝ) : ℝ) : ℂ)⁻¹ -
        ((tCoord alpha beta x a.1 a.2 - (a.2 : ℝ) : ℝ) : ℂ)⁻¹)) := by
    fun_prop
  fun_prop

/- Proof idea: apply the uniform shifted-sinc bound, translate the slice norm by Haar
invariance, and sum the product of the quadratic series with the slice-norm series. -/
theorem summable_integral_norm_intEvalSummand {alpha : ℝ} {beta : ℚ}
    {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f)
    (hbetaSmall : |(beta : ℝ)| < 1 / 2) (k : ℤ) :
    Summable (fun a : ℤ × ℤ =>
      ∫ x : AddCircle (1 : ℝ), ‖intEvalSummand data k x a‖ ∂AddCircle.haarAddCircle) := by
  classical
  obtain ⟨Ck, hCk, hbound⟩ := Theorem12.Generic.norm_sincShiftCoeff_le k
  have hq : Summable (fun q : ℤ => Ck / (1 + (q : ℝ) ^ 2)) := by
    simpa only [div_eq_mul_inv] using
      Theorem12.Generic.summable_one_add_int_sq_inv.mul_left Ck
  have hq_nonneg (q : ℤ) : 0 ≤ Ck / (1 + (q : ℝ) ^ 2) := by positivity
  have hj : Summable (fun j : ℤ =>
      ∫ u : AddCircle (1 : ℝ), ‖slice data j u‖ ∂AddCircle.haarAddCircle) :=
    (hasSum_integral_norm_slice data).summable
  have hj_nonneg (j : ℤ) :
      0 ≤ ∫ u : AddCircle (1 : ℝ), ‖slice data j u‖ ∂AddCircle.haarAddCircle :=
    integral_nonneg fun _ => norm_nonneg _
  refine Summable.of_nonneg_of_le
    (fun _ => integral_nonneg fun _ => norm_nonneg _) ?_
    (hj.mul_of_nonneg hq hj_nonneg hq_nonneg)
  rintro ⟨j, q⟩
  let shift : AddCircle (1 : ℝ) :=
    (((((floorBeta beta j + q : ℤ) : ℝ) * alpha : ℝ)) : AddCircle (1 : ℝ))
  have hsliceInt : Integrable (fun x : AddCircle (1 : ℝ) =>
      ‖slice data j (uCoordClass alpha beta x j q)‖) AddCircle.haarAddCircle := by
    change Integrable (fun x : AddCircle (1 : ℝ) => ‖slice data j (x - shift)‖)
      AddCircle.haarAddCircle
    simpa only [Function.comp_def] using
      (Theorem12.Generic.measurePreserving_addCircle_sub shift).integrable_comp_of_integrable
        (integrable_slice data j).norm
  have hpoint (x : AddCircle (1 : ℝ)) :
      ‖intEvalSummand data k x (j, q)‖ ≤
        (Ck / (1 + (q : ℝ) ^ 2)) *
          ‖slice data j (uCoordClass alpha beta x j q)‖ := by
    by_cases hx : x ∈ sineBad alpha beta
    · simp only [intEvalSummand, hx, if_pos, norm_zero]
      positivity
    · have htInt : ∀ ell : ℤ, tCoord alpha beta x j q ≠ (ell : ℝ) := by
        intro ell ht
        apply poleCoord_not_int_of_not_sineBad alpha beta x hx j q (q - ell)
        rw [poleCoord_eq_q_sub_tCoord, ht]
        push_cast
        ring
      have hsinc := hbound (tCoord alpha beta x j q)
        (abs_tCoord_lt_three_halves alpha beta hbetaSmall x j q) htInt q
      have heq :
          intEvalSummand data k x (j, q) =
            intParity (floorBeta beta j) *
              slice data j (uCoordClass alpha beta x j q) *
                Theorem12.Generic.sincShiftCoeff k (tCoord alpha beta x j q) q := by
        simp only [intEvalSummand, hx, if_false, Theorem12.Generic.sincShiftCoeff]
        ring
      rw [heq, norm_mul, norm_mul]
      have hparity : ‖intParity (floorBeta beta j)‖ = 1 := by
        simp [intParity]
      rw [hparity, one_mul]
      simpa only [mul_comm] using
        mul_le_mul_of_nonneg_left hsinc
          (norm_nonneg (slice data j (uCoordClass alpha beta x j q)))
  have hupper : Integrable (fun x : AddCircle (1 : ℝ) =>
      (Ck / (1 + (q : ℝ) ^ 2)) *
        ‖slice data j (uCoordClass alpha beta x j q)‖) AddCircle.haarAddCircle :=
    hsliceInt.const_mul _
  calc
    (∫ x : AddCircle (1 : ℝ), ‖intEvalSummand data k x (j, q)‖
        ∂AddCircle.haarAddCircle) ≤
        ∫ x : AddCircle (1 : ℝ),
          (Ck / (1 + (q : ℝ) ^ 2)) *
            ‖slice data j (uCoordClass alpha beta x j q)‖
          ∂AddCircle.haarAddCircle :=
      integral_mono_of_nonneg (ae_of_all _ fun x => norm_nonneg _)
        hupper (ae_of_all _ hpoint)
    _ = (∫ u : AddCircle (1 : ℝ), ‖slice data j u‖ ∂AddCircle.haarAddCircle) *
        (Ck / (1 + (q : ℝ) ^ 2)) := by
      rw [integral_const_mul]
      change (Ck / (1 + (q : ℝ) ^ 2)) *
          (∫ x : AddCircle (1 : ℝ), ‖slice data j (x - shift)‖
            ∂AddCircle.haarAddCircle) = _
      rw [Theorem12.Generic.integral_addCircle_sub
        (fun u : AddCircle (1 : ℝ) => ‖slice data j u‖)
        (integrable_slice data j).norm shift]
      ring

/- Proof idea: apply Bochner integral/tsum convergence to the AE-measurable fixed-index
summands and the summable integral-norm family from `summable_integral_norm_intEvalSummand`. -/
theorem integrable_intEvaluator {alpha : ℝ} {beta : ℚ} {S : Set ℝ} {f : ℝ → ℂ}
    (data : PositiveInputData alpha beta S f) (hbetaSmall : |(beta : ℝ)| < 1 / 2)
    (k : ℤ) : Integrable (intEvaluator data k) AddCircle.haarAddCircle := by
  classical
  obtain ⟨Ck, hCk, hbound⟩ := Theorem12.Generic.norm_sincShiftCoeff_le k
  have htermInt (a : ℤ × ℤ) :
      Integrable (fun x : AddCircle (1 : ℝ) => intEvalSummand data k x a)
        AddCircle.haarAddCircle := by
    let shift : AddCircle (1 : ℝ) :=
      (((((floorBeta beta a.1 + a.2 : ℤ) : ℝ) * alpha : ℝ)) : AddCircle (1 : ℝ))
    have hsliceInt : Integrable (fun x : AddCircle (1 : ℝ) =>
        ‖slice data a.1 (uCoordClass alpha beta x a.1 a.2)‖)
        AddCircle.haarAddCircle := by
      change Integrable (fun x : AddCircle (1 : ℝ) => ‖slice data a.1 (x - shift)‖)
        AddCircle.haarAddCircle
      simpa only [Function.comp_def] using
        (Theorem12.Generic.measurePreserving_addCircle_sub shift).integrable_comp_of_integrable
          (integrable_slice data a.1).norm
    have hpoint (x : AddCircle (1 : ℝ)) :
        ‖intEvalSummand data k x a‖ ≤
          (Ck / (1 + (a.2 : ℝ) ^ 2)) *
            ‖slice data a.1 (uCoordClass alpha beta x a.1 a.2)‖ := by
      by_cases hx : x ∈ sineBad alpha beta
      · simp only [intEvalSummand, hx, if_pos, norm_zero]
        positivity
      · have htInt : ∀ ell : ℤ,
            tCoord alpha beta x a.1 a.2 ≠ (ell : ℝ) := by
          intro ell ht
          apply poleCoord_not_int_of_not_sineBad alpha beta x hx a.1 a.2 (a.2 - ell)
          rw [poleCoord_eq_q_sub_tCoord, ht]
          push_cast
          ring
        have hsinc := hbound (tCoord alpha beta x a.1 a.2)
          (abs_tCoord_lt_three_halves alpha beta hbetaSmall x a.1 a.2) htInt a.2
        have heq :
            intEvalSummand data k x a =
              intParity (floorBeta beta a.1) *
                slice data a.1 (uCoordClass alpha beta x a.1 a.2) *
                  Theorem12.Generic.sincShiftCoeff k
                    (tCoord alpha beta x a.1 a.2) a.2 := by
          rcases a with ⟨j, q⟩
          simp only [intEvalSummand, hx, if_false, Theorem12.Generic.sincShiftCoeff]
          ring
        rw [heq, norm_mul, norm_mul]
        have hparity : ‖intParity (floorBeta beta a.1)‖ = 1 := by
          simp [intParity]
        rw [hparity, one_mul]
        simpa only [mul_comm] using
          mul_le_mul_of_nonneg_left hsinc
            (norm_nonneg (slice data a.1 (uCoordClass alpha beta x a.1 a.2)))
    have hupper : Integrable (fun x : AddCircle (1 : ℝ) =>
        (Ck / (1 + (a.2 : ℝ) ^ 2)) *
          ‖slice data a.1 (uCoordClass alpha beta x a.1 a.2)‖)
        AddCircle.haarAddCircle := hsliceInt.const_mul _
    exact hupper.mono'
      (aemeasurable_intEvalSummand data k a).aestronglyMeasurable
      (ae_of_all _ hpoint)
  have hsum := summable_integral_norm_intEvalSummand data hbetaSmall k
  have hmeas (a : ℤ × ℤ) :
      AEMeasurable (fun x : AddCircle (1 : ℝ) => intEvalSummand data k x a)
        AddCircle.haarAddCircle :=
    aemeasurable_intEvalSummand data k a
  have hlin_ne :
      (∑' a : ℤ × ℤ, ∫⁻ x : AddCircle (1 : ℝ),
        ‖intEvalSummand data k x a‖ₑ ∂AddCircle.haarAddCircle) ≠ ∞ := by
    have hlin (a : ℤ × ℤ) :
        (∫⁻ x : AddCircle (1 : ℝ), ‖intEvalSummand data k x a‖ₑ
          ∂AddCircle.haarAddCircle) =
          ENNReal.ofReal
            (∫ x : AddCircle (1 : ℝ), ‖intEvalSummand data k x a‖
              ∂AddCircle.haarAddCircle) := by
      exact (ofReal_integral_norm_eq_lintegral_enorm (htermInt a)).symm
    rw [funext hlin]
    exact hsum.tsum_ofReal_ne_top
  refine ⟨(AEMeasurable.tsum hmeas).aestronglyMeasurable, ?_⟩
  change (∫⁻ x : AddCircle (1 : ℝ),
    ‖∑' a : ℤ × ℤ, intEvalSummand data k x a‖ₑ
      ∂AddCircle.haarAddCircle) < ∞
  calc
    (∫⁻ x : AddCircle (1 : ℝ),
      ‖∑' a : ℤ × ℤ, intEvalSummand data k x a‖ₑ
        ∂AddCircle.haarAddCircle) ≤
        ∫⁻ x : AddCircle (1 : ℝ),
          ∑' a : ℤ × ℤ, ‖intEvalSummand data k x a‖ₑ
          ∂AddCircle.haarAddCircle :=
      lintegral_mono fun x => enorm_tsum_le_tsum_enorm
    _ = ∑' a : ℤ × ℤ, ∫⁻ x : AddCircle (1 : ℝ),
          ‖intEvalSummand data k x a‖ₑ ∂AddCircle.haarAddCircle := by
      rw [lintegral_tsum fun a => (hmeas a).enorm]
    _ < ∞ := lt_top_iff_ne_top.mpr hlin_ne

/- Proof idea: use unit norm of the integer character to preserve `summable_integral_norm_intEvalSummand`'s
integral-norm summability, then apply Bochner integral/tsum interchange. -/
theorem integral_intEvaluator_mul_character {alpha : ℝ} {beta : ℚ}
    {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f)
    (hbetaSmall : |(beta : ℝ)| < 1 / 2) (k n : ℤ) :
    (∫ x : AddCircle (1 : ℝ), intEvaluator data k x * fourier n x
      ∂AddCircle.haarAddCircle) =
      ∑' a : ℤ × ℤ, ∫ x : AddCircle (1 : ℝ),
        intEvalSummand data k x a * fourier n x ∂AddCircle.haarAddCircle := by
  classical
  obtain ⟨Ck, hCk, hbound⟩ := Theorem12.Generic.norm_sincShiftCoeff_le k
  have htermInt (a : ℤ × ℤ) :
      Integrable (fun x : AddCircle (1 : ℝ) => intEvalSummand data k x a)
        AddCircle.haarAddCircle := by
    let shift : AddCircle (1 : ℝ) :=
      (((((floorBeta beta a.1 + a.2 : ℤ) : ℝ) * alpha : ℝ)) : AddCircle (1 : ℝ))
    have hsliceInt : Integrable (fun x : AddCircle (1 : ℝ) =>
        ‖slice data a.1 (uCoordClass alpha beta x a.1 a.2)‖)
        AddCircle.haarAddCircle := by
      change Integrable (fun x : AddCircle (1 : ℝ) => ‖slice data a.1 (x - shift)‖)
        AddCircle.haarAddCircle
      simpa only [Function.comp_def] using
        (Theorem12.Generic.measurePreserving_addCircle_sub shift).integrable_comp_of_integrable
          (integrable_slice data a.1).norm
    have hpoint (x : AddCircle (1 : ℝ)) :
        ‖intEvalSummand data k x a‖ ≤
          (Ck / (1 + (a.2 : ℝ) ^ 2)) *
            ‖slice data a.1 (uCoordClass alpha beta x a.1 a.2)‖ := by
      by_cases hx : x ∈ sineBad alpha beta
      · simp only [intEvalSummand, hx, if_pos, norm_zero]
        positivity
      · have htInt : ∀ ell : ℤ,
            tCoord alpha beta x a.1 a.2 ≠ (ell : ℝ) := by
          intro ell ht
          apply poleCoord_not_int_of_not_sineBad alpha beta x hx a.1 a.2 (a.2 - ell)
          rw [poleCoord_eq_q_sub_tCoord, ht]
          push_cast
          ring
        have hsinc := hbound (tCoord alpha beta x a.1 a.2)
          (abs_tCoord_lt_three_halves alpha beta hbetaSmall x a.1 a.2) htInt a.2
        have heq :
            intEvalSummand data k x a =
              intParity (floorBeta beta a.1) *
                slice data a.1 (uCoordClass alpha beta x a.1 a.2) *
                  Theorem12.Generic.sincShiftCoeff k
                    (tCoord alpha beta x a.1 a.2) a.2 := by
          rcases a with ⟨j, q⟩
          simp only [intEvalSummand, hx, if_false, Theorem12.Generic.sincShiftCoeff]
          ring
        rw [heq, norm_mul, norm_mul]
        have hparity : ‖intParity (floorBeta beta a.1)‖ = 1 := by
          simp [intParity]
        rw [hparity, one_mul]
        simpa only [mul_comm] using
          mul_le_mul_of_nonneg_left hsinc
            (norm_nonneg (slice data a.1 (uCoordClass alpha beta x a.1 a.2)))
    have hupper : Integrable (fun x : AddCircle (1 : ℝ) =>
        (Ck / (1 + (a.2 : ℝ) ^ 2)) *
          ‖slice data a.1 (uCoordClass alpha beta x a.1 a.2)‖)
        AddCircle.haarAddCircle := hsliceInt.const_mul _
    exact hupper.mono'
      (aemeasurable_intEvalSummand data k a).aestronglyMeasurable
      (ae_of_all _ hpoint)
  have hproductInt (a : ℤ × ℤ) : Integrable (fun x : AddCircle (1 : ℝ) =>
      intEvalSummand data k x a * fourier n x) AddCircle.haarAddCircle := by
    apply (htermInt a).mul_bdd
    · exact (map_continuous (fourier n)).aestronglyMeasurable
    · filter_upwards
      intro x
      rw [fourier_apply, Circle.norm_coe]
  have hproductSum : Summable (fun a : ℤ × ℤ =>
      ∫ x : AddCircle (1 : ℝ),
        ‖intEvalSummand data k x a * fourier n x‖ ∂AddCircle.haarAddCircle) := by
    simpa only [norm_mul, fourier_apply, Circle.norm_coe, mul_one] using
      summable_integral_norm_intEvalSummand data hbetaSmall k
  have hinterchange := integral_tsum_of_summable_integral_norm hproductInt hproductSum
  change (∫ x : AddCircle (1 : ℝ),
      (∑' a : ℤ × ℤ, intEvalSummand data k x a) * fourier n x
      ∂AddCircle.haarAddCircle) = _
  simp_rw [← tsum_mul_right]
  exact hinterchange.symm

/- Proof idea: derive nonzero denominators from off-badness, dominate the integer kernel
by the summable residue-weight family away from finitely many poles, and handle the exceptions. -/
theorem summable_intEvalSummand_of_analyticParameter {alpha : ℝ} {beta : ℚ}
    {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f)
    (x : AddCircle (1 : ℝ)) (hx : AnalyticParameter data x) (k : ℤ) :
    Summable (fun a : ℤ × ℤ => intEvalSummand data k x a) := by
  classical
  let R : ℝ := 2 * (|(k : ℝ)| + 1)
  let A : Set (ℤ × ℤ) := {a | residueCoord data alpha beta x a.1 a.2 ≠ 0 ∧
    poleCoord alpha beta x a.1 a.2 ∈ Set.Icc (-R) R}
  let F : ℤ × ℤ → ℂ := fun a => intEvalSummand data k x a
  let C : ℝ := 4 * (|(k : ℝ)| + 1)
  have hR : 0 ≤ R := by
    dsimp [R]
    positivity
  have hA : A.Finite := by
    simpa only [A] using finite_activePair_pole_Icc data x hx.2 R hR
  have hin : Summable (A.indicator F) :=
    summable_subtype_iff_indicator.mp (hA.summable F)
  have hresidue : Summable (fun a : ℤ × ℤ =>
      ‖residueCoord data alpha beta x a.1 a.2‖ /
        (1 + (poleCoord alpha beta x a.1 a.2) ^ 2)) :=
    (summable_residue_and_indicator_weight data x hx.2).1
  have hmajor : Summable (fun a : ℤ × ℤ =>
      C * (‖residueCoord data alpha beta x a.1 a.2‖ /
        (1 + (poleCoord alpha beta x a.1 a.2) ^ 2))) :=
    Summable.mul_left C hresidue
  have heval (a : ℤ × ℤ) :
      F a = residueCoord data alpha beta x a.1 a.2 *
        regularizedKernel (poleCoord alpha beta x a.1 a.2) (k : ℂ) := by
    rcases a with ⟨j, q⟩
    have hp0 : poleCoord alpha beta x j q ≠ (0 : ℝ) :=
      by simpa using poleCoord_not_int_of_not_sineBad alpha beta x hx.1 j q 0
    have hpk : poleCoord alpha beta x j q ≠ (k : ℝ) :=
      poleCoord_not_int_of_not_sineBad alpha beta x hx.1 j q k
    have htq : tCoord alpha beta x j q - (q : ℝ) ≠ 0 := by
      intro h
      apply hp0
      rw [poleCoord_eq_q_sub_tCoord]
      linarith
    have htqk : tCoord alpha beta x j q - (q : ℝ) + (k : ℝ) ≠ 0 := by
      intro h
      apply hpk
      rw [poleCoord_eq_q_sub_tCoord]
      linarith
    have hkernel :
        (((tCoord alpha beta x j q - (q : ℝ) + (k : ℝ) : ℝ) : ℂ)⁻¹ -
            ((tCoord alpha beta x j q - (q : ℝ) : ℝ) : ℂ)⁻¹) =
          (k : ℂ) /
            (((((q : ℝ) - tCoord alpha beta x j q : ℝ) : ℂ)) *
              ((k : ℂ) - (((q : ℝ) - tCoord alpha beta x j q : ℝ) : ℂ))) := by
      have h1 : (((tCoord alpha beta x j q - (q : ℝ) : ℝ) : ℂ)) ≠ 0 := by
        exact_mod_cast htq
      have h2 :
          (((tCoord alpha beta x j q - (q : ℝ) + (k : ℝ) : ℝ) : ℂ)) ≠ 0 := by
        exact_mod_cast htqk
      have h3 : ((((q : ℝ) - tCoord alpha beta x j q : ℝ) : ℂ)) ≠ 0 := by
        have h3r : (q : ℝ) - tCoord alpha beta x j q ≠ 0 := by
          intro h
          apply htq
          linarith
        exact_mod_cast h3r
      have h4 :
          ((k : ℂ) - (((q : ℝ) - tCoord alpha beta x j q : ℝ) : ℂ)) ≠ 0 := by
        have h4r : (k : ℝ) - ((q : ℝ) - tCoord alpha beta x j q) ≠ 0 := by
          intro h
          apply htqk
          linarith
        exact_mod_cast h4r
      field_simp [h1, h2, h3, h4]
      push_cast
      ring
    dsimp only [F]
    rw [intEvalSummand, if_neg hx.1, residueCoord, regularizedKernel,
      poleCoord_eq_q_sub_tCoord]
    rw [hkernel]
    ring
  have hkernel_bound (p : ℝ) (hp : R < |p|) :
      ‖regularizedKernel p (k : ℂ)‖ ≤ C / (1 + p ^ 2) := by
    have hk0 : 0 ≤ |(k : ℝ)| := abs_nonneg _
    have hp' : 2 * (|(k : ℝ)| + 1) < |p| := by simpa only [R] using hp
    have hp0 : 0 < |p| := by nlinarith
    have hp1 : 1 < |p| := by nlinarith
    have hhalf : |p| / 2 < |p| - |(k : ℝ)| := by nlinarith
    have hdiff : |p| - |(k : ℝ)| ≤ |(k : ℝ) - p| := by
      simpa [abs_sub_comm] using (abs_sub_abs_le_abs_sub p (k : ℝ))
    have hdiff0 : 0 < |(k : ℝ) - p| :=
      lt_trans (by positivity : 0 < |p| / 2) (hhalf.trans_le hdiff)
    have hsq : 1 < p ^ 2 := by
      rw [sq, ← abs_mul_abs_self p]
      nlinarith
    have hnorm :
        ‖regularizedKernel p (k : ℂ)‖ =
          |(k : ℝ)| / (|p| * |(k : ℝ) - p|) := by
      unfold regularizedKernel
      rw [norm_div, norm_mul]
      have hcast : ((k : ℂ) - (p : ℂ)) = (((k : ℝ) - p : ℝ) : ℂ) := by
        push_cast
        rfl
      rw [hcast]
      simp only [Complex.norm_real, Complex.norm_intCast, Real.norm_eq_abs]
    rw [hnorm]
    apply (div_le_div_iff₀ (mul_pos hp0 hdiff0)
      (by positivity : 0 < 1 + p ^ 2)).2
    have hp_sq_abs : |p| ^ 2 = p ^ 2 := sq_abs p
    dsimp [C]
    calc
      |(k : ℝ)| * (1 + p ^ 2) ≤ 2 * |(k : ℝ)| * p ^ 2 := by nlinarith
      _ ≤ 4 * (|(k : ℝ)| + 1) * (|p| * |(k : ℝ) - p|) := by
        have hprod : |p| ^ 2 / 2 < |p| * |(k : ℝ) - p| := by
          nlinarith [mul_lt_mul_of_pos_left (hhalf.trans_le hdiff) hp0]
        rw [← hp_sq_abs]
        nlinarith
  have houtNorm : Summable (fun a : ℤ × ℤ => ‖Aᶜ.indicator F a‖) := by
    refine Summable.of_nonneg_of_le (fun a => norm_nonneg _) (fun a => ?_) hmajor
    by_cases haComp : a ∈ Aᶜ
    · rw [Set.indicator_of_mem haComp, heval, norm_mul]
      by_cases haResidue : residueCoord data alpha beta x a.1 a.2 = 0
      · simp [haResidue]
      · have haOutside :
            poleCoord alpha beta x a.1 a.2 ∉ Set.Icc (-R) R := by
          intro haIcc
          exact haComp ⟨haResidue, haIcc⟩
        have hpabs : R < |poleCoord alpha beta x a.1 a.2| := by
          by_contra hnot
          have habs : |poleCoord alpha beta x a.1 a.2| ≤ R := le_of_not_gt hnot
          exact haOutside (abs_le.mp habs)
        have hkb := hkernel_bound (poleCoord alpha beta x a.1 a.2) hpabs
        have hres0 : 0 ≤ ‖residueCoord data alpha beta x a.1 a.2‖ := norm_nonneg _
        calc
          ‖residueCoord data alpha beta x a.1 a.2‖ *
              ‖regularizedKernel (poleCoord alpha beta x a.1 a.2) (k : ℂ)‖
              ≤ ‖residueCoord data alpha beta x a.1 a.2‖ *
                (C / (1 + (poleCoord alpha beta x a.1 a.2) ^ 2)) :=
            mul_le_mul_of_nonneg_left hkb hres0
          _ = C * (‖residueCoord data alpha beta x a.1 a.2‖ /
                (1 + (poleCoord alpha beta x a.1 a.2) ^ 2)) := by ring
    · rw [Set.indicator_of_notMem haComp, norm_zero]
      positivity
  have hout : Summable (Aᶜ.indicator F) := houtNorm.of_norm
  change Summable F
  rw [← Set.indicator_self_add_compl A F]
  exact hin.add hout

/- Proof idea: delete the good-parameter branch, rewrite `p=q-t`, prove all denominators
nonzero, and normalize the reciprocal difference to the regularized kernel at `(k : ℂ)`. -/
theorem intEvalSummand_eq_activeTerm_int {alpha : ℝ} {beta : ℚ}
    {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f)
    (x : AddCircle (1 : ℝ)) (hx : AnalyticParameter data x) (j q k : ℤ) :
    intEvalSummand data k x (j, q) =
      residueCoord data alpha beta x j q *
        regularizedKernel (poleCoord alpha beta x j q) (k : ℂ) := by
  have hp0 : poleCoord alpha beta x j q ≠ (0 : ℝ) :=
    by simpa using poleCoord_not_int_of_not_sineBad alpha beta x hx.1 j q 0
  have hpk : poleCoord alpha beta x j q ≠ (k : ℝ) :=
    poleCoord_not_int_of_not_sineBad alpha beta x hx.1 j q k
  have htq : tCoord alpha beta x j q - (q : ℝ) ≠ 0 := by
    intro h
    apply hp0
    rw [poleCoord_eq_q_sub_tCoord]
    linarith
  have htqk : tCoord alpha beta x j q - (q : ℝ) + (k : ℝ) ≠ 0 := by
    intro h
    apply hpk
    rw [poleCoord_eq_q_sub_tCoord]
    linarith
  have hkernel :
      (((tCoord alpha beta x j q - (q : ℝ) + (k : ℝ) : ℝ) : ℂ)⁻¹ -
          ((tCoord alpha beta x j q - (q : ℝ) : ℝ) : ℂ)⁻¹) =
        (k : ℂ) /
          (((((q : ℝ) - tCoord alpha beta x j q : ℝ) : ℂ)) *
            ((k : ℂ) - (((q : ℝ) - tCoord alpha beta x j q : ℝ) : ℂ))) := by
    have h1 : (((tCoord alpha beta x j q - (q : ℝ) : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast htq
    have h2 : (((tCoord alpha beta x j q - (q : ℝ) + (k : ℝ) : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast htqk
    have h3 : ((((q : ℝ) - tCoord alpha beta x j q : ℝ) : ℂ)) ≠ 0 := by
      have h3r : (q : ℝ) - tCoord alpha beta x j q ≠ 0 := by
        intro h
        apply htq
        linarith
      exact_mod_cast h3r
    have h4 :
        ((k : ℂ) - (((q : ℝ) - tCoord alpha beta x j q : ℝ) : ℂ)) ≠ 0 := by
      have h4r : (k : ℝ) - ((q : ℝ) - tCoord alpha beta x j q) ≠ 0 := by
        intro h
        apply htqk
        linarith
      exact_mod_cast h4r
    field_simp [h1, h2, h3, h4]
    push_cast
    ring
  rw [intEvalSummand, if_neg hx.1, residueCoord, regularizedKernel,
    poleCoord_eq_q_sub_tCoord]
  rw [hkernel]
  ring

/- Proof idea: rewrite every full-index term by `intEvalSummand_eq_activeTerm_int`, delete zero-residue terms
with a summable subtype-tsum identity, and unfold the sole analytic series `activeM`. -/
theorem intEvaluator_eq_activeM_int {alpha : ℝ} {beta : ℚ}
    {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f)
    (x : AddCircle (1 : ℝ)) (hx : AnalyticParameter data x) (k : ℤ) :
    intEvaluator data k x = activeM data x (k : ℂ) := by
  classical
  change (∑' a : ℤ × ℤ, intEvalSummand data k x a) =
    ∑' a : ActiveIndex data x, activeTerm data x a (k : ℂ)
  calc
    (∑' a : ℤ × ℤ, intEvalSummand data k x a) =
        ∑' a : ℤ × ℤ,
          residueCoord data alpha beta x a.1 a.2 *
            regularizedKernel (poleCoord alpha beta x a.1 a.2) (k : ℂ) := by
      apply tsum_congr
      intro a
      exact intEvalSummand_eq_activeTerm_int data x hx a.1 a.2 k
    _ = ∑' a : ActiveIndex data x, activeTerm data x a (k : ℂ) := by
      change (∑' a : ℤ × ℤ,
          residueCoord data alpha beta x a.1 a.2 *
            regularizedKernel (poleCoord alpha beta x a.1 a.2) (k : ℂ)) =
        ∑' a : {a : ℤ × ℤ // residueCoord data alpha beta x a.1 a.2 ≠ 0},
          residueCoord data alpha beta x a.1.1 a.1.2 *
            regularizedKernel (poleCoord alpha beta x a.1.1 a.1.2) (k : ℂ)
      symm
      calc
        (∑' a : {a : ℤ × ℤ // residueCoord data alpha beta x a.1 a.2 ≠ 0},
            residueCoord data alpha beta x a.1.1 a.1.2 *
              regularizedKernel (poleCoord alpha beta x a.1.1 a.1.2) (k : ℂ)) =
            ∑' a : ℤ × ℤ,
              {a : ℤ × ℤ | residueCoord data alpha beta x a.1 a.2 ≠ 0}.indicator
                (fun b : ℤ × ℤ => residueCoord data alpha beta x b.1 b.2 *
                  regularizedKernel (poleCoord alpha beta x b.1 b.2) (k : ℂ)) a :=
          tsum_subtype
            {a : ℤ × ℤ | residueCoord data alpha beta x a.1 a.2 ≠ 0}
            (fun a : ℤ × ℤ => residueCoord data alpha beta x a.1 a.2 *
              regularizedKernel (poleCoord alpha beta x a.1 a.2) (k : ℂ))
        _ = ∑' a : ℤ × ℤ,
            residueCoord data alpha beta x a.1 a.2 *
              regularizedKernel (poleCoord alpha beta x a.1 a.2) (k : ℂ) := by
          apply tsum_congr
          intro a
          by_cases ha : residueCoord data alpha beta x a.1 a.2 ≠ 0
          · have hamem : a ∈
                {b : ℤ × ℤ | residueCoord data alpha beta x b.1 b.2 ≠ 0} := ha
            simp only [Set.indicator_of_mem hamem]
          · have hanmem : a ∉
                {b : ℤ × ℤ | residueCoord data alpha beta x b.1 b.2 ≠ 0} := ha
            have hz : residueCoord data alpha beta x a.1 a.2 = 0 := not_ne_iff.mp ha
            simp only [Set.indicator_of_notMem hanmem, hz, zero_mul]

/- Proof idea: rewrite the coordinate class by `uCoordClass_translate` and apply congruence to `slice`. -/
theorem slice_uCoord_translate {alpha : ℝ} {beta : ℚ} {S : Set ℝ} {f : ℝ → ℂ}
    (data : PositiveInputData alpha beta S f) (u : AddCircle (1 : ℝ)) (j q : ℤ) :
    let a : ℤ := floorBeta beta j + q
    slice data j
      (uCoordClass alpha beta
        (u + ((((a : ℤ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ))) j q) =
      slice data j u := by
  simp only
  rw [uCoordClass_translate]

/- Proof idea: apply the AddCircle character homomorphism, evaluate the real multiple,
and retain the positive factor indexed by `a=floorBeta beta j+q` at `{n*alpha}`. -/
theorem addCircle_character_translate (alpha : ℝ) (beta : ℚ)
    (u : AddCircle (1 : ℝ)) (j q n : ℤ) :
    let a : ℤ := floorBeta beta j + q
    fourier n (u + ((((a : ℤ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ))) =
      fourier n u *
        fourier a ((((n : ℤ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ)) := by
  simp only
  calc
    fourier n
        (u + ((((floorBeta beta j + q : ℤ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ))) =
        fourier n u *
          fourier n
            (((((floorBeta beta j + q : ℤ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ))) := by
      simp only [fourier_apply, zsmul_add, AddCircle.toCircle_add, Circle.coe_mul]
    _ = fourier n u *
        fourier (floorBeta beta j + q)
          ((((n : ℤ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ)) := by
      congr 1
      simp only [fourier_coe_apply]
      congr 1
      push_cast
      ring

/- Proof idea: transparently retain the literal `beta*(unitRep u+j)-floor(beta*j)` formula,
which is independent of `q` after translation. -/
private def translatedTRow (beta : ℚ) (j : ℤ) (u : AddCircle (1 : ℝ)) : ℝ :=
  (beta : ℝ) * (Theorem12.Generic.unitRep u + (j : ℝ)) - (floorBeta beta j : ℝ)

/- Proof idea: transparently coerce the real product `n*alpha` to `AddCircle 1`; the
canonical-representative theorem later identifies its representative with the fractional part. -/
private def rotationPoint (alpha : ℝ) (n : ℤ) : AddCircle (1 : ℝ) :=
  ((((n : ℤ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ))

/- Proof idea: transparently apply the identical positive AddCircle shift in both the fixed-index
evaluator summand and the native positive `n` character. -/
private def translatedRowSummand {alpha : ℝ} {beta : ℚ}
    {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f)
    (j k n q : ℤ) (u : AddCircle (1 : ℝ)) : ℂ :=
  let shift : AddCircle (1 : ℝ) :=
    (((((floorBeta beta j + q : ℤ) : ℝ) * alpha : ℝ)) : AddCircle (1 : ℝ))
  intEvalSummand data k (u + shift) (j, q) * fourier n (u + shift)

/- Proof idea: transparently place the integer `q` quantifier inside the proposition so later
AE selection chooses one `u` before every `q`. -/
private def rowGood (alpha : ℝ) (beta : ℚ) (j : ℤ)
    (u : AddCircle (1 : ℝ)) : Prop :=
  ∀ q : ℤ,
    u + (((((floorBeta beta j + q : ℤ) : ℝ) * alpha : ℝ)) : AddCircle (1 : ℝ)) ∉
      sineBad alpha beta

end Theorem12.Internal

namespace Theorem12.ScaffoldAxioms

open Theorem12.Internal

/-
This is exactly the simultaneous conull-row assertion; the same-file private
wrapper is its sole consumer.
-/
theorem four_026_rowGood_ae (alpha : ℝ) (beta : ℚ) (hbeta0 : beta ≠ 0) (j : ℤ) :
    ∀ᵐ u : AddCircle (1 : ℝ) ∂AddCircle.haarAddCircle,
      rowGood alpha beta j u ∧
        ∀ ell : ℤ, translatedTRow beta j u ≠ (ell : ℝ) := by
  have hall : ∀ᵐ u : AddCircle (1 : ℝ) ∂AddCircle.haarAddCircle,
      ∀ q : ℤ,
        u + (((((floorBeta beta j + q : ℤ) : ℝ) * alpha : ℝ)) : AddCircle (1 : ℝ)) ∉
          sineBad alpha beta := by
    apply ae_all_iff.mpr
    intro q
    let mp := Theorem12.Generic.measurePreserving_addCircle_add
      (((((floorBeta beta j + q : ℤ) : ℝ) * alpha : ℝ)) : AddCircle (1 : ℝ))
    have hpre : AddCircle.haarAddCircle
        ((fun u : AddCircle (1 : ℝ) =>
          u + (((((floorBeta beta j + q : ℤ) : ℝ) * alpha : ℝ)) : AddCircle (1 : ℝ))) ⁻¹'
            sineBad alpha beta) = 0 := by
      rw [mp.measure_preimage
        (NullMeasurableSet.of_null (sineBad_null alpha beta hbeta0)),
        sineBad_null alpha beta hbeta0]
    exact measure_eq_zero_iff_ae_notMem.mp hpre
  filter_upwards [hall] with u hu
  refine ⟨hu, ?_⟩
  intro ell ht
  apply hu 0
  refine ⟨j, 0, ell, ?_⟩
  rw [tCoord_translate]
  exact ht

end Theorem12.ScaffoldAxioms

namespace Theorem12.Internal

/- Proof idea: transport nullity of `sineBad` through each integer translation, intersect the
countable complements, and derive nonintegrality of the single translated row coordinate. -/
private theorem rowGood_ae (alpha : ℝ) (beta : ℚ) (hbeta0 : beta ≠ 0) (j : ℤ) :
    ∀ᵐ u : AddCircle (1 : ℝ) ∂AddCircle.haarAddCircle,
      rowGood alpha beta j u ∧
        ∀ ell : ℤ, translatedTRow beta j u ≠ (ell : ℝ) :=
  Theorem12.ScaffoldAxioms.four_026_rowGood_ae alpha beta hbeta0 j

/- Proof idea: transparently multiply parity, translated slice, shifted-sinc coefficient,
the positive `n` character in `u`, and the positive `floorBeta+q` phase in exact order. -/
private def rowSincSummand {alpha : ℝ} {beta : ℚ}
    {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f)
    (j k n q : ℤ) (u : AddCircle (1 : ℝ)) : ℂ :=
  intParity (floorBeta beta j) * slice data j u *
    Theorem12.Generic.sincShiftCoeff k (translatedTRow beta j u) q *
    fourier n u * fourier (floorBeta beta j + q) (rotationPoint alpha n)

/- Proof idea: transparently retain the character-difference, parity, slice, positive `n` and
`m_j` characters, and centered phase in the exact source factor order. -/
private def collapsedRowIntegrand {alpha : ℝ} {beta : ℚ}
    {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f)
    (j k n : ℤ) (u : AddCircle (1 : ℝ)) : ℂ :=
  (fourier k (rotationPoint alpha n) - 1) * intParity (floorBeta beta j) *
    slice data j u * fourier n u *
    fourier (floorBeta beta j) (rotationPoint alpha n) *
    Theorem12.Generic.centeredExp (translatedTRow beta j u) (rotationPoint alpha n)

end Theorem12.Internal

namespace Theorem12.ScaffoldAxioms

open Theorem12.Internal

/-
The helper retains the literal `∀ᵐ u, ∀ q` order and is consumed only by the private wrapper.
-/
theorem four_029_translatedRowSummand_eq_ae {alpha : ℝ} {beta : ℚ}
    {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f)
    (hbeta0 : beta ≠ 0) (j k n : ℤ) :
    ∀ᵐ u : AddCircle (1 : ℝ) ∂AddCircle.haarAddCircle, ∀ q : ℤ,
      translatedRowSummand data j k n q u = rowSincSummand data j k n q u := by
  filter_upwards [four_026_rowGood_ae alpha beta hbeta0 j] with u hu
  intro q
  have hgood := hu.1 q
  unfold translatedRowSummand rowSincSummand
  dsimp only
  rw [intEvalSummand, if_neg hgood, slice_uCoord_translate, tCoord_translate,
    addCircle_character_translate]
  unfold Theorem12.Generic.sincShiftCoeff translatedTRow rotationPoint
  ring

/-
The helper is the exact pointwise row `HasSum`, with its fixed `u` and `rowGood` witness.
-/
theorem four_030_hasSum_rowSincSummand {alpha : ℝ} {beta : ℚ}
    {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f)
    (hbetaSmall : |(beta : ℝ)| < 1 / 2) (j k n : ℤ)
    (u : AddCircle (1 : ℝ)) (hu : rowGood alpha beta j u) :
    HasSum (fun q : ℤ => rowSincSummand data j k n q u)
      (collapsedRowIntegrand data j k n u) := by
  let t := translatedTRow beta j u
  let y := rotationPoint alpha n
  have ht : |t| < 3 / 2 := by
    have h := abs_tCoord_lt_three_halves alpha beta hbetaSmall
      (u + (((((floorBeta beta j + 0 : ℤ) : ℝ) * alpha : ℝ)) : AddCircle (1 : ℝ))) j 0
    rw [tCoord_translate] at h
    exact h
  have htInt : ∀ ell : ℤ, t ≠ (ell : ℝ) := by
    intro ell hell
    apply hu 0
    refine ⟨j, 0, ell, ?_⟩
    rw [tCoord_translate]
    exact hell
  have hfourier (r : ℤ) : fourier r y =
      Complex.exp
        (((2 * Real.pi : ℝ) : ℂ) * Complex.I * (r : ℂ) *
          (Theorem12.Generic.unitRep y : ℂ)) := by
    calc
      fourier r y = fourier r
          ((Theorem12.Generic.unitRep y : ℝ) : AddCircle (1 : ℝ)) := by
        rw [Theorem12.Generic.coe_unitRep]
      _ = _ := by
        rw [fourier_coe_apply]
        push_cast
        congr 1
        ring
  obtain ⟨Ck, hCk, hbound⟩ := Theorem12.Generic.norm_sincShiftCoeff_le k
  have hnorm : Summable (fun q : ℤ =>
      ‖Theorem12.Generic.sincShiftCoeff k t q‖) := by
    refine Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => hbound t ht htInt q) ?_
    simpa only [div_eq_mul_inv] using
      Theorem12.Generic.summable_one_add_int_sq_inv.mul_left Ck
  have hbaseSum : Summable (fun q : ℤ =>
      Theorem12.Generic.sincShiftCoeff k t q * fourier q y) := by
    apply Summable.of_norm
    simpa only [norm_mul, fourier_apply, Circle.norm_coe, mul_one] using hnorm
  have hbaseValue :
      (∑' q : ℤ, Theorem12.Generic.sincShiftCoeff k t q * fourier q y) =
        Theorem12.Generic.shiftedCenteredExp k t y := by
    rw [← Theorem12.Generic.sinc_shift_identity k t ht htInt y]
    unfold Theorem12.Generic.sincShiftSeries
    apply tsum_congr
    intro q
    rw [hfourier q]
  have hbaseHas : HasSum
      (fun q : ℤ => Theorem12.Generic.sincShiftCoeff k t q * fourier q y)
      (Theorem12.Generic.shiftedCenteredExp k t y) := by
    rw [← hbaseValue]
    exact hbaseSum.hasSum
  let common : ℂ := intParity (floorBeta beta j) * slice data j u *
    fourier n u * fourier (floorBeta beta j) y
  have hmul := hbaseHas.mul_left common
  have hterm (q : ℤ) : rowSincSummand data j k n q u =
      common * (Theorem12.Generic.sincShiftCoeff k t q * fourier q y) := by
    simp only [rowSincSummand]
    rw [fourier_add]
    dsimp only [common, t, y]
    ring
  have hlimit : collapsedRowIntegrand data j k n u =
      common * Theorem12.Generic.shiftedCenteredExp k t y := by
    simp only [collapsedRowIntegrand, Theorem12.Generic.shiftedCenteredExp]
    dsimp only [common, t, y]
    rw [hfourier k]
    ring
  rw [hlimit]
  simpa only [hterm] using hmul

/-
The helper preserves the positive translation and the exact Bochner Haar integrals.
-/
theorem four_031_integral_intEvalSummand_eq_translatedRowSummand
    {alpha : ℝ} {beta : ℚ} {S : Set ℝ} {f : ℝ → ℂ}
    (data : PositiveInputData alpha beta S f) (hbetaSmall : |(beta : ℝ)| < 1 / 2)
    (j k n q : ℤ) :
    (∫ x : AddCircle (1 : ℝ), intEvalSummand data k x (j, q) * fourier n x
      ∂AddCircle.haarAddCircle) =
      ∫ u : AddCircle (1 : ℝ), translatedRowSummand data j k n q u
        ∂AddCircle.haarAddCircle := by
  let shift : AddCircle (1 : ℝ) :=
    (((((floorBeta beta j + q : ℤ) : ℝ) * alpha : ℝ)) : AddCircle (1 : ℝ))
  let integrand : AddCircle (1 : ℝ) → ℂ := fun x =>
    intEvalSummand data k x (j, q) * fourier n x
  have htranslate := (Theorem12.Generic.measurePreserving_addCircle_add shift).integral_comp
    (Homeomorph.addRight shift).isClosedEmbedding.measurableEmbedding integrand
  symm
  simpa only [translatedRowSummand, shift, integrand] using htranslate

end Theorem12.ScaffoldAxioms

namespace Theorem12.Internal

/- Proof idea: choose one `u` in the conull row-good set before every `q`, delete each bad
branch, apply all coordinate/slice/character translations, and normalize the sinc coefficient. -/
private theorem translatedRowSummand_eq_ae {alpha : ℝ} {beta : ℚ}
    {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f)
    (hbeta0 : beta ≠ 0) (j k n : ℤ) :
    ∀ᵐ u : AddCircle (1 : ℝ) ∂AddCircle.haarAddCircle, ∀ q : ℤ,
      translatedRowSummand data j k n q u = rowSincSummand data j k n q u :=
  Theorem12.ScaffoldAxioms.four_029_translatedRowSummand_eq_ae
    data hbeta0 j k n

/- Proof idea: factor the common terms and split the final character, specialize the pointwise
sinc identity at `rotationPoint alpha n`, and package summability and value as `HasSum`. -/
private theorem hasSum_rowSincSummand {alpha : ℝ} {beta : ℚ}
    {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f)
    (hbetaSmall : |(beta : ℝ)| < 1 / 2) (j k n : ℤ)
    (u : AddCircle (1 : ℝ)) (hu : rowGood alpha beta j u) :
    HasSum (fun q : ℤ => rowSincSummand data j k n q u)
      (collapsedRowIntegrand data j k n u) :=
  Theorem12.ScaffoldAxioms.four_030_hasSum_rowSincSummand
    data hbetaSmall j k n u hu

/- Proof idea: apply Bochner Haar translation invariance with the positive displayed shift,
using `summable_integral_norm_intEvalSummand` for integrability, and unfold `translatedRowSummand`. -/
private theorem integral_intEvalSummand_eq_translatedRowSummand
    {alpha : ℝ} {beta : ℚ} {S : Set ℝ} {f : ℝ → ℂ}
    (data : PositiveInputData alpha beta S f) (hbetaSmall : |(beta : ℝ)| < 1 / 2)
    (j k n q : ℤ) :
    (∫ x : AddCircle (1 : ℝ), intEvalSummand data k x (j, q) * fourier n x
      ∂AddCircle.haarAddCircle) =
      ∫ u : AddCircle (1 : ℝ), translatedRowSummand data j k n q u
        ∂AddCircle.haarAddCircle :=
  Theorem12.ScaffoldAxioms.four_031_integral_intEvalSummand_eq_translatedRowSummand
    data hbetaSmall j k n q

/- Proof idea: translate every integral, simplify all rows on one common conull set, use the
pointwise row `HasSum`, and justify series/integral interchange from absolute summability. -/
theorem sum_q_integral_intEvalSummand {alpha : ℝ} {beta : ℚ}
    {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f)
    (hbeta0 : beta ≠ 0) (hbetaSmall : |(beta : ℝ)| < 1 / 2) (j k n : ℤ) :
    (∑' q : ℤ, ∫ x : AddCircle (1 : ℝ),
      intEvalSummand data k x (j, q) * fourier n x ∂AddCircle.haarAddCircle) =
      ∫ u : AddCircle (1 : ℝ), collapsedRowIntegrand data j k n u
        ∂AddCircle.haarAddCircle := by
  obtain ⟨Ck, hCk, hbound⟩ := Theorem12.Generic.norm_sincShiftCoeff_le k
  have hunit : Measurable Theorem12.Generic.unitRep := by
    apply measurable_of_continuousOn_compl_singleton (0 : AddCircle (1 : ℝ))
    intro y hy
    exact (continuousAt_subtype_val.comp
      (AddCircle.continuousAt_equivIco (1 : ℝ) 0 hy)).continuousWithinAt
  have htMeas : Measurable (translatedTRow beta j) := by
    unfold translatedTRow
    fun_prop
  have hrowInt (q : ℤ) : Integrable (fun u : AddCircle (1 : ℝ) =>
      rowSincSummand data j k n q u) AddCircle.haarAddCircle := by
    let multiplier : AddCircle (1 : ℝ) → ℂ := fun u =>
      intParity (floorBeta beta j) *
        Theorem12.Generic.sincShiftCoeff k (translatedTRow beta j u) q *
        fourier n u * fourier (floorBeta beta j + q) (rotationPoint alpha n)
    have hmultMeas : AEStronglyMeasurable multiplier AddCircle.haarAddCircle := by
      apply Measurable.aestronglyMeasurable
      unfold multiplier Theorem12.Generic.sincShiftCoeff
      fun_prop
    have hmultBound : ∀ᵐ u : AddCircle (1 : ℝ) ∂AddCircle.haarAddCircle,
        ‖multiplier u‖ ≤ Ck / (1 + (q : ℝ) ^ 2) := by
      filter_upwards [rowGood_ae alpha beta hbeta0 j] with u hu
      have ht : |translatedTRow beta j u| < 3 / 2 := by
        have h := abs_tCoord_lt_three_halves alpha beta hbetaSmall
          (u + (((((floorBeta beta j + 0 : ℤ) : ℝ) * alpha : ℝ)) : AddCircle (1 : ℝ))) j 0
        rw [tCoord_translate] at h
        exact h
      have hsinc := hbound (translatedTRow beta j u) ht hu.2 q
      unfold multiplier
      simpa only [norm_mul, intParity, norm_zpow, norm_neg, norm_one, one_zpow,
        one_mul, fourier_apply, Circle.norm_coe, mul_one] using hsinc
    have h := (integrable_slice data j).mul_bdd hmultMeas hmultBound
    simpa only [rowSincSummand, multiplier, mul_assoc, mul_left_comm, mul_comm] using h
  have htranslatedInt (q : ℤ) : Integrable (fun u : AddCircle (1 : ℝ) =>
      translatedRowSummand data j k n q u) AddCircle.haarAddCircle := by
    apply (hrowInt q).congr
    exact (translatedRowSummand_eq_ae data hbeta0 j k n).mono fun u hu => (hu q).symm
  have hnormEq (q : ℤ) :
      (∫ u : AddCircle (1 : ℝ), ‖translatedRowSummand data j k n q u‖
        ∂AddCircle.haarAddCircle) =
      ∫ x : AddCircle (1 : ℝ), ‖intEvalSummand data k x (j, q)‖
        ∂AddCircle.haarAddCircle := by
    let shift : AddCircle (1 : ℝ) :=
      (((((floorBeta beta j + q : ℤ) : ℝ) * alpha : ℝ)) : AddCircle (1 : ℝ))
    let g : AddCircle (1 : ℝ) → ℝ := fun x =>
      ‖intEvalSummand data k x (j, q) * fourier n x‖
    have htranslate := (Theorem12.Generic.measurePreserving_addCircle_add shift).integral_comp
      (Homeomorph.addRight shift).isClosedEmbedding.measurableEmbedding g
    simpa only [translatedRowSummand, shift, g, norm_mul, fourier_apply,
      Circle.norm_coe, mul_one] using htranslate
  have hsumNorm : Summable (fun q : ℤ =>
      ∫ u : AddCircle (1 : ℝ), ‖translatedRowSummand data j k n q u‖
        ∂AddCircle.haarAddCircle) := by
    simpa only [hnormEq] using
      (summable_integral_norm_intEvalSummand data hbetaSmall k).prod_factor j
  have hinterchange := integral_tsum_of_summable_integral_norm htranslatedInt hsumNorm
  calc
    (∑' q : ℤ, ∫ x : AddCircle (1 : ℝ),
        intEvalSummand data k x (j, q) * fourier n x
          ∂AddCircle.haarAddCircle) =
        ∑' q : ℤ, ∫ u : AddCircle (1 : ℝ),
          translatedRowSummand data j k n q u
          ∂AddCircle.haarAddCircle := by
      apply tsum_congr
      intro q
      exact integral_intEvalSummand_eq_translatedRowSummand
        data hbetaSmall j k n q
    _ = ∫ u : AddCircle (1 : ℝ),
        ∑' q : ℤ, translatedRowSummand data j k n q u
        ∂AddCircle.haarAddCircle := hinterchange
    _ = ∫ u : AddCircle (1 : ℝ), collapsedRowIntegrand data j k n u
        ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      filter_upwards [translatedRowSummand_eq_ae data hbeta0 j k n,
        rowGood_ae alpha beta hbeta0 j] with u htranslate hgood
      rw [tsum_congr htranslate]
      exact (hasSum_rowSincSummand data hbetaSmall j k n u hgood.1).tsum_eq

/- Proof idea: express parity as the half-period exponential, combine all exponents, substitute
`t=beta*(u+j)-m`, cancel `m`, and identify `delta=beta*(fract(n*alpha)-1/2)`. -/
theorem phase_identity (alpha : ℝ) (beta : ℚ) (j n : ℤ) (u : ℝ)
    (hu : u ∈ Set.Ico (0 : ℝ) 1) :
    let m : ℤ := floorBeta beta j
    let t : ℝ := (beta : ℝ) * (u + (j : ℝ)) - (m : ℝ)
    let y : ℝ := Int.fract ((n : ℝ) * alpha)
    intParity m *
        Complex.exp
          (((2 * Real.pi : ℝ) : ℂ) * Complex.I * (m : ℂ) * (y : ℂ)) *
        Complex.exp
          (((2 * Real.pi : ℝ) : ℂ) * Complex.I * (t : ℂ) *
            ((y - 1 / 2 : ℝ) : ℂ)) =
      Complex.exp
        (((2 * Real.pi : ℝ) : ℂ) * Complex.I * (Theorem12.delta alpha beta n : ℂ) *
          (((u : ℝ) + (j : ℝ) : ℝ) : ℂ)) := by
  simp only
  rw [intParity, ← Complex.exp_pi_mul_I, ← Complex.exp_int_mul,
    ← Complex.exp_add, ← Complex.exp_add]
  let m : ℤ := floorBeta beta j
  let y : ℝ := Int.fract ((n : ℝ) * alpha)
  have harg :
      (m : ℂ) * ((Real.pi : ℂ) * Complex.I) +
          ((2 * Real.pi : ℝ) : ℂ) * Complex.I * (m : ℂ) * (y : ℂ) +
          ((2 * Real.pi : ℝ) : ℂ) * Complex.I *
            (((beta : ℝ) * (u + (j : ℝ)) - (m : ℝ) : ℝ) : ℂ) *
              ((y - 1 / 2 : ℝ) : ℂ) =
        (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) +
          ((2 * Real.pi : ℝ) : ℂ) * Complex.I *
            (((beta : ℝ) * (y - 1 / 2) : ℝ) : ℂ) *
              (((u : ℝ) + (j : ℝ) : ℝ) : ℂ) := by
    push_cast
    ring
  change Complex.exp
      ((m : ℂ) * ((Real.pi : ℂ) * Complex.I) +
        ((2 * Real.pi : ℝ) : ℂ) * Complex.I * (m : ℂ) * (y : ℂ) +
        ((2 * Real.pi : ℝ) : ℂ) * Complex.I *
          (((beta : ℝ) * (u + (j : ℝ)) - (m : ℝ) : ℝ) : ℂ) *
            ((y - 1 / 2 : ℝ) : ℂ)) = _
  rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I]
  simp only [one_mul, Theorem12.delta]
  rfl

end Theorem12.Internal

namespace Theorem12.ScaffoldAxioms

open Theorem12.Internal

/-
This helper is exactly the absolute summability certificate consumed before
the outer `j`-sum is recombined.
-/
theorem four_032_summable_integral_norm_collapsedRow {alpha : ℝ} {beta : ℚ}
    {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f)
    (hbetaSmall : |(beta : ℝ)| < 1 / 2) (k n : ℤ) :
    Summable (fun j : ℤ =>
      ∫ u : AddCircle (1 : ℝ), ‖collapsedRowIntegrand data j k n u‖
        ∂AddCircle.haarAddCircle) := by
  have hslice : Summable (fun j : ℤ =>
      2 * ∫ u : AddCircle (1 : ℝ), ‖slice data j u‖
        ∂AddCircle.haarAddCircle) :=
    (hasSum_integral_norm_slice data).summable.mul_left 2
  refine Summable.of_nonneg_of_le
    (fun j => integral_nonneg fun u => norm_nonneg _) ?_ hslice
  intro j
  have hpoint (u : AddCircle (1 : ℝ)) :
      ‖collapsedRowIntegrand data j k n u‖ ≤ 2 * ‖slice data j u‖ := by
    have hdiff : ‖fourier k (rotationPoint alpha n) - 1‖ ≤ 2 := by
      calc
        ‖fourier k (rotationPoint alpha n) - 1‖ ≤
            ‖fourier k (rotationPoint alpha n)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [fourier_apply, Circle.norm_coe]; norm_num
    have hcenter : ‖Theorem12.Generic.centeredExp
        (translatedTRow beta j u) (rotationPoint alpha n)‖ = 1 := by
      unfold Theorem12.Generic.centeredExp
      rw [Complex.norm_exp]
      norm_num
    unfold collapsedRowIntegrand
    simp only [norm_mul, intParity, norm_zpow, norm_neg, norm_one, one_zpow,
      fourier_apply, Circle.norm_coe, mul_one, hcenter]
    exact mul_le_mul_of_nonneg_right hdiff (norm_nonneg _)
  have hupper : Integrable (fun u : AddCircle (1 : ℝ) =>
      2 * ‖slice data j u‖) AddCircle.haarAddCircle :=
    (integrable_slice data j).norm.const_mul 2
  calc
    (∫ u : AddCircle (1 : ℝ), ‖collapsedRowIntegrand data j k n u‖
      ∂AddCircle.haarAddCircle) ≤
        ∫ u : AddCircle (1 : ℝ), 2 * ‖slice data j u‖
          ∂AddCircle.haarAddCircle :=
      integral_mono_of_nonneg (ae_of_all _ fun u => norm_nonneg _)
        hupper (ae_of_all _ hpoint)
    _ = 2 * ∫ u : AddCircle (1 : ℝ), ‖slice data j u‖
        ∂AddCircle.haarAddCircle := integral_const_mul 2 _

end Theorem12.ScaffoldAxioms

namespace Theorem12.Internal

/- Proof idea: bound all unit-norm character, parity, and centered-exponential factors and
`‖fourier k y-1‖` by two, then compare with the summable slice-norm family. -/
private theorem summable_integral_norm_collapsedRow {alpha : ℝ} {beta : ℚ}
    {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f)
    (hbetaSmall : |(beta : ℝ)| < 1 / 2) (k n : ℤ) :
    Summable (fun j : ℤ =>
      ∫ u : AddCircle (1 : ℝ), ‖collapsedRowIntegrand data j k n u‖
        ∂AddCircle.haarAddCircle) :=
  Theorem12.ScaffoldAxioms.four_032_summable_integral_norm_collapsedRow
    data hbetaSmall k n

/- Proof idea: sum the row identity over `j`, apply the exact phase identity, combine `n` with
`delta_n` into `frequency`, and use Bochner integer tiling to recover the whole-line integral. -/
theorem integral_intEvaluator_mul_character_eq_sample {alpha : ℝ} {beta : ℚ}
    {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f)
    (hbeta0 : beta ≠ 0) (hbetaSmall : |(beta : ℝ)| < 1 / 2) (k n : ℤ) :
    (∫ x : AddCircle (1 : ℝ), intEvaluator data k x * fourier n x
      ∂AddCircle.haarAddCircle) =
      (Complex.exp
          (((2 * Real.pi : ℝ) : ℂ) * Complex.I * (k : ℂ) *
            ((((n : ℤ) : ℝ) * alpha : ℝ) : ℂ)) - 1) *
        ∫ s : ℝ, data.g s *
          Complex.exp
            (((2 * Real.pi : ℝ) : ℂ) * Complex.I *
              (Theorem12.frequency alpha beta n : ℂ) * (s : ℂ)) ∂volume := by
  let multiplier : ℂ := Complex.exp
    (((2 * Real.pi : ℝ) : ℂ) * Complex.I * (k : ℂ) *
      ((((n : ℤ) : ℝ) * alpha : ℝ) : ℂ)) - 1
  let wholeIntegrand : ℝ → ℂ := fun s => data.g s *
    Complex.exp
      (((2 * Real.pi : ℝ) : ℂ) * Complex.I *
        (Theorem12.frequency alpha beta n : ℂ) * (s : ℂ))
  have hwholeInt : Integrable wholeIntegrand volume := by
    apply data.integrable_g.mul_bdd (c := 1)
    · apply Continuous.aestronglyMeasurable
      fun_prop
    · filter_upwards
      intro s
      rw [Complex.norm_exp]
      norm_num
  have hfourierUnit (r : ℤ) (v : AddCircle (1 : ℝ)) : fourier r v =
      Complex.exp
        (((2 * Real.pi : ℝ) : ℂ) * Complex.I * (r : ℂ) *
          (Theorem12.Generic.unitRep v : ℂ)) := by
    calc
      fourier r v = fourier r
          ((Theorem12.Generic.unitRep v : ℝ) : AddCircle (1 : ℝ)) := by
        rw [Theorem12.Generic.coe_unitRep]
      _ = _ := by
        rw [fourier_coe_apply]
        push_cast
        congr 1
        ring
  have hphaseCircle (j : ℤ) (v : AddCircle (1 : ℝ)) :
      intParity (floorBeta beta j) *
          fourier (floorBeta beta j) (rotationPoint alpha n) *
          Theorem12.Generic.centeredExp (translatedTRow beta j v)
            (rotationPoint alpha n) =
        Complex.exp
          (((2 * Real.pi : ℝ) : ℂ) * Complex.I *
            (Theorem12.delta alpha beta n : ℂ) *
              ((Theorem12.Generic.unitRep v + (j : ℝ) : ℝ) : ℂ)) := by
    have h := phase_identity alpha beta j n (Theorem12.Generic.unitRep v)
      (Theorem12.Generic.unitRep_mem_Ico v)
    simp only at h
    rw [hfourierUnit]
    unfold rotationPoint Theorem12.Generic.centeredExp translatedTRow
    rw [Theorem12.Generic.unitRep_coe_eq_fract]
    push_cast at h ⊢
    convert h using 1
  have hfrequencyPhase (j : ℤ) (v : AddCircle (1 : ℝ)) :
      fourier n v *
          Complex.exp
            (((2 * Real.pi : ℝ) : ℂ) * Complex.I *
              (Theorem12.delta alpha beta n : ℂ) *
                ((Theorem12.Generic.unitRep v + (j : ℝ) : ℝ) : ℂ)) =
        Complex.exp
          (((2 * Real.pi : ℝ) : ℂ) * Complex.I *
            (Theorem12.frequency alpha beta n : ℂ) *
              (((j : ℝ) + Theorem12.Generic.unitRep v : ℝ) : ℂ)) := by
    rw [hfourierUnit, ← Complex.exp_add]
    have harg :
        ((2 * Real.pi : ℝ) : ℂ) * Complex.I * (n : ℂ) *
              (Theorem12.Generic.unitRep v : ℂ) +
            ((2 * Real.pi : ℝ) : ℂ) * Complex.I *
              (Theorem12.delta alpha beta n : ℂ) *
                ((Theorem12.Generic.unitRep v + (j : ℝ) : ℝ) : ℂ) =
          ((-(n * j) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) +
            ((2 * Real.pi : ℝ) : ℂ) * Complex.I *
              (Theorem12.frequency alpha beta n : ℂ) *
                (((j : ℝ) + Theorem12.Generic.unitRep v : ℝ) : ℂ) := by
      unfold Theorem12.frequency
      push_cast
      ring
    rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul]
  have hcollapsed (j : ℤ) (v : AddCircle (1 : ℝ)) :
      collapsedRowIntegrand data j k n v =
        multiplier * wholeIntegrand ((j : ℝ) + Theorem12.Generic.unitRep v) := by
    have hk : fourier k (rotationPoint alpha n) - 1 = multiplier := by
      unfold rotationPoint multiplier
      rw [fourier_coe_apply]
      congr 2
      push_cast
      ring
    unfold collapsedRowIntegrand wholeIntegrand
    rw [hk, ← hfrequencyPhase j v, ← hphaseCircle j v]
    unfold slice
    ring
  have hcell (j : ℤ) :
      (∫ v : AddCircle (1 : ℝ), collapsedRowIntegrand data j k n v
        ∂AddCircle.haarAddCircle) =
        multiplier * ∫ v : AddCircle (1 : ℝ),
          wholeIntegrand ((j : ℝ) + Theorem12.Generic.unitRep v)
          ∂AddCircle.haarAddCircle := by
    rw [integral_congr_ae (ae_of_all _ (hcollapsed j)), integral_const_mul]
  have hcomplexSum : Summable (fun a : ℤ × ℤ =>
      ∫ x : AddCircle (1 : ℝ),
        intEvalSummand data k x a * fourier n x
        ∂AddCircle.haarAddCircle) := by
    apply (summable_integral_norm_intEvalSummand data hbetaSmall k).of_norm_bounded
    intro a
    calc
      ‖∫ x : AddCircle (1 : ℝ), intEvalSummand data k x a * fourier n x
          ∂AddCircle.haarAddCircle‖ ≤
          ∫ x : AddCircle (1 : ℝ),
            ‖intEvalSummand data k x a * fourier n x‖
            ∂AddCircle.haarAddCircle := norm_integral_le_integral_norm _
      _ = ∫ x : AddCircle (1 : ℝ), ‖intEvalSummand data k x a‖
          ∂AddCircle.haarAddCircle := by
        apply integral_congr_ae
        filter_upwards
        intro x
        rw [norm_mul, fourier_apply, Circle.norm_coe, mul_one]
  have htiling := Theorem12.Generic.integral_int_tiling_of_integrable
    wholeIntegrand hwholeInt
  calc
    (∫ x : AddCircle (1 : ℝ), intEvaluator data k x * fourier n x
      ∂AddCircle.haarAddCircle) =
        ∑' a : ℤ × ℤ, ∫ x : AddCircle (1 : ℝ),
          intEvalSummand data k x a * fourier n x
          ∂AddCircle.haarAddCircle :=
      integral_intEvaluator_mul_character data hbetaSmall k n
    _ = ∑' j : ℤ, ∑' q : ℤ, ∫ x : AddCircle (1 : ℝ),
          intEvalSummand data k x (j, q) * fourier n x
          ∂AddCircle.haarAddCircle := hcomplexSum.tsum_prod
    _ = ∑' j : ℤ, ∫ v : AddCircle (1 : ℝ),
          collapsedRowIntegrand data j k n v
          ∂AddCircle.haarAddCircle := by
      apply tsum_congr
      intro j
      exact sum_q_integral_intEvalSummand data hbeta0 hbetaSmall j k n
    _ = ∑' j : ℤ, multiplier *
          ∫ v : AddCircle (1 : ℝ),
            wholeIntegrand ((j : ℝ) + Theorem12.Generic.unitRep v)
            ∂AddCircle.haarAddCircle := by
      apply tsum_congr
      exact hcell
    _ = multiplier * ∑' j : ℤ,
          ∫ v : AddCircle (1 : ℝ),
            wholeIntegrand ((j : ℝ) + Theorem12.Generic.unitRep v)
            ∂AddCircle.haarAddCircle := tsum_mul_left
    _ = multiplier * ∫ s : ℝ, wholeIntegrand s ∂volume := by rw [htiling.tsum_eq]
    _ = _ := by rfl

/- Proof idea: rewrite by `integral_intEvaluator_mul_character_eq_sample`, apply the `positiveSamples n` field, and simplify
the resulting multiplier times zero without any irrationality assumption. -/
theorem integral_intEvaluator_mul_character_eq_zero {alpha : ℝ} {beta : ℚ}
    {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f)
    (hbeta0 : beta ≠ 0) (hbetaSmall : |(beta : ℝ)| < 1 / 2) (k n : ℤ) :
    (∫ x : AddCircle (1 : ℝ), intEvaluator data k x * fourier n x
      ∂AddCircle.haarAddCircle) = 0 := by
  rw [integral_intEvaluator_mul_character_eq_sample data hbeta0 hbetaSmall k n,
    data.positiveSamples n, mul_zero]

/- Proof idea: unfold the Mathlib negative-sign coefficient, instantiate the positive moment
theorem at `n=-m`, and normalize the native integer character sign. -/
theorem fourierCoeff_intEvaluator_eq_zero {alpha : ℝ} {beta : ℚ}
    {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f)
    (hbeta0 : beta ≠ 0) (hbetaSmall : |(beta : ℝ)| < 1 / 2) (k m : ℤ) :
    fourierCoeff (intEvaluator data k) m = 0 := by
  rw [fourierCoeff]
  simpa only [smul_eq_mul, mul_comm] using
    integral_intEvaluator_mul_character_eq_zero data hbeta0 hbetaSmall k (-m)

/- Proof idea: combine integrability with vanishing of all negative-sign Fourier coefficients
and apply the generic `L1` Fourier uniqueness theorem. -/
theorem intEvaluator_ae_eq_zero {alpha : ℝ} {beta : ℚ}
    {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f)
    (hbeta0 : beta ≠ 0) (hbetaSmall : |(beta : ℝ)| < 1 / 2) (k : ℤ) :
    intEvaluator data k =ᵐ[AddCircle.haarAddCircle] (fun _ => 0) := by
  exact Theorem12.Generic.ae_eq_zero_of_all_fourierCoeff_eq_zero
    (intEvaluator data k) (integrable_intEvaluator data hbetaSmall k)
    (fourierCoeff_intEvaluator_eq_zero data hbeta0 hbetaSmall k)

/- Proof idea: take the countable intersection of `intEvaluator_ae_eq_zero` over `ℤ`, keeping the
quantifier order literally `∀ᵐ x, ∀ k`. -/
theorem intEvaluator_all_int_ae {alpha : ℝ} {beta : ℚ}
    {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f)
    (hbeta0 : beta ≠ 0) (hbetaSmall : |(beta : ℝ)| < 1 / 2) :
    ∀ᵐ x : AddCircle (1 : ℝ) ∂AddCircle.haarAddCircle, ∀ k : ℤ,
      intEvaluator data k x = 0 := by
  exact ae_all_iff.mpr fun k => intEvaluator_ae_eq_zero data hbeta0 hbetaSmall k

/- Proof idea: literally package the analytic-parameter certificate and simultaneous
fixed-index evaluator zeros, deferring all orbit and density information. -/
structure FourierGoodParameter {alpha : ℝ} {beta : ℚ}
    {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f)
    (x : AddCircle (1 : ℝ)) : Prop where
  analytic : AnalyticParameter data x
  evaluatorZero : ∀ k : ℤ, intEvaluator data k x = 0

/- Proof idea: derive finite support mass from `volume S<1` and intersect the conull
off-bad, finite-weight, and simultaneous integer-evaluator-zero sets. -/
theorem fourierGoodParameter_ae {alpha : ℝ} {beta : ℚ}
    {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f)
    (hbeta0 : beta ≠ 0) (hbetaSmall : |(beta : ℝ)| < 1 / 2)
    (hSlt : volume S < 1) :
    ∀ᵐ x : AddCircle (1 : ℝ) ∂AddCircle.haarAddCircle,
      FourierGoodParameter data x := by
  have hoff : ∀ᵐ x : AddCircle (1 : ℝ) ∂AddCircle.haarAddCircle,
      x ∉ sineBad alpha beta :=
    measure_eq_zero_iff_ae_notMem.mp (sineBad_null alpha beta hbeta0)
  have hfinite := poleWeight_tsum_lt_top_ae data hbetaSmall
    (supportMassENN_ne_top data hSlt)
  filter_upwards [hoff, hfinite,
    intEvaluator_all_int_ae data hbeta0 hbetaSmall] with x hxBad hxFinite hxZero
  exact ⟨⟨hxBad, hxFinite⟩, hxZero⟩

/- Proof idea: rewrite `activeM` at each integer through the fixed-to-active bridge and
apply the packaged simultaneous evaluator-zero field. -/
theorem activeM_int_eq_zero {alpha : ℝ} {beta : ℚ}
    {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f)
    (x : AddCircle (1 : ℝ)) (hx : FourierGoodParameter data x) (k : ℤ) :
    activeM data x (k : ℂ) = 0 := by
  rw [← intEvaluator_eq_activeM_int data x hx.analytic k]
  exact hx.evaluatorZero k

end Theorem12.Internal
