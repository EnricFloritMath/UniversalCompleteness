import Theorem12.GenericAuxiliary
import Theorem12.SupportSlicing
import Theorem12.PoleCoordinates

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Theorem12.Internal

/- Proof idea: add the ENNReal residue norm and active indicator, then divide by the positive
ENNReal image of `1 + poleCoord^2`. -/
def poleWeightENN {dataAlpha : ℝ} {dataBeta : ℚ} {S : Set ℝ} {f : ℝ → ℂ}
    (data : PositiveInputData dataAlpha dataBeta S f) (alpha : ℝ) (beta : ℚ)
    (x : AddCircle (1 : ℝ)) (a : ℤ × ℤ) : ENNReal := open Classical in
  (ENNReal.ofReal ‖residueCoord data alpha beta x a.1 a.2‖ +
      if residueCoord data alpha beta x a.1 a.2 ≠ 0 then 1 else 0) /
    ENNReal.ofReal (1 + (poleCoord alpha beta x a.1 a.2) ^ 2)

/- Proof idea: compose AddCircle translations and `unitRep` with the strongly measurable fixed
representative, then close under sine, norm, indicator, ENNReal coercion, and arithmetic. -/
theorem aemeasurable_poleWeightENN {alpha : ℝ} {beta : ℚ} {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f) (a : ℤ × ℤ) : AEMeasurable (fun x : AddCircle (1 : ℝ) => poleWeightENN data alpha beta x a) AddCircle.haarAddCircle := by
  classical
  have hunit : Measurable Theorem12.Generic.unitRep := by
    apply measurable_of_continuousOn_compl_singleton (0 : AddCircle (1 : ℝ))
    intro y hy
    exact (continuousAt_subtype_val.comp
      (AddCircle.continuousAt_equivIco (1 : ℝ) 0 hy)).continuousWithinAt
  have huClass : Measurable (fun x : AddCircle (1 : ℝ) =>
      uCoordClass alpha beta x a.1 a.2) := by
    unfold uCoordClass
    fun_prop
  have hu : Measurable (fun x : AddCircle (1 : ℝ) =>
      uCoord alpha beta x a.1 a.2) := by
    exact hunit.comp huClass
  have ht : Measurable (fun x : AddCircle (1 : ℝ) =>
      tCoord alpha beta x a.1 a.2) := by
    unfold tCoord
    fun_prop
  have hp : Measurable (fun x : AddCircle (1 : ℝ) =>
      poleCoord alpha beta x a.1 a.2) := by
    unfold poleCoord
    fun_prop
  have hslice : Measurable (fun x : AddCircle (1 : ℝ) =>
      slice data a.1 (uCoordClass alpha beta x a.1 a.2)) := by
    unfold slice
    exact data.stronglyMeasurable_g.measurable.comp (measurable_const.add (hunit.comp huClass))
  have hres : Measurable (fun x : AddCircle (1 : ℝ) =>
      residueCoord data alpha beta x a.1 a.2) := by
    unfold residueCoord
    fun_prop
  have hactive : Measurable (fun x : AddCircle (1 : ℝ) =>
      if residueCoord data alpha beta x a.1 a.2 ≠ 0 then (1 : ENNReal) else 0) := by
    apply Measurable.ite
    · convert (hres (measurableSet_singleton (0 : ℂ))).compl using 1
      ext y
      simp
    · exact measurable_const
    · exact measurable_const
  exact ((hres.norm.ennreal_ofReal.add hactive).div
    ((measurable_const.add (hp.pow_const 2)).ennreal_ofReal)).aemeasurable

/- Proof idea: combine `|p-q| < 3/2` with the quadratic inequality for `q = p + (q-p)`,
obtain the factor six, and invert the positive quantities. -/
theorem inv_one_add_pole_sq_le (alpha : ℝ) (beta : ℚ) (hbetaSmall : |(beta : ℝ)| < 1 / 2) (x : AddCircle (1 : ℝ)) (j q : ℤ) : (1 + (poleCoord alpha beta x j q) ^ 2)⁻¹ ≤ 6 * (1 + (q : ℝ) ^ 2)⁻¹ := by
  have hdist := abs_poleCoord_sub_q_lt alpha beta hbetaSmall x j q
  have hdistSq : (poleCoord alpha beta x j q - (q : ℝ)) ^ 2 < (3 / 2 : ℝ) ^ 2 :=
    sq_lt_sq.mpr (by simpa [abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)] using hdist)
  have hden : 1 + (q : ℝ) ^ 2 ≤ 6 * (1 + (poleCoord alpha beta x j q) ^ 2) := by
    nlinarith [sq_nonneg (poleCoord alpha beta x j q + (q : ℝ))]
  have hdiv : (1 : ℝ) / (1 + (poleCoord alpha beta x j q) ^ 2) ≤
      6 / (1 + (q : ℝ) ^ 2) :=
    (div_le_div_iff₀ (by positivity : (0 : ℝ) < 1 + (poleCoord alpha beta x j q) ^ 2)
      (by positivity : (0 : ℝ) < 1 + (q : ℝ) ^ 2)).2 (by simpa using hden)
  simpa [div_eq_mul_inv] using hdiv

private theorem norm_residueCoord_le_norm_slice
    {dataAlpha : ℝ} {dataBeta : ℚ} {S : Set ℝ} {f : ℝ → ℂ}
    (data : PositiveInputData dataAlpha dataBeta S f) (alpha : ℝ) (beta : ℚ)
    (x : AddCircle (1 : ℝ)) (j q : ℤ) :
    ‖residueCoord data alpha beta x j q‖ ≤
      ‖slice data j (uCoordClass alpha beta x j q)‖ := by
  have hsin : |Real.sin (Real.pi * tCoord alpha beta x j q)| ≤ 1 :=
    abs_le.2 ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
  have hpi : (1 : ℝ) ≤ |Real.pi| := by
    rw [abs_of_pos Real.pi_pos]
    linarith [Real.two_le_pi]
  have hratio : |Real.sin (Real.pi * tCoord alpha beta x j q)| / |Real.pi| ≤ 1 :=
    (div_le_one (abs_pos.mpr Real.pi_ne_zero)).2 (hsin.trans hpi)
  have hparity : ‖intParity (floorBeta beta j)‖ = 1 := by
    simp [intParity]
  change ‖intParity (floorBeta beta j) *
      ((Real.sin (Real.pi * tCoord alpha beta x j q) : ℝ) : ℂ) /
      (Real.pi : ℂ) * slice data j (uCoordClass alpha beta x j q)‖ ≤ _
  rw [norm_mul, norm_div, norm_mul, hparity, one_mul,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs]
  simpa [abs_of_pos Real.pi_pos] using
    (mul_le_mul_of_nonneg_right hratio
      (norm_nonneg (slice data j (uCoordClass alpha beta x j q))))

/- Proof idea: bound parity and sine, apply `inv_one_add_pole_sq_le`, dominate the active indicator by the
translated slice indicator, and use Haar translation invariance for both contributions. -/
theorem lintegral_poleWeightENN_le {alpha : ℝ} {beta : ℚ} {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f) (hbetaSmall : |(beta : ℝ)| < 1 / 2) (j q : ℤ) : (∫⁻ x : AddCircle (1 : ℝ), poleWeightENN data alpha beta x (j, q) ∂AddCircle.haarAddCircle) ≤ (ENNReal.ofReal 6 / ENNReal.ofReal (1 + (q : ℝ) ^ 2)) * (ENNReal.ofReal (∫ u : AddCircle (1 : ℝ), ‖slice data j u‖ ∂AddCircle.haarAddCircle) + AddCircle.haarAddCircle (sliceSupport data j)) := by
  classical
  let shift : AddCircle (1 : ℝ) :=
    ((((floorBeta beta j + q : ℤ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ))
  let A : AddCircle (1 : ℝ) → ENNReal := fun u => ENNReal.ofReal ‖slice data j u‖
  let B : AddCircle (1 : ℝ) → ENNReal := fun u =>
    if u ∈ sliceSupport data j then 1 else 0
  let C : ENNReal := ENNReal.ofReal 6 / ENNReal.ofReal (1 + (q : ℝ) ^ 2)
  have hunit : Measurable Theorem12.Generic.unitRep := by
    apply measurable_of_continuousOn_compl_singleton (0 : AddCircle (1 : ℝ))
    intro y hy
    exact (continuousAt_subtype_val.comp
      (AddCircle.continuousAt_equivIco (1 : ℝ) 0 hy)).continuousWithinAt
  have huClass : Measurable (fun x : AddCircle (1 : ℝ) =>
      uCoordClass alpha beta x j q) := by
    unfold uCoordClass
    fun_prop
  have hslice : Measurable (slice data j) := by
    unfold slice
    exact data.stronglyMeasurable_g.measurable.comp (measurable_const.add hunit)
  have hA : Measurable A := hslice.norm.ennreal_ofReal
  have hB : Measurable B := by
    apply Measurable.ite (measurableSet_sliceSupport data j)
    · exact measurable_const
    · exact measurable_const
  have hdenENN (x : AddCircle (1 : ℝ)) :
      (ENNReal.ofReal (1 + (poleCoord alpha beta x j q) ^ 2))⁻¹ ≤ C := by
    rw [← ENNReal.ofReal_inv_of_pos (by positivity :
      (0 : ℝ) < 1 + (poleCoord alpha beta x j q) ^ 2)]
    rw [show C = ENNReal.ofReal (6 / (1 + (q : ℝ) ^ 2)) by
      simp [C, ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < 1 + (q : ℝ) ^ 2)]]
    apply ENNReal.ofReal_le_ofReal
    simpa [div_eq_mul_inv] using inv_one_add_pole_sq_le alpha beta hbetaSmall x j q
  have hpoint (x : AddCircle (1 : ℝ)) :
      poleWeightENN data alpha beta x (j, q) ≤
        C * (A (uCoordClass alpha beta x j q) + B (uCoordClass alpha beta x j q)) := by
    have hnum :
        ENNReal.ofReal ‖residueCoord data alpha beta x j q‖ +
            (if residueCoord data alpha beta x j q ≠ 0 then 1 else 0) ≤
          A (uCoordClass alpha beta x j q) + B (uCoordClass alpha beta x j q) :=
      add_le_add (ENNReal.ofReal_le_ofReal
        (norm_residueCoord_le_norm_slice data alpha beta x j q))
        (residue_indicator_le_slice_indicator data x j q)
    rw [poleWeightENN, div_eq_mul_inv]
    calc
      (ENNReal.ofReal ‖residueCoord data alpha beta x j q‖ +
          if residueCoord data alpha beta x j q ≠ 0 then 1 else 0) *
          (ENNReal.ofReal (1 + (poleCoord alpha beta x j q) ^ 2))⁻¹
          ≤ (A (uCoordClass alpha beta x j q) + B (uCoordClass alpha beta x j q)) * C :=
            mul_le_mul hnum (hdenENN x) bot_le bot_le
      _ = C * (A (uCoordClass alpha beta x j q) + B (uCoordClass alpha beta x j q)) :=
        mul_comm _ _
  have huClass_eq (x : AddCircle (1 : ℝ)) :
      uCoordClass alpha beta x j q = x - shift := by
    rfl
  have hlinA :
      (∫⁻ x : AddCircle (1 : ℝ), A (uCoordClass alpha beta x j q)
        ∂AddCircle.haarAddCircle) =
        ENNReal.ofReal (∫ u : AddCircle (1 : ℝ), ‖slice data j u‖
          ∂AddCircle.haarAddCircle) := by
    simp_rw [huClass_eq]
    rw [Theorem12.Generic.lintegral_addCircle_sub A shift]
    exact (ofReal_integral_eq_lintegral_ofReal (integrable_slice data j).norm
      (ae_of_all _ fun u => norm_nonneg (slice data j u))).symm
  have hlinB :
      (∫⁻ x : AddCircle (1 : ℝ), B (uCoordClass alpha beta x j q)
        ∂AddCircle.haarAddCircle) = AddCircle.haarAddCircle (sliceSupport data j) := by
    simp_rw [huClass_eq]
    rw [Theorem12.Generic.lintegral_addCircle_sub B shift]
    simpa [B, Set.indicator] using
      (lintegral_indicator_one (measurableSet_sliceSupport data j) :
        (∫⁻ u : AddCircle (1 : ℝ), (sliceSupport data j).indicator 1 u
          ∂AddCircle.haarAddCircle) = AddCircle.haarAddCircle (sliceSupport data j))
  calc
    (∫⁻ x : AddCircle (1 : ℝ), poleWeightENN data alpha beta x (j, q)
        ∂AddCircle.haarAddCircle) ≤
        ∫⁻ x : AddCircle (1 : ℝ),
          C * (A (uCoordClass alpha beta x j q) + B (uCoordClass alpha beta x j q))
          ∂AddCircle.haarAddCircle := lintegral_mono hpoint
    _ = C * (∫⁻ x : AddCircle (1 : ℝ),
          A (uCoordClass alpha beta x j q) + B (uCoordClass alpha beta x j q)
          ∂AddCircle.haarAddCircle) :=
      lintegral_const_mul C ((hA.comp huClass).add (hB.comp huClass))
    _ = C * ((∫⁻ x : AddCircle (1 : ℝ), A (uCoordClass alpha beta x j q)
          ∂AddCircle.haarAddCircle) +
          ∫⁻ x : AddCircle (1 : ℝ), B (uCoordClass alpha beta x j q)
            ∂AddCircle.haarAddCircle) := by
      congr 1
      simpa only [Function.comp_apply] using
        (lintegral_add_left (hA.comp huClass)
          (fun x : AddCircle (1 : ℝ) => B (uCoordClass alpha beta x j q)))
    _ = C * (ENNReal.ofReal (∫ u : AddCircle (1 : ℝ), ‖slice data j u‖
          ∂AddCircle.haarAddCircle) + AddCircle.haarAddCircle (sliceSupport data j)) := by
      rw [hlinA, hlinB]
    _ = (ENNReal.ofReal 6 / ENNReal.ofReal (1 + (q : ℝ) ^ 2)) *
        (ENNReal.ofReal (∫ u : AddCircle (1 : ℝ), ‖slice data j u‖
          ∂AddCircle.haarAddCircle) + AddCircle.haarAddCircle (sliceSupport data j)) := by
      rfl

/- Proof idea: use Tonelli, the one-term estimate, the repeated quadratic series, the slice-norm
`HasSum`, and the slice-support mass identity to produce an explicitly finite upper bound. -/
theorem lintegral_tsum_poleWeightENN_lt_top {alpha : ℝ} {beta : ℚ} {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f) (hbetaSmall : |(beta : ℝ)| < 1 / 2) (hSupportFinite : supportMassENN data ≠ ∞) : (∫⁻ x : AddCircle (1 : ℝ), ∑' a : ℤ × ℤ, poleWeightENN data alpha beta x a ∂AddCircle.haarAddCircle) < ∞ := by
  let D : ℤ → ENNReal := fun q =>
    ENNReal.ofReal 6 / ENNReal.ofReal (1 + (q : ℝ) ^ 2)
  let N : ℤ → ENNReal := fun j =>
    ENNReal.ofReal (∫ u : AddCircle (1 : ℝ), ‖slice data j u‖
      ∂AddCircle.haarAddCircle)
  let M : ℤ → ENNReal := fun j => AddCircle.haarAddCircle (sliceSupport data j)
  let W : ℤ → ENNReal := fun j => N j + M j
  have hD_eq (q : ℤ) :
      D q = ENNReal.ofReal (6 * (1 + (q : ℝ) ^ 2)⁻¹) := by
    rw [show D q = ENNReal.ofReal 6 / ENNReal.ofReal (1 + (q : ℝ) ^ 2) by rfl,
      ← ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < 1 + (q : ℝ) ^ 2)]
    simp [div_eq_mul_inv]
  have hDlt : (∑' q : ℤ, D q) < ∞ := by
    simp_rw [hD_eq]
    exact (Theorem12.Generic.summable_one_add_int_sq_inv.mul_left 6).tsum_ofReal_lt_top
  have hNlt : (∑' j : ℤ, N j) < ∞ := by
    exact (hasSum_integral_norm_slice data).summable.tsum_ofReal_lt_top
  have hMlt : (∑' j : ℤ, M j) < ∞ := by
    rw [show (∑' j : ℤ, M j) = supportMassENN data by
      simpa [M] using tsum_sliceSupport_measure data]
    exact lt_top_iff_ne_top.mpr hSupportFinite
  have hWlt : (∑' j : ℤ, W j) < ∞ := by
    rw [show (∑' j : ℤ, W j) = (∑' j : ℤ, N j) + ∑' j : ℤ, M j by
      simpa [W] using (@ENNReal.tsum_add ℤ N M)]
    exact ENNReal.add_lt_top.mpr ⟨hNlt, hMlt⟩
  have hmajor_eq :
      (∑' a : ℤ × ℤ, D a.2 * W a.1) =
        (∑' q : ℤ, D q) * ∑' j : ℤ, W j := by
    rw [ENNReal.tsum_prod']
    simp_rw [ENNReal.tsum_mul_right]
    rw [ENNReal.tsum_mul_left]
  have hmajor_lt : (∑' a : ℤ × ℤ, D a.2 * W a.1) < ∞ := by
    rw [hmajor_eq]
    exact ENNReal.mul_lt_top hDlt hWlt
  rw [lintegral_tsum fun a => aemeasurable_poleWeightENN data a]
  refine (ENNReal.tsum_le_tsum fun a => ?_).trans_lt hmajor_lt
  simpa [D, N, M, W] using
    lintegral_poleWeightENN_le data hbetaSmall a.1 a.2

/- Proof idea: apply the standard theorem that an ENNReal function with finite lintegral is finite AE
to the finite integral supplied by `lintegral_tsum_poleWeightENN_lt_top`. -/
theorem poleWeight_tsum_lt_top_ae {alpha : ℝ} {beta : ℚ} {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f) (hbetaSmall : |(beta : ℝ)| < 1 / 2) (hSupportFinite : supportMassENN data ≠ ∞) : ∀ᵐ x : AddCircle (1 : ℝ) ∂AddCircle.haarAddCircle, (∑' a : ℤ × ℤ, poleWeightENN data alpha beta x a) < ∞ := by
  apply ae_lt_top' (AEMeasurable.tsum fun a => aemeasurable_poleWeightENN data a)
  exact (lintegral_tsum_poleWeightENN_lt_top data hbetaSmall hSupportFinite).ne

/- Proof idea: dominate both real nonnegative components by the `toReal` of the combined ENNReal
weight after its total sum is known non-top. -/
theorem summable_residue_and_indicator_weight {alpha : ℝ} {beta : ℚ} {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f) (x : AddCircle (1 : ℝ)) (hfinite : (∑' a : ℤ × ℤ, poleWeightENN data alpha beta x a) < ∞) : open Classical in Summable (fun a : ℤ × ℤ => ‖residueCoord data alpha beta x a.1 a.2‖ / (1 + (poleCoord alpha beta x a.1 a.2) ^ 2)) ∧ Summable (fun a : ℤ × ℤ => (if residueCoord data alpha beta x a.1 a.2 ≠ 0 then (1 : ℝ) else 0) / (1 + (poleCoord alpha beta x a.1 a.2) ^ 2)) := by
  classical
  let W : ℤ × ℤ → ℝ := fun a => (poleWeightENN data alpha beta x a).toReal
  have hW : Summable W := ENNReal.summable_toReal hfinite.ne
  have hW_eq (a : ℤ × ℤ) :
      W a = (‖residueCoord data alpha beta x a.1 a.2‖ +
          if residueCoord data alpha beta x a.1 a.2 ≠ 0 then (1 : ℝ) else 0) /
        (1 + (poleCoord alpha beta x a.1 a.2) ^ 2) := by
    have hden : 0 ≤ 1 + (poleCoord alpha beta x a.1 a.2) ^ 2 := by positivity
    simp only [W, poleWeightENN, ENNReal.toReal_div]
    rw [ENNReal.toReal_ofReal hden]
    by_cases ha : residueCoord data alpha beta x a.1 a.2 ≠ 0
    · rw [ENNReal.toReal_add ENNReal.ofReal_ne_top (by simp [ha])]
      simp [ha]
    · simp [not_ne_iff.mp ha]
  constructor
  · refine Summable.of_nonneg_of_le (fun a => by positivity) (fun a => ?_) hW
    rw [hW_eq]
    apply div_le_div_of_nonneg_right
    · split_ifs <;> simp
    · positivity
  · refine Summable.of_nonneg_of_le (fun a => by positivity) (fun a => ?_) hW
    rw [hW_eq]
    apply div_le_div_of_nonneg_right
    · split_ifs <;> simp
    · positivity

/- Proof idea: every active pair with pole in `[-R,R]` contributes at least
`(1 + R^2)⁻¹` to the summable indicator-weight family; apply finite-superlevel finiteness. -/
theorem finite_activePair_pole_Icc {alpha : ℝ} {beta : ℚ} {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f) (x : AddCircle (1 : ℝ)) (hfinite : (∑' a : ℤ × ℤ, poleWeightENN data alpha beta x a) < ∞) (R : ℝ) (hR : 0 ≤ R) : Set.Finite {a : ℤ × ℤ | residueCoord data alpha beta x a.1 a.2 ≠ 0 ∧ poleCoord alpha beta x a.1 a.2 ∈ Set.Icc (-R) R} := by
  classical
  let w : ℤ × ℤ → ℝ := fun a =>
    (if residueCoord data alpha beta x a.1 a.2 ≠ 0 then (1 : ℝ) else 0) /
      (1 + (poleCoord alpha beta x a.1 a.2) ^ 2)
  have hw : Summable w := (summable_residue_and_indicator_weight data x hfinite).2
  have hsuper : Set.Finite {a : ℤ × ℤ | (1 + R ^ 2)⁻¹ ≤ w a} :=
    Theorem12.Generic.Summable.finite_set_le_of_pos w (fun a => by
      simp only [w]
      positivity) hw (by positivity)
  refine hsuper.subset ?_
  intro a ha
  rcases ha with ⟨haActive, haIcc⟩
  have habs : |poleCoord alpha beta x a.1 a.2| ≤ R :=
    abs_le.2 ⟨haIcc.1, haIcc.2⟩
  have hsq : (poleCoord alpha beta x a.1 a.2) ^ 2 ≤ R ^ 2 := by
    exact sq_le_sq.mpr (by simpa [abs_of_nonneg hR] using habs)
  have hinv : (1 + R ^ 2)⁻¹ ≤ (1 + (poleCoord alpha beta x a.1 a.2) ^ 2)⁻¹ :=
    (inv_le_inv₀ (by positivity) (by positivity)).2 (by linarith)
  simpa [w, haActive, div_eq_mul_inv] using hinv

end Theorem12.Internal
