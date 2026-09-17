import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.NumberTheory.Real.Irrational
import SpectralGapsPrelim.BirkhoffPointwise.Basic

noncomputable section

open Filter Function MeromorphicOn Metric MeasureTheory Real Set
open scoped BigOperators ENNReal Topology Pointwise

namespace Theorem12.Generic

/- Proof idea: transparently project `AddCircle.equivIco 0 x` to its real value. -/
def unitRep (x : AddCircle (1 : ℝ)) : ℝ :=
  AddCircle.equivIco (1 : ℝ) 0 x

/- Proof idea: read the subtype membership supplied by the codomain of `equivIco`. -/
theorem unitRep_mem_Ico (x : AddCircle (1 : ℝ)) : unitRep x ∈ Set.Ico (0 : ℝ) 1 := by
  simpa [unitRep] using (AddCircle.equivIco (1 : ℝ) 0 x).property

/- Proof idea: apply the inverse law for `AddCircle.equivIco` and normalize coercions. -/
theorem coe_unitRep (x : AddCircle (1 : ℝ)) :
    ((unitRep x : ℝ) : AddCircle (1 : ℝ)) = x := by
  exact AddCircle.coe_equivIco

/- Proof idea: use uniqueness in `Ico 0 1` together with the `AddCircle.coe_fract` identity. -/
theorem unitRep_coe_eq_fract (r : ℝ) :
    unitRep ((r : ℝ) : AddCircle (1 : ℝ)) = Int.fract r := by
  simpa [unitRep] using AddCircle.coe_equivIco_mk_apply (1 : ℝ) r

/- Proof idea: apply the `Ioc` preimage formula, replace its endpoints by AE congruence,
and identify the period-one representatives to obtain the displayed `Ico` integral. -/
theorem integral_comp_unitRep {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (g : ℝ → E) (hg : IntegrableOn g (Set.Ico (0 : ℝ) 1)) :
    (∫ x : AddCircle (1 : ℝ), g (unitRep x) ∂AddCircle.haarAddCircle) =
      ∫ x in Set.Ico (0 : ℝ) 1, g x := by
  rw [MeasureTheory.integral_Ico_eq_integral_Ioc]
  rw [AddCircle.integral_haarAddCircle]
  simp only [inv_one, one_smul]
  rw [← AddCircle.integral_preimage (1 : ℝ) 0 (fun x => g (unitRep x))]
  simp only [zero_add]
  apply MeasureTheory.integral_congr_ae
  have hmem : ∀ᵐ x : ℝ ∂volume.restrict (Ioc 0 1), x ∈ Ioc 0 1 :=
    MeasureTheory.ae_restrict_mem measurableSet_Ioc
  have hne : ∀ᵐ x : ℝ ∂volume.restrict (Ioc 0 1), x ≠ 1 := by
    rw [MeasureTheory.ae_iff]
    simp
  filter_upwards [hmem, hne] with x hx hxne
  congr 1
  apply AddCircle.equivIco_coe_of_mem
  simpa using (show x ∈ Ico (0 : ℝ) 1 from ⟨hx.1.le, hx.2.lt_of_ne hxne⟩)

/- Proof idea: derive equality of the pushed measures from `integral_comp_unitRep` using measurable
indicators and endpoint nullity, retaining the literal intersection with `Ico 0 1`. -/
theorem measure_unitRep_preimage (A : Set ℝ) (hA : MeasurableSet A) :
    AddCircle.haarAddCircle (unitRep ⁻¹' A) = volume (A ∩ Set.Ico (0 : ℝ) 1) := by
  have hunit : Measurable unitRep :=
    (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable.subtype_val
  have hpre : MeasurableSet (unitRep ⁻¹' A) := hA.preimage hunit
  have hinter : MeasurableSet (A ∩ Ico (0 : ℝ) 1) := hA.inter measurableSet_Ico
  rw [← MeasureTheory.lintegral_indicator_one hpre]
  rw [← MeasureTheory.lintegral_indicator_one hinter]
  have hvol : (volume : Measure (AddCircle (1 : ℝ))) = AddCircle.haarAddCircle := by
    simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ)))
  rw [← hvol]
  rw [← AddCircle.lintegral_preimage (1 : ℝ) 0
    ((unitRep ⁻¹' A).indicator (1 : AddCircle (1 : ℝ) → ENNReal))]
  simp only [zero_add]
  rw [← MeasureTheory.lintegral_indicator measurableSet_Ioc]
  apply MeasureTheory.lintegral_congr_ae
  have hne0 : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simp
  have hne1 : ∀ᵐ x : ℝ ∂volume, x ≠ 1 := by
    rw [MeasureTheory.ae_iff]
    simp
  filter_upwards [hne0, hne1] with x hx0 hx1
  have hiff : x ∈ Ioc (0 : ℝ) 1 ↔ x ∈ Ico (0 : ℝ) 1 := by
    constructor
    · intro hx
      exact ⟨hx.1.le, hx.2.lt_of_ne hx1⟩
    · intro hx
      exact ⟨hx.1.lt_of_ne (Ne.symm hx0), hx.2.le⟩
  by_cases hx : x ∈ Ico (0 : ℝ) 1
  · have hrep : unitRep ((x : ℝ) : AddCircle (1 : ℝ)) = x := by
      apply AddCircle.equivIco_coe_of_mem
      simpa using hx
    have hAiff : ((x : ℝ) : AddCircle (1 : ℝ)) ∈ unitRep ⁻¹' A ↔ x ∈ A := by
      simp only [mem_preimage]
      rw [hrep]
    by_cases hAx : x ∈ A
    · have hleft := hAiff.mpr hAx
      simp [Set.indicator, hiff.mpr hx, hx, hleft, hAx]
    · have hleft : unitRep ((x : ℝ) : AddCircle (1 : ℝ)) ∉ A := by
        simpa [hrep] using hAx
      simp [Set.indicator, hiff.mpr hx, hx, hleft, hAx]
  · have hnot : x ∉ Ioc (0 : ℝ) 1 := fun h => hx (hiff.mp h)
    simp [Set.indicator, hnot, hx]

/- Proof idea: specialize the Haar right-translation theorem to `AddCircle 1`. -/
theorem integral_addCircle_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (g : AddCircle (1 : ℝ) → E)
    (hg : Integrable g AddCircle.haarAddCircle) (a : AddCircle (1 : ℝ)) :
    (∫ x, g (x + a) ∂AddCircle.haarAddCircle) =
      ∫ x, g x ∂AddCircle.haarAddCircle := by
  exact MeasureTheory.integral_add_right_eq_self g a

/- Proof idea: instantiate `integral_addCircle_add` with `-a` and normalize addition as subtraction. -/
theorem integral_addCircle_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (g : AddCircle (1 : ℝ) → E)
    (hg : Integrable g AddCircle.haarAddCircle) (a : AddCircle (1 : ℝ)) :
    (∫ x, g (x - a) ∂AddCircle.haarAddCircle) =
      ∫ x, g x ∂AddCircle.haarAddCircle := by
  exact MeasureTheory.integral_sub_right_eq_self g a

/- Proof idea: specialize `measurePreserving_add_right` at `-a` and normalize subtraction. -/
theorem measurePreserving_addCircle_sub (a : AddCircle (1 : ℝ)) :
    MeasurePreserving (fun x : AddCircle (1 : ℝ) => x - a)
      AddCircle.haarAddCircle AddCircle.haarAddCircle := by
  exact MeasureTheory.measurePreserving_sub_right AddCircle.haarAddCircle a

/- Proof idea: specialize `measurePreserving_add_right` to normalized period-one Haar. -/
theorem measurePreserving_addCircle_add (a : AddCircle (1 : ℝ)) :
    MeasurePreserving (fun x : AddCircle (1 : ℝ) => x + a)
      AddCircle.haarAddCircle AddCircle.haarAddCircle := by
  exact MeasureTheory.measurePreserving_add_right AddCircle.haarAddCircle a

/- Proof idea: specialize `MeasureTheory.lintegral_add_right_eq_self` at period one;
the invariant-measure theorem applies without an added measurability premise. -/
theorem lintegral_addCircle_add (g : AddCircle (1 : ℝ) → ENNReal)
    (a : AddCircle (1 : ℝ)) :
    (∫⁻ x, g (x + a) ∂AddCircle.haarAddCircle) =
      ∫⁻ x, g x ∂AddCircle.haarAddCircle := by
  exact MeasureTheory.lintegral_add_right_eq_self g a

/- Proof idea: apply `lintegral_addCircle_add` at `-a` and normalize subtraction. -/
theorem lintegral_addCircle_sub (g : AddCircle (1 : ℝ) → ENNReal)
    (a : AddCircle (1 : ℝ)) :
    (∫⁻ x, g (x - a) ∂AddCircle.haarAddCircle) =
      ∫⁻ x, g x ∂AddCircle.haarAddCircle := by
  exact MeasureTheory.lintegral_sub_right_eq_self g a

private theorem lintegral_comp_unitRep (g : ℝ → ENNReal) :
    (∫⁻ x : AddCircle (1 : ℝ), g (unitRep x) ∂AddCircle.haarAddCircle) =
      ∫⁻ x in Set.Ico (0 : ℝ) 1, g x := by
  rw [MeasureTheory.restrict_Ico_eq_restrict_Ioc]
  have hvol : (volume : Measure (AddCircle (1 : ℝ))) = AddCircle.haarAddCircle := by
    simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ)))
  rw [← hvol]
  rw [← AddCircle.lintegral_preimage (1 : ℝ) 0 (fun x => g (unitRep x))]
  simp only [zero_add]
  apply MeasureTheory.lintegral_congr_ae
  have hmem : ∀ᵐ x : ℝ ∂volume.restrict (Ioc 0 1), x ∈ Ioc 0 1 :=
    MeasureTheory.ae_restrict_mem measurableSet_Ioc
  have hne : ∀ᵐ x : ℝ ∂volume.restrict (Ioc 0 1), x ≠ 1 := by
    rw [MeasureTheory.ae_iff]
    simp
  filter_upwards [hmem, hne] with x hx hxne
  congr 1
  apply AddCircle.equivIco_coe_of_mem
  simpa using (show x ∈ Ico (0 : ℝ) 1 from ⟨hx.1.le, hx.2.lt_of_ne hxne⟩)

private noncomputable def intEquivZMultiplesOne :
    ℤ ≃ AddSubgroup.zmultiples (1 : ℝ) := by
  let f : ℤ → AddSubgroup.zmultiples (1 : ℝ) :=
    Set.codRestrict (fun n : ℤ => n • (1 : ℝ)) (AddSubgroup.zmultiples (1 : ℝ)) (by
      intro n
      exact ⟨n, rfl⟩)
  exact Equiv.ofBijective f
    (Equiv.ofInjective (fun n : ℤ => n • (1 : ℝ))
      (zsmul_left_strictMono (show (0 : ℝ) < 1 by norm_num)).injective).bijective

/- Proof idea: partition `ℝ` into the half-open cells `[j,j+1)`, translate every cell to
`Ico 0 1`, apply `integral_comp_unitRep`, and interchange the nonnegative countable sum. -/
theorem lintegral_int_tiling (F : ℝ → ENNReal) (hF : Measurable F) :
    (∫⁻ x : ℝ, F x ∂volume) =
      ∑' j : ℤ, ∫⁻ u : AddCircle (1 : ℝ),
        F ((j : ℝ) + unitRep u) ∂AddCircle.haarAddCircle := by
  rw [(isAddFundamentalDomain_Ioc (show (0 : ℝ) < 1 by norm_num) 0 volume).lintegral_eq_tsum'' F]
  simp only [zero_add]
  rw [← (intEquivZMultiplesOne.tsum_eq
    (fun g => ∫⁻ x : ℝ in Ioc (0 : ℝ) 1, F (g +ᵥ x) ∂volume))]
  apply tsum_congr
  intro j
  rw [← MeasureTheory.restrict_Ico_eq_restrict_Ioc]
  rw [lintegral_comp_unitRep (fun x => F ((j : ℝ) + x))]
  simp [intEquivZMultiplesOne, AddSubgroup.vadd_def, vadd_eq_add]

/- Proof idea: apply the nonnegative tiling theorem to `‖F‖`, deduce summability of the
cell-integral norms, and use dominated Bochner series interchange to obtain `HasSum`. -/
theorem integral_int_tiling_of_integrable {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (F : ℝ → E) (hF : Integrable F volume) :
    HasSum
      (fun j : ℤ => ∫ u : AddCircle (1 : ℝ),
        F ((j : ℝ) + unitRep u) ∂AddCircle.haarAddCircle)
      (∫ x : ℝ, F x ∂volume) := by
  have hfd : IsAddFundamentalDomain (AddSubgroup.zmultiples (1 : ℝ))
      (Ioc (0 : ℝ) 1) volume := by
    simpa only [zero_add] using
      isAddFundamentalDomain_Ioc (show (0 : ℝ) < 1 by norm_num) 0 volume
  let μ : AddSubgroup.zmultiples (1 : ℝ) → Measure ℝ :=
    fun g => volume.restrict (g +ᵥ Ioc (0 : ℝ) 1)
  have hsum : Measure.sum μ = volume := hfd.sum_restrict
  have hFsum : Integrable F (Measure.sum μ) := by simpa [hsum] using hF
  have hbound : Summable (fun g : AddSubgroup.zmultiples (1 : ℝ) =>
      ∫ x : ℝ, ‖F x‖ ∂μ g) :=
    hFsum.summable_integral
  have hcells : Summable (fun g : AddSubgroup.zmultiples (1 : ℝ) =>
      ∫ x : ℝ, F x ∂μ g) := by
    apply hbound.of_norm_bounded
    intro g
    calc
      ‖∫ x : ℝ, F x ∂μ g‖ ≤
          (∫⁻ x : ℝ, ENNReal.ofReal ‖F x‖ ∂μ g).toReal :=
        MeasureTheory.norm_integral_le_lintegral_norm F
      _ = ∫ x : ℝ, ‖F x‖ ∂μ g := by
        rw [MeasureTheory.integral_norm_eq_lintegral_enorm]
        · simp only [ofReal_norm]
        · exact hFsum.aestronglyMeasurable.mono_measure (Measure.le_sum μ g)
  have hcell_eq (g : AddSubgroup.zmultiples (1 : ℝ)) :
      (∫ x : ℝ, F x ∂μ g) = ∫ x : ℝ in Ioc (0 : ℝ) 1, F (g +ᵥ x) ∂volume := by
    simpa only [μ, ← image_vadd] using
      (MeasureTheory.measurePreserving_vadd g volume).setIntegral_image_emb
        (measurableEmbedding_const_vadd g) F (Ioc (0 : ℝ) 1)
  have hcells' : Summable (fun g : AddSubgroup.zmultiples (1 : ℝ) =>
      ∫ x : ℝ in Ioc (0 : ℝ) 1, F (g +ᵥ x) ∂volume) :=
    hcells.congr hcell_eq
  have hsub : HasSum (fun g : AddSubgroup.zmultiples (1 : ℝ) =>
      ∫ x : ℝ in Ioc (0 : ℝ) 1, F (g +ᵥ x) ∂volume)
      (∫ x : ℝ, F x ∂volume) := by
    rw [hfd.integral_eq_tsum'' F hF]
    exact hcells'.hasSum
  have hcomp := intEquivZMultiplesOne.hasSum_iff.mpr hsub
  convert hcomp using 1
  funext j
  simp only [Function.comp_apply]
  rw [← MeasureTheory.restrict_Ico_eq_restrict_Ioc]
  have hshift : Integrable (fun x : ℝ => F ((j : ℝ) + x)) volume := by
    have hright : Integrable (fun x : ℝ => F (x + (j : ℝ))) volume := by
      exact ((MeasureTheory.measurePreserving_add_right volume (j : ℝ)).integrable_comp
        hF.aestronglyMeasurable).mpr hF
    simpa only [add_comm] using hright
  rw [integral_comp_unitRep (fun x => F ((j : ℝ) + x)) hshift.integrableOn]
  simp [intEquivZMultiplesOne, AddSubgroup.vadd_def, vadd_eq_add]

/- Proof idea: transport every slice null set to its integer cell using `measure_unitRep_preimage`,
take the countable union, and use that the half-open integer cells cover `ℝ`. -/
theorem ae_of_ae_all_int_slices {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (F : ℝ → E) (hF : StronglyMeasurable F)
    (hslices : ∀ j : ℤ,
      (fun u : AddCircle (1 : ℝ) => F ((j : ℝ) + unitRep u))
        =ᵐ[AddCircle.haarAddCircle] (fun _ => 0)) :
    F =ᵐ[volume] (fun _ => 0) := by
  have hmeas : Measurable (fun x : ℝ => ‖F x‖ₑ) := hF.enorm
  have hzeroIntegral : (∫⁻ x : ℝ, ‖F x‖ₑ ∂volume) = 0 := by
    rw [lintegral_int_tiling (fun x : ℝ => ‖F x‖ₑ) hmeas]
    rw [ENNReal.tsum_eq_zero]
    intro j
    have hsliceNorm :
        (fun u : AddCircle (1 : ℝ) => ‖F ((j : ℝ) + unitRep u)‖ₑ)
          =ᵐ[AddCircle.haarAddCircle] (fun _ => 0) := by
      filter_upwards [hslices j] with u hu
      rw [hu]
      exact enorm_zero
    rw [MeasureTheory.lintegral_congr_ae hsliceNorm]
    exact MeasureTheory.lintegral_zero
  have hnormZero : (fun x : ℝ => ‖F x‖ₑ) =ᵐ[volume] (fun _ => 0) :=
    (MeasureTheory.lintegral_eq_zero_iff hmeas).mp hzeroIntegral
  filter_upwards [hnormZero] with x hx
  have : ‖F x‖ₑ = 0 := by simpa using hx
  exact (enorm_eq_zero.mp this)

/- Proof idea: compare both integer tails to the convergent `1/q^2` p-series and handle
the finitely many central terms separately. -/
theorem summable_one_add_int_sq_inv :
    Summable (fun q : ℤ => (1 + (q : ℝ) ^ 2)⁻¹) := by
  rw [summable_int_iff_summable_nat_and_neg]
  have hmajor : Summable (fun n : ℕ =>
      6 * ((1 / ((n : ℝ) + 1)) - (1 / ((n : ℝ) + 2)))) := by
    apply HasSum.summable
    rw [hasSum_iff_tendsto_nat_of_nonneg]
    · have htelescope : ∀ n : ℕ,
          (∑ i ∈ Finset.range n,
            6 * ((1 / ((i : ℝ) + 1)) - (1 / ((i : ℝ) + 2)))) =
              6 * (1 - 1 / ((n : ℝ) + 1)) := by
        intro n
        rw [← Finset.mul_sum]
        rw [show (∑ i ∈ Finset.range n,
            (1 / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2))) =
            ∑ i ∈ Finset.range n,
              ((fun k : ℕ => 1 / ((k : ℝ) + 1)) i -
                (fun k : ℕ => 1 / ((k : ℝ) + 1)) (i + 1)) by
          apply Finset.sum_congr rfl
          intro i hi
          congr 2
          push_cast
          ring]
        rw [Finset.sum_range_sub']
        norm_num
      simp_rw [htelescope]
      have hlim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      simpa using (hlim.const_sub (1 : ℝ)).const_mul (6 : ℝ)
    · intro n
      have h1 : 0 < (n : ℝ) + 1 := by positivity
      have h2 : 0 < (n : ℝ) + 2 := by positivity
      exact mul_nonneg (by norm_num)
        (sub_nonneg.mpr (one_div_le_one_div_of_le h1 (by linarith)))
  have hnat : Summable (fun n : ℕ => (1 + (n : ℝ) ^ 2)⁻¹) := by
    apply hmajor.of_nonneg_of_le
    · intro n
      positivity
    · intro n
      have h1 : 0 < (n : ℝ) + 1 := by positivity
      have h2 : 0 < (n : ℝ) + 2 := by positivity
      have hsquare : 0 < 1 + (n : ℝ) ^ 2 := by positivity
      rw [inv_eq_one_div]
      rw [div_le_iff₀ hsquare]
      field_simp
      nlinarith [sq_nonneg ((n : ℝ) - 1)]
  exact ⟨hnat, by simpa only [Int.cast_neg, Int.cast_natCast, neg_sq] using hnat⟩

namespace Summable

/- Proof idea: show that infinitely many terms bounded below by positive `c` would make
the finite partial sums unbounded, contradicting summability. -/
theorem finite_set_le_of_pos {A : Type*} [Countable A] (w : A → ℝ)
    (hw_nonneg : ∀ a, 0 ≤ w a) (hw : Summable w) {c : ℝ} (hc : 0 < c) :
    Set.Finite {a : A | c ≤ w a} := by
  have hsmall : ∀ᶠ a in (cofinite : Filter A), w a < c :=
    hw.tendsto_cofinite_zero (Iio_mem_nhds hc)
  simpa only [Filter.eventually_cofinite, not_lt] using hsmall

end Summable

/- Proof idea: rewrite the `tsum` as the finite sum over the explicitly finite support
and normalize the natural-to-ENNReal cast. -/
theorem ennreal_tsum_indicator_eq_ncard {A : Type*} [Countable A]
    (P : A → Prop) [DecidablePred P] (hP : Set.Finite {a : A | P a}) :
    (∑' a : A, if P a then (1 : ENNReal) else 0) = (Set.ncard {a : A | P a} : ENNReal) := by
  calc
    (∑' a : A, if P a then (1 : ENNReal) else 0) =
        ∑' a : A, {a : A | P a}.indicator (fun _ => (1 : ENNReal)) a := by
          congr 1
          funext a
          simp [Set.indicator]
    _ = ∑' _ : {a : A | P a}, (1 : ENNReal) :=
      (tsum_subtype {a : A | P a} (fun _ => (1 : ENNReal))).symm
    _ = (Set.ncard {a : A | P a} : ENNReal) := by
      rw [ENNReal.tsum_set_one, ← hP.cast_ncard_eq]
      exact ENat.toENNReal_coe _

/- Proof idea: thin adapter to the proved two-sided irrational-rotation
Birkhoff theorem, preserving the inverse rotation, inclusive integer interval, and normalization. -/
theorem twoSided_average_irrationalRotation (alpha : ℝ) (halpha : Irrational alpha)
    (phi : AddCircle (1 : ℝ) → ℝ) (hphi : Integrable phi AddCircle.haarAddCircle) :
    ∀ᵐ x : AddCircle (1 : ℝ) ∂AddCircle.haarAddCircle,
      Tendsto
        (fun N : ℕ => (2 * (N : ℝ) + 1)⁻¹ *
          ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
            phi (x - ((((k : ℤ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ))))
        atTop (nhds (∫ y, phi y ∂AddCircle.haarAddCircle)) := by
  let a : AddCircle (1 : ℝ) := ((alpha : ℝ) : AddCircle (1 : ℝ))
  have hvol : (volume : Measure (AddCircle (1 : ℝ))) =
      AddCircle.haarAddCircle := by
    simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ)))
  have hergPlus : Ergodic (fun x : AddCircle (1 : ℝ) => x + a)
      AddCircle.haarAddCircle := by
    rw [← hvol]
    apply AddCircle.ergodic_add_right.mpr
    apply AddCircle.denseRange_zsmul_iff.mp
    exact (AddCircle.denseRange_zsmul_coe_iff (a := alpha) (p := 1)).2
      (by simpa using halpha)
  have hergMinus : Ergodic (fun x : AddCircle (1 : ℝ) => x + (-a))
      AddCircle.haarAddCircle := by
    rw [← hvol]
    apply AddCircle.ergodic_add_right.mpr
    apply AddCircle.denseRange_zsmul_iff.mp
    exact (AddCircle.denseRange_zsmul_coe_iff (a := -alpha) (p := 1)).2
      (by simpa using halpha.neg)
  have hforward :
      ∀ᵐ x : AddCircle (1 : ℝ) ∂AddCircle.haarAddCircle,
        Tendsto
          (fun N : ℕ =>
            (∑ r ∈ Finset.range N,
              phi (x + ((((r : ℕ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ)))) /
                (N : ℝ)) atTop
          (nhds (∫ y, phi y ∂AddCircle.haarAddCircle)) := by
    filter_upwards [SpectralGapsPrelim.BirkhoffPointwise.ae_tendsto_birkhoff_average_of_ergodic
      hergPlus hphi] with x hx
    refine hx.congr' ?_
    filter_upwards with N
    congr 1
    apply Finset.sum_congr rfl
    intro r hr
    rw [add_right_iterate_apply]
    congr 1
    dsimp only [a]
    rw [← AddCircle.coe_nsmul]
    congr 1
    norm_num only [nsmul_eq_mul]
  let psi : AddCircle (1 : ℝ) → ℝ := fun y => phi (y - a)
  have hpsi : Integrable psi AddCircle.haarAddCircle := by
    have hc := (measurePreserving_addCircle_sub a).integrable_comp
      hphi.aestronglyMeasurable
    exact hc.mpr hphi
  have hbackward :
      ∀ᵐ x : AddCircle (1 : ℝ) ∂AddCircle.haarAddCircle,
        Tendsto
          (fun N : ℕ =>
            (∑ r ∈ Finset.range N,
              phi (x - (((((r : ℕ) : ℝ) + 1) * alpha : ℝ) :
                AddCircle (1 : ℝ)))) / (N : ℝ)) atTop
          (nhds (∫ y, phi y ∂AddCircle.haarAddCircle)) := by
    filter_upwards [SpectralGapsPrelim.BirkhoffPointwise.ae_tendsto_birkhoff_average_of_ergodic
      hergMinus hpsi] with x hx
    have hx' := hx
    rw [show (∫ y, psi y ∂AddCircle.haarAddCircle) =
        ∫ y, phi y ∂AddCircle.haarAddCircle by
      exact integral_addCircle_sub phi hphi a] at hx'
    refine hx'.congr' ?_
    filter_upwards with N
    congr 1
    apply Finset.sum_congr rfl
    intro r hr
    rw [add_right_iterate_apply]
    dsimp only [psi, a]
    congr 1
    rw [← AddCircle.coe_neg, ← AddCircle.coe_nsmul]
    have hcast :
        (((r • (-alpha) : ℝ) : AddCircle (1 : ℝ)) -
          ((alpha : ℝ) : AddCircle (1 : ℝ))) =
            -(((((r : ℝ) + 1) * alpha : ℝ) : AddCircle (1 : ℝ))) := by
      rw [← AddCircle.coe_sub, ← AddCircle.coe_neg]
      congr 1
      norm_num only [nsmul_eq_mul]
      ring
    rw [show x + ((r • (-alpha) : ℝ) : AddCircle (1 : ℝ)) -
        ((alpha : ℝ) : AddCircle (1 : ℝ)) =
      x + ((((r • (-alpha) : ℝ) : AddCircle (1 : ℝ))) -
        ((alpha : ℝ) : AddCircle (1 : ℝ))) by abel]
    rw [hcast]
    rfl
  have hsumNeg : ∀ (N : ℕ) (f : ℤ → ℝ),
      (∑ q ∈ Finset.Icc (-(N : ℤ)) 0, f q) =
        ∑ r ∈ Finset.range (N + 1), f (-(r : ℤ)) := by
    intro N f
    refine Finset.sum_bij (fun q hq => Int.toNat (-q)) ?_ ?_ ?_ ?_
    · intro q hq
      rw [Finset.mem_range]
      rw [Finset.mem_Icc] at hq
      exact (Int.toNat_lt_of_ne_zero (m := -q) (Nat.succ_ne_zero N)).2 (by omega)
    · intro q₁ hq₁ q₂ hq₂ heq
      rw [Finset.mem_Icc] at hq₁ hq₂
      have hcast :
          ((Int.toNat (-q₁) : ℕ) : ℤ) = ((Int.toNat (-q₂) : ℕ) : ℤ) := by
        exact_mod_cast heq
      rw [Int.toNat_of_nonneg (by omega : 0 ≤ -q₁),
        Int.toNat_of_nonneg (by omega : 0 ≤ -q₂)] at hcast
      omega
    · intro r hr
      refine ⟨-(r : ℤ), ?_, ?_⟩
      · rw [Finset.mem_Icc]
        rw [Finset.mem_range] at hr
        omega
      · simp
    · intro q hq
      rw [Finset.mem_Icc] at hq
      have hq_eq : -((Int.toNat (-q) : ℕ) : ℤ) = q := by
        rw [Int.toNat_of_nonneg (by omega : 0 ≤ -q)]
        omega
      exact (congrArg f hq_eq).symm
  have hsumPos : ∀ (N : ℕ) (f : ℤ → ℝ),
      (∑ q ∈ Finset.Icc 1 (N : ℤ), f q) =
        ∑ r ∈ Finset.range N, f ((r : ℤ) + 1) := by
    intro N f
    by_cases hN : N = 0
    · subst N
      simp
    refine Finset.sum_bij (fun q hq => Int.toNat (q - 1)) ?_ ?_ ?_ ?_
    · intro q hq
      rw [Finset.mem_range]
      rw [Finset.mem_Icc] at hq
      exact (Int.toNat_lt_of_ne_zero (m := q - 1) hN).2 (by omega)
    · intro q₁ hq₁ q₂ hq₂ heq
      rw [Finset.mem_Icc] at hq₁ hq₂
      have hcast :
          ((Int.toNat (q₁ - 1) : ℕ) : ℤ) =
            ((Int.toNat (q₂ - 1) : ℕ) : ℤ) := by
        exact_mod_cast heq
      rw [Int.toNat_of_nonneg (by omega : 0 ≤ q₁ - 1),
        Int.toNat_of_nonneg (by omega : 0 ≤ q₂ - 1)] at hcast
      omega
    · intro r hr
      refine ⟨(r : ℤ) + 1, ?_, ?_⟩
      · rw [Finset.mem_Icc]
        rw [Finset.mem_range] at hr
        omega
      · simp
    · intro q hq
      rw [Finset.mem_Icc] at hq
      have hq_eq : ((Int.toNat (q - 1) : ℕ) : ℤ) + 1 = q := by
        rw [Int.toNat_of_nonneg (by omega : 0 ≤ q - 1)]
        omega
      exact (congrArg f hq_eq).symm
  filter_upwards [hforward, hbackward] with x hxForward hxBackward
  let f : ℤ → ℝ := fun k =>
    phi (x - ((((k : ℤ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ)))
  let A : ℕ → ℝ := fun N => ∑ r ∈ Finset.range (N + 1), f (-(r : ℤ))
  let B : ℕ → ℝ := fun N => ∑ r ∈ Finset.range N, f ((r : ℤ) + 1)
  let S : ℕ → ℝ := fun N => ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), f k
  have hA : Tendsto (fun N : ℕ => A N / ((N : ℝ) + 1)) atTop
      (nhds (∫ y, phi y ∂AddCircle.haarAddCircle)) := by
    have hs := hxForward.comp (tendsto_add_atTop_nat 1)
    change Tendsto
      (fun N : ℕ =>
        (∑ r ∈ Finset.range (N + 1),
          phi (x + ((((r : ℕ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ)))) /
            ((N + 1 : ℕ) : ℝ)) atTop
      (nhds (∫ y, phi y ∂AddCircle.haarAddCircle)) at hs
    simpa only [Function.comp_apply, Nat.cast_add, Nat.cast_one, A, f,
      Int.cast_neg, Int.cast_natCast, neg_mul, AddCircle.coe_neg,
      sub_neg_eq_add] using hs
  have hB : Tendsto (fun N : ℕ => B N / (N : ℝ)) atTop
      (nhds (∫ y, phi y ∂AddCircle.haarAddCircle)) := by
    simpa only [B, f, Int.cast_add, Int.cast_natCast, Int.cast_one,
      add_mul] using hxBackward
  have hsplit : ∀ N : ℕ, S N = A N + B N := by
    intro N
    have hset : Finset.Icc (-(N : ℤ)) (N : ℤ) =
        Finset.Icc (-(N : ℤ)) 0 ∪ Finset.Icc 1 (N : ℤ) := by
      ext q
      simp
      omega
    have hdisj : Disjoint (Finset.Icc (-(N : ℤ)) 0)
        (Finset.Icc 1 (N : ℤ)) := by
      rw [Finset.disjoint_left]
      intro q hq0 hq1
      rw [Finset.mem_Icc] at hq0 hq1
      omega
    dsimp only [S, A, B]
    rw [hset, Finset.sum_union hdisj, hsumNeg N f, hsumPos N f]
  have hden : Tendsto (fun N : ℕ => 4 * (N : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 4))
  have hsmall : Tendsto (fun N : ℕ => (4 * (N : ℝ) + 2)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hden
  have hwA : Tendsto
      (fun N : ℕ => ((N : ℝ) + 1) / (2 * (N : ℝ) + 1)) atTop
      (nhds (1 / 2 : ℝ)) := by
    have h := (tendsto_const_nhds.add hsmall : Tendsto
      (fun N : ℕ => (1 / 2 : ℝ) + (4 * (N : ℝ) + 2)⁻¹) atTop
      (nhds ((1 / 2 : ℝ) + 0)))
    simpa only [add_zero] using h.congr' (by
      filter_upwards with N
      have hd : (2 * (N : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      ring)
  have hwB : Tendsto
      (fun N : ℕ => (N : ℝ) / (2 * (N : ℝ) + 1)) atTop
      (nhds (1 / 2 : ℝ)) := by
    have h := (tendsto_const_nhds.sub hsmall : Tendsto
      (fun N : ℕ => (1 / 2 : ℝ) - (4 * (N : ℝ) + 2)⁻¹) atTop
      (nhds ((1 / 2 : ℝ) - 0)))
    simpa only [sub_zero] using h.congr' (by
      filter_upwards with N
      have hd : (2 * (N : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      ring)
  have hcombined := (hwA.mul hA).add (hwB.mul hB)
  have hlimit : (1 / 2 : ℝ) * (∫ y, phi y ∂AddCircle.haarAddCircle) +
      (1 / 2 : ℝ) * (∫ y, phi y ∂AddCircle.haarAddCircle) =
        ∫ y, phi y ∂AddCircle.haarAddCircle := by ring
  rw [hlimit] at hcombined
  refine hcombined.congr' ?_
  filter_upwards [Nat.eventually_pos] with N hN
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hN1R : (N : ℝ) + 1 ≠ 0 := by positivity
  have hdenR : 2 * (N : ℝ) + 1 ≠ 0 := by positivity
  change
    ((N : ℝ) + 1) / (2 * (N : ℝ) + 1) * (A N / ((N : ℝ) + 1)) +
        (N : ℝ) / (2 * (N : ℝ) + 1) * (B N / (N : ℝ)) =
      (2 * (N : ℝ) + 1)⁻¹ * S N
  rw [hsplit N]
  field_simp

/- Proof idea: retain global meromorphicity, exclude infinite order, choose its literal integer
representative at every point, and record local finiteness of nonzero orders on closed balls. -/
structure MeromorphicCountingData (F : ℂ → ℂ) where
  meromorphicOn_univ : MeromorphicOn F Set.univ
  order_ne_top : ∀ z : ℂ, meromorphicOrderAt F z ≠ (⊤ : WithTop ℤ)
  order : ℂ → ℤ
  order_spec : ∀ z : ℂ, ((order z : ℤ) : WithTop ℤ) = meromorphicOrderAt F z
  finite_orderSupport_closedBall : ∀ R : ℝ,
    Set.Finite ({z : ℂ | order z ≠ 0} ∩ Metric.closedBall 0 R)

/- Proof idea: return zero at nonpositive radii; otherwise turn the proved finite divisor
support in the closed ball into a finset, restrict it to the open disk, and sum positive orders. -/
def zeroCount {F : ℂ → ℂ} (data : MeromorphicCountingData F) (R : ℝ) : ℕ :=
  if R ≤ 0 then 0
  else
    ∑ z ∈ (data.finite_orderSupport_closedBall R).toFinset,
      if ‖z‖ < R then Int.toNat (data.order z) else 0

/- Proof idea: use the same finite divisor finset as `zeroCount`, restrict it to the open
disk, and sum the natural multiplicities of the negative integer orders. -/
def poleCount {F : ℂ → ℂ} (data : MeromorphicCountingData F) (R : ℝ) : ℕ :=
  if R ≤ 0 then 0
  else
    ∑ z ∈ (data.finite_orderSupport_closedBall R).toFinset,
      if ‖z‖ < R then Int.toNat (-data.order z) else 0

/- Proof idea: transparently parametrize the radius-`R` circle once over `Ioc 0 (2*pi)`,
integrate the ordinary logarithm of the norm, and multiply by `(2*pi)⁻¹`. -/
def circleLogMean (F : ℂ → ℂ) (R : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ *
    ∫ t in Set.Ioc (0 : ℝ) (2 * Real.pi),
      Real.log ‖F ((R : ℂ) * Complex.exp (Complex.I * (t : ℂ)))‖

private theorem circleLogMean_eq_circleAverage (F : ℂ → ℂ) (R : ℝ) :
    circleLogMean F R = Real.circleAverage (fun z => Real.log ‖F z‖) 0 R := by
  rw [circleLogMean, Real.circleAverage_def,
    intervalIntegral.integral_of_le Real.two_pi_pos.le]
  simp only [smul_eq_mul]
  congr 2
  funext t
  congr 2
  simp [circleMap, mul_comm]

private theorem integral_radial_indicator (c n T R : ℝ)
    (hc : n = 0 → c = 0) (hn : 0 ≤ n) (hT : 0 < T) (hTR : T ≤ R) :
    (∫ t in T..R, if n < t then c * t⁻¹ else 0) =
      (if n < R then c * Real.log (R * n⁻¹) else 0) -
        (if n < T then c * Real.log (T * n⁻¹) else 0) := by
  have hR : 0 < R := hT.trans_le hTR
  have hinv : IntervalIntegrable (fun t : ℝ => t⁻¹) volume T R := by
    apply ContinuousOn.intervalIntegrable
    exact continuousOn_inv₀.mono (by
      intro t ht
      rw [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ne_of_gt (lt_of_lt_of_le hT (by simpa [Set.mem_uIcc, hTR] using ht.1)))
  by_cases hnT : n < T
  · have hnR : n < R := hnT.trans_le hTR
    by_cases hn0 : n = 0
    · subst n
      simp [hc rfl]
    have hnpos : 0 < n := lt_of_le_of_ne hn (Ne.symm hn0)
    rw [if_pos hnR, if_pos hnT]
    calc
      (∫ t in T..R, if n < t then c * t⁻¹ else 0) =
          ∫ t in T..R, c * t⁻¹ := by
            apply intervalIntegral.integral_congr
            intro t ht
            change (if n < t then c * t⁻¹ else 0) = c * t⁻¹
            rw [if_pos (hnT.trans_le (by simpa [Set.mem_uIcc, hTR] using ht.1))]
      _ = c * Real.log (R / T) := by
        rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hT hR]
      _ = c * Real.log (R * n⁻¹) - c * Real.log (T * n⁻¹) := by
        rw [Real.log_mul (ne_of_gt hR) (inv_ne_zero hn0),
          Real.log_mul (ne_of_gt hT) (inv_ne_zero hn0), Real.log_inv,
          Real.log_div (ne_of_gt hR) (ne_of_gt hT)]
        ring
  · have hTn : T ≤ n := le_of_not_gt hnT
    by_cases hnR : n < R
    · have hnpos : 0 < n := hT.trans_le hTn
      have hbelow : IntervalIntegrable
          ((Set.Iic n).indicator (fun t : ℝ => c * t⁻¹)) volume T R := by
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hTR]
        have hbase : IntegrableOn (fun t : ℝ => c * t⁻¹) (Set.Ioc T R) volume := by
          rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hTR]
          exact hinv.const_mul c
        exact hbase.indicator measurableSet_Iic
      rw [if_pos hnR, if_neg hnT]
      have hfun : (fun t : ℝ => if n < t then c * t⁻¹ else 0) =
          fun t => c * t⁻¹ - (Set.Iic n).indicator (fun s : ℝ => c * s⁻¹) t := by
        funext t
        by_cases ht : n < t
        · simp [Set.indicator, ht, not_le.mpr ht]
        · simp [Set.indicator, ht, le_of_not_gt ht]
      have hindicator :
          (∫ x in T..R, (Set.Iic n).indicator (fun t : ℝ => c * t⁻¹) x) =
            ∫ x in T..n, c * x⁻¹ := by
        exact intervalIntegral.integral_indicator ⟨hTn, hnR.le⟩
      rw [hfun, intervalIntegral.integral_sub (hinv.const_mul c) hbelow,
        hindicator,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        integral_inv_of_pos hT hR, integral_inv_of_pos hT hnpos]
      rw [Real.log_div (ne_of_gt hR) (ne_of_gt hT),
        Real.log_div (ne_of_gt hnpos) (ne_of_gt hT),
        Real.log_mul (ne_of_gt hR) (inv_ne_zero (ne_of_gt hnpos)), Real.log_inv]
      ring
    · have hRn : R ≤ n := le_of_not_gt hnR
      rw [if_neg hnR, if_neg hnT]
      simp only [sub_zero]
      apply intervalIntegral.integral_zero_ae
      filter_upwards with t
      intro ht
      rw [if_neg]
      have htR : t ≤ R := by simpa [Set.mem_uIoc, hTR] using ht.2
      exact not_lt_of_ge (htR.trans hRn)

private theorem intervalIntegrable_radial_indicator (c n T R : ℝ)
    (hT : 0 < T) (hTR : T ≤ R) :
    IntervalIntegrable (fun t : ℝ => if n < t then c * t⁻¹ else 0) volume T R := by
  have hinv : IntervalIntegrable (fun t : ℝ => t⁻¹) volume T R := by
    apply ContinuousOn.intervalIntegrable
    exact continuousOn_inv₀.mono (by
      intro t ht
      rw [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ne_of_gt (lt_of_lt_of_le hT (by simpa [Set.mem_uIcc, hTR] using ht.1)))
  by_cases hnT : n < T
  · apply (hinv.const_mul c).congr
    intro t ht
    change c * t⁻¹ = (if n < t then c * t⁻¹ else 0)
    rw [if_pos]
    exact hnT.trans_le (by simpa [Set.mem_uIoc, hTR] using ht.1.le)
  · by_cases hnR : n < R
    · have hTn : T ≤ n := le_of_not_gt hnT
      have hbelow : IntervalIntegrable
          ((Set.Iic n).indicator (fun t : ℝ => c * t⁻¹)) volume T R := by
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hTR]
        have hbase : IntegrableOn (fun t : ℝ => c * t⁻¹) (Set.Ioc T R) volume := by
          rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hTR]
          exact hinv.const_mul c
        exact hbase.indicator measurableSet_Iic
      have hsub := (hinv.const_mul c).sub hbelow
      apply hsub.congr
      intro t ht
      by_cases hnt : n < t
      · simp [Set.indicator, hnt, not_le.mpr hnt]
      · simp [Set.indicator, hnt, le_of_not_gt hnt]
    · apply (intervalIntegrable_const (c := (0 : ℝ))).congr
      intro t ht
      change 0 = (if n < t then c * t⁻¹ else 0)
      rw [if_neg]
      have htR : t ≤ R := by simpa [Set.mem_uIoc, hTR] using ht.2
      exact not_lt_of_ge (htR.trans (le_of_not_gt hnR))

private def radialCountSum (mult : ℂ → ℕ) (r : ℝ) : ℝ :=
  ∑ᶠ z : ℂ, if ‖z‖ < r then (mult z : ℝ) else 0

private def radialLogSum (mult : ℂ → ℕ) (R : ℝ) : ℝ :=
  ∑ᶠ z : ℂ, if ‖z‖ < R then
    (mult z : ℝ) * Real.log (R * ‖z‖⁻¹) else 0

private theorem radialLogSum_sub_eq_integral (mult : ℂ → ℕ)
    (hfinite : ∀ r : ℝ, Set.Finite ({z : ℂ | mult z ≠ 0} ∩ Metric.closedBall 0 r))
    (hmult0 : mult 0 = 0) {T R : ℝ} (hT : 0 < T) (hTR : T ≤ R) :
    radialLogSum mult R - radialLogSum mult T =
      ∫ t in T..R, radialCountSum mult t * t⁻¹ := by
  let s : Finset ℂ := (hfinite R).toFinset
  have hlogSupport (U : ℝ) (hUR : U ≤ R) :
      (fun z : ℂ => if ‖z‖ < U then
        (mult z : ℝ) * Real.log (U * ‖z‖⁻¹) else 0).support ⊆ s := by
    intro z hz
    simp only [Function.mem_support, ne_eq] at hz
    have hzu : ‖z‖ < U := by
      by_contra h
      apply hz
      simp [not_lt.mp h]
    have hmz : mult z ≠ 0 := by
      intro hm
      apply hz
      simp [hm]
    apply (Set.Finite.mem_toFinset _).2
    exact ⟨hmz, by
      simpa [Metric.mem_closedBall, dist_zero_right] using hzu.le.trans hUR⟩
  have hcountSupport (t : ℝ) (htR : t ≤ R) :
      (fun z : ℂ => if ‖z‖ < t then (mult z : ℝ) else 0).support ⊆ s := by
    intro z hz
    simp only [Function.mem_support, ne_eq] at hz
    have hzt : ‖z‖ < t := by
      by_contra h
      apply hz
      simp [not_lt.mp h]
    have hmz : mult z ≠ 0 := by
      intro hm
      apply hz
      simp [hm]
    apply (Set.Finite.mem_toFinset _).2
    exact ⟨hmz, by
      simpa [Metric.mem_closedBall, dist_zero_right] using hzt.le.trans htR⟩
  rw [radialLogSum, radialLogSum,
    finsum_eq_sum_of_support_subset _ (hlogSupport R le_rfl),
    finsum_eq_sum_of_support_subset _ (hlogSupport T hTR), ← Finset.sum_sub_distrib]
  calc
    ∑ z ∈ s,
        ((if ‖z‖ < R then (mult z : ℝ) * Real.log (R * ‖z‖⁻¹) else 0) -
          if ‖z‖ < T then (mult z : ℝ) * Real.log (T * ‖z‖⁻¹) else 0) =
        ∑ z ∈ s, ∫ t in T..R,
          if ‖z‖ < t then (mult z : ℝ) * t⁻¹ else 0 := by
      apply Finset.sum_congr rfl
      intro z hz
      symm
      apply integral_radial_indicator
      · intro hnorm
        have hz0 : z = 0 := norm_eq_zero.mp hnorm
        simp [hz0, hmult0]
      · exact norm_nonneg z
      · exact hT
      · exact hTR
    _ = ∫ t in T..R, ∑ z ∈ s,
          if ‖z‖ < t then (mult z : ℝ) * t⁻¹ else 0 := by
      rw [intervalIntegral.integral_finsetSum]
      intro z hz
      exact intervalIntegrable_radial_indicator (mult z : ℝ) ‖z‖ T R hT hTR
    _ = ∫ t in T..R, radialCountSum mult t * t⁻¹ := by
      apply intervalIntegral.integral_congr
      intro t ht
      have htR : t ≤ R := by simpa [Set.mem_uIcc, hTR] using ht.2
      change (∑ z ∈ s, if ‖z‖ < t then (mult z : ℝ) * t⁻¹ else 0) =
        (∑ᶠ z : ℂ, if ‖z‖ < t then (mult z : ℝ) else 0) * t⁻¹
      rw [finsum_eq_sum_of_support_subset _ (hcountSupport t htR),
        Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro z hz
      by_cases hzt : ‖z‖ < t <;> simp [hzt]

private def zeroLogSum {F : ℂ → ℂ} (data : MeromorphicCountingData F) (R : ℝ) : ℝ :=
  radialLogSum (fun z => (data.order z).toNat) R

private def poleLogSum {F : ℂ → ℂ} (data : MeromorphicCountingData F) (R : ℝ) : ℝ :=
  radialLogSum (fun z => (-data.order z).toNat) R

private theorem zeroCount_eq_finsum {F : ℂ → ℂ} (data : MeromorphicCountingData F)
    {r : ℝ} (hr : 0 < r) :
    (zeroCount data r : ℝ) =
      radialCountSum (fun z => (data.order z).toNat) r := by
  rw [zeroCount, if_neg (not_le.mpr hr)]
  push_cast
  rw [radialCountSum]
  rw [finsum_eq_sum_of_support_subset
    (s := (data.finite_orderSupport_closedBall r).toFinset)]
  intro z hz
  simp only [Function.mem_support, ne_eq] at hz
  apply (Set.Finite.mem_toFinset _).2
  have hlt : ‖z‖ < r := by
    by_contra h
    apply hz
    simp [not_lt.mp h]
  constructor
  · intro hzero
    apply hz
    simp [hzero]
  · simpa [Metric.mem_closedBall, dist_zero_right] using hlt.le

private theorem poleCount_eq_finsum {F : ℂ → ℂ} (data : MeromorphicCountingData F)
    {r : ℝ} (hr : 0 < r) :
    (poleCount data r : ℝ) =
      radialCountSum (fun z => (-data.order z).toNat) r := by
  rw [poleCount, if_neg (not_le.mpr hr)]
  push_cast
  rw [radialCountSum]
  rw [finsum_eq_sum_of_support_subset
    (s := (data.finite_orderSupport_closedBall r).toFinset)]
  intro z hz
  simp only [Function.mem_support, ne_eq] at hz
  apply (Set.Finite.mem_toFinset _).2
  have hlt : ‖z‖ < r := by
    by_contra h
    apply hz
    simp [not_lt.mp h]
  constructor
  · intro hzero
    apply hz
    simp [hzero]
  · simpa [Metric.mem_closedBall, dist_zero_right] using hlt.le

private theorem counting_order_zero {F : ℂ → ℂ} (data : MeromorphicCountingData F)
    (hF0analytic : AnalyticAt ℂ F 0) (hF0 : F 0 ≠ 0) : data.order 0 = 0 := by
  have hmer : meromorphicOrderAt F 0 = (0 : WithTop ℤ) := by
    rw [hF0analytic.meromorphicOrderAt_eq,
      (hF0analytic.analyticOrderAt_eq_zero).2 hF0]
    simp
  have hs := data.order_spec 0
  rw [hmer] at hs
  exact_mod_cast hs

private theorem zeroLogSum_sub_eq_integral {F : ℂ → ℂ} (data : MeromorphicCountingData F)
    (horder0 : data.order 0 = 0) {T R : ℝ} (hT : 0 < T) (hTR : T ≤ R) :
    zeroLogSum data R - zeroLogSum data T =
      ∫ t in T..R, (zeroCount data t : ℝ) * t⁻¹ := by
  have hfinite : ∀ r : ℝ, Set.Finite
      ({z : ℂ | (data.order z).toNat ≠ 0} ∩ Metric.closedBall 0 r) := by
    intro r
    apply (data.finite_orderSupport_closedBall r).subset
    intro z hz
    exact ⟨by
      intro hord
      apply hz.1
      simp [hord], hz.2⟩
  change radialLogSum (fun z => (data.order z).toNat) R -
      radialLogSum (fun z => (data.order z).toNat) T = _
  rw [radialLogSum_sub_eq_integral _ hfinite (by simp [horder0]) hT hTR]
  apply intervalIntegral.integral_congr
  intro t ht
  have htpos : 0 < t := hT.trans_le (by
    simpa [Set.mem_uIcc, hTR] using ht.1)
  change radialCountSum (fun z => (data.order z).toNat) t * t⁻¹ =
    (zeroCount data t : ℝ) * t⁻¹
  rw [zeroCount_eq_finsum data htpos]

private theorem poleLogSum_sub_eq_integral {F : ℂ → ℂ} (data : MeromorphicCountingData F)
    (horder0 : data.order 0 = 0) {T R : ℝ} (hT : 0 < T) (hTR : T ≤ R) :
    poleLogSum data R - poleLogSum data T =
      ∫ t in T..R, (poleCount data t : ℝ) * t⁻¹ := by
  have hfinite : ∀ r : ℝ, Set.Finite
      ({z : ℂ | (-data.order z).toNat ≠ 0} ∩ Metric.closedBall 0 r) := by
    intro r
    apply (data.finite_orderSupport_closedBall r).subset
    intro z hz
    exact ⟨by
      intro hord
      apply hz.1
      simp [hord], hz.2⟩
  change radialLogSum (fun z => (-data.order z).toNat) R -
      radialLogSum (fun z => (-data.order z).toNat) T = _
  rw [radialLogSum_sub_eq_integral _ hfinite (by simp [horder0]) hT hTR]
  apply intervalIntegral.integral_congr
  intro t ht
  have htpos : 0 < t := hT.trans_le (by
    simpa [Set.mem_uIcc, hTR] using ht.1)
  change radialCountSum (fun z => (-data.order z).toNat) t * t⁻¹ =
    (poleCount data t : ℝ) * t⁻¹
  rw [poleCount_eq_finsum data htpos]

private theorem counting_order_eq_zero_of_analytic_ne {F : ℂ → ℂ}
    (data : MeromorphicCountingData F) {z : ℂ} (hzAnalytic : AnalyticAt ℂ F z)
    (hz : F z ≠ 0) : data.order z = 0 := by
  have hmer : meromorphicOrderAt F z = (0 : WithTop ℤ) := by
    rw [hzAnalytic.meromorphicOrderAt_eq, (hzAnalytic.analyticOrderAt_eq_zero).2 hz]
    simp
  have hs := data.order_spec z
  rw [hmer] at hs
  exact_mod_cast hs

private theorem divisor_eq_counting_order {F : ℂ → ℂ}
    (data : MeromorphicCountingData F) (z : ℂ) :
    divisor F Set.univ z = data.order z := by
  rw [data.meromorphicOn_univ.divisor_apply (Set.mem_univ z)]
  rw [← data.order_spec z]
  exact WithTop.untop₀_coe _

private theorem logCounting_eq_zeroLog_sub_poleLog {F : ℂ → ℂ}
    (data : MeromorphicCountingData F) (horder0 : data.order 0 = 0)
    {R : ℝ} (hR : 0 < R)
    (hclean : ∀ z, ‖z‖ = R → AnalyticAt ℂ F z ∧ F z ≠ 0) :
    Function.locallyFinsuppWithin.logCounting (divisor F Set.univ) R =
      zeroLogSum data R - poleLogSum data R := by
  have hzeroFinite : Function.HasFiniteSupport (fun z : ℂ =>
      if ‖z‖ < R then (data.order z).toNat * Real.log (R * ‖z‖⁻¹) else 0) := by
    apply (data.finite_orderSupport_closedBall R).subset
    intro z hz
    simp only [Function.mem_support, ne_eq] at hz
    have hlt : ‖z‖ < R := by
      by_contra h
      apply hz
      simp [not_lt.mp h]
    exact ⟨by
      intro hord
      apply hz
      simp [hord], by
        simpa [Metric.mem_closedBall, dist_zero_right] using hlt.le⟩
  have hpoleFinite : Function.HasFiniteSupport (fun z : ℂ =>
      if ‖z‖ < R then (-data.order z).toNat * Real.log (R * ‖z‖⁻¹) else 0) := by
    apply (data.finite_orderSupport_closedBall R).subset
    intro z hz
    simp only [Function.mem_support, ne_eq] at hz
    have hlt : ‖z‖ < R := by
      by_contra h
      apply hz
      simp [not_lt.mp h]
    exact ⟨by
      intro hord
      apply hz
      simp [hord], by
        simpa [Metric.mem_closedBall, dist_zero_right] using hlt.le⟩
  rw [Function.locallyFinsuppWithin.logCounting]
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [divisor_eq_counting_order data 0, horder0]
  simp only [Int.cast_zero, zero_mul, add_zero, zeroLogSum, poleLogSum, radialLogSum]
  rw [← finsum_sub_distrib hzeroFinite hpoleFinite]
  apply finsum_congr
  intro z
  have hdiv := divisor_eq_counting_order data z
  by_cases hzR : ‖z‖ < R
  · rw [if_pos hzR, if_pos hzR]
    rw [Function.locallyFinsuppWithin.toClosedBall_eval_within]
    · rw [hdiv]
      have hcast : (data.order z : ℝ) =
          ((data.order z).toNat : ℝ) - ((-data.order z).toNat : ℝ) := by
        exact_mod_cast (Int.toNat_sub_toNat_neg (data.order z)).symm
      rw [hcast]
      ring
    · simpa [abs_of_pos hR, Metric.mem_closedBall, dist_zero_right] using hzR.le
  · rw [if_neg hzR, if_neg hzR, sub_zero]
    by_cases hzEq : ‖z‖ = R
    · have hord : data.order z = 0 :=
        counting_order_eq_zero_of_analytic_ne data (hclean z hzEq).1 (hclean z hzEq).2
      rw [Function.locallyFinsuppWithin.toClosedBall_eval_within]
      · rw [hdiv, hord]
        simp
      · simpa [abs_of_pos hR, Metric.mem_closedBall, dist_zero_right, hzEq]
    · have hzout : z ∉ Metric.closedBall (0 : ℂ) |R| := by
        simp only [Metric.mem_closedBall, dist_zero_right, abs_of_pos hR, not_le]
        exact lt_of_le_of_ne (le_of_not_gt hzR) (Ne.symm hzEq)
      simp [Function.locallyFinsuppWithin.toClosedBall, hzout]

private theorem circleLogMean_jensen {F : ℂ → ℂ} (data : MeromorphicCountingData F)
    (hF0analytic : AnalyticAt ℂ F 0) (hF0 : F 0 ≠ 0)
    {R : ℝ} (hR : 0 < R)
    (hclean : ∀ z, ‖z‖ = R → AnalyticAt ℂ F z ∧ F z ≠ 0) :
    circleLogMean F R =
      zeroLogSum data R - poleLogSum data R + Real.log ‖F 0‖ := by
  have horder0 := counting_order_zero data hF0analytic hF0
  have hj := Function.locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_const
    (meromorphicOn_univ.mp data.meromorphicOn_univ) hR.ne'
  rw [logCounting_eq_zeroLog_sub_poleLog data horder0 hR hclean,
    ← circleLogMean_eq_circleAverage F R,
    hF0analytic.meromorphicTrailingCoeffAt_of_ne_zero hF0] at hj
  linarith

private theorem intervalIntegrable_radialCountSum (mult : ℂ → ℕ)
    (hfinite : ∀ r : ℝ, Set.Finite ({z : ℂ | mult z ≠ 0} ∩ Metric.closedBall 0 r))
    {T R : ℝ} (hT : 0 < T) (hTR : T ≤ R) :
    IntervalIntegrable (fun t => radialCountSum mult t * t⁻¹) volume T R := by
  let s : Finset ℂ := (hfinite R).toFinset
  have hcountSupport (t : ℝ) (htR : t ≤ R) :
      (fun z : ℂ => if ‖z‖ < t then (mult z : ℝ) else 0).support ⊆ s := by
    intro z hz
    simp only [Function.mem_support, ne_eq] at hz
    have hzt : ‖z‖ < t := by
      by_contra h
      apply hz
      simp [not_lt.mp h]
    have hmz : mult z ≠ 0 := by
      intro hm
      apply hz
      simp [hm]
    apply (Set.Finite.mem_toFinset _).2
    exact ⟨hmz, by
      simpa [Metric.mem_closedBall, dist_zero_right] using hzt.le.trans htR⟩
  have hsum : IntervalIntegrable (fun t => ∑ z ∈ s,
      if ‖z‖ < t then (mult z : ℝ) * t⁻¹ else 0) volume T R := by
    apply (IntervalIntegrable.sum s (fun z hz =>
      intervalIntegrable_radial_indicator (mult z : ℝ) ‖z‖ T R hT hTR)).congr
    intro t ht
    simp only [Finset.sum_apply]
  apply hsum.congr
  intro t ht
  have htR : t ≤ R := by simpa [Set.mem_uIoc, hTR] using ht.2
  change (∑ z ∈ s, if ‖z‖ < t then (mult z : ℝ) * t⁻¹ else 0) =
    radialCountSum mult t * t⁻¹
  rw [radialCountSum, finsum_eq_sum_of_support_subset _ (hcountSupport t htR),
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hzt : ‖z‖ < t <;> simp [hzt]

private theorem intervalIntegrable_zeroCount {F : ℂ → ℂ}
    (data : MeromorphicCountingData F) {T R : ℝ} (hT : 0 < T) (hTR : T ≤ R) :
    IntervalIntegrable (fun t => (zeroCount data t : ℝ) * t⁻¹) volume T R := by
  have hfinite : ∀ r : ℝ, Set.Finite
      ({z : ℂ | (data.order z).toNat ≠ 0} ∩ Metric.closedBall 0 r) := by
    intro r
    apply (data.finite_orderSupport_closedBall r).subset
    intro z hz
    exact ⟨by
      intro hord
      apply hz.1
      simp [hord], hz.2⟩
  have hradial := intervalIntegrable_radialCountSum
    (fun z => (data.order z).toNat) hfinite hT hTR
  apply hradial.congr
  intro t ht
  have htpos : 0 < t := hT.trans (by simpa [Set.mem_uIoc, hTR] using ht.1)
  change radialCountSum (fun z => (data.order z).toNat) t * t⁻¹ =
    (zeroCount data t : ℝ) * t⁻¹
  rw [zeroCount_eq_finsum data htpos]

private theorem intervalIntegrable_poleCount {F : ℂ → ℂ}
    (data : MeromorphicCountingData F) {T R : ℝ} (hT : 0 < T) (hTR : T ≤ R) :
    IntervalIntegrable (fun t => (poleCount data t : ℝ) * t⁻¹) volume T R := by
  have hfinite : ∀ r : ℝ, Set.Finite
      ({z : ℂ | (-data.order z).toNat ≠ 0} ∩ Metric.closedBall 0 r) := by
    intro r
    apply (data.finite_orderSupport_closedBall r).subset
    intro z hz
    exact ⟨by
      intro hord
      apply hz.1
      simp [hord], hz.2⟩
  have hradial := intervalIntegrable_radialCountSum
    (fun z => (-data.order z).toNat) hfinite hT hTR
  apply hradial.congr
  intro t ht
  have htpos : 0 < t := hT.trans (by simpa [Set.mem_uIoc, hTR] using ht.1)
  change radialCountSum (fun z => (-data.order z).toNat) t * t⁻¹ =
    (poleCount data t : ℝ) * t⁻¹
  rw [poleCount_eq_finsum data htpos]

/- Proof idea: thin representation adapter to the proved Jensen theorem,
changing only proved-equivalent divisor-count, clean-radius, filter, and circle-normalization forms. -/
theorem jensen_density_comparison (F : ℂ → ℂ) (data : MeromorphicCountingData F)
    (hF0analytic : AnalyticAt ℂ F 0) (hF0 : F 0 ≠ 0)
    (R : ℕ → ℝ) (hRpos : ∀ m, 0 < R m) (hRtendsto : Tendsto R atTop atTop)
    (hclean : ∀ m z, ‖z‖ = R m → AnalyticAt ℂ F z ∧ F z ≠ 0)
    (sigma rho tau : ℝ) (b : ℕ → ℝ)
    (hb : Tendsto (fun m => b m / R m) atTop (nhds 0))
    (hboundary : ∀ᶠ m in atTop,
      circleLogMean F (R m) ≤ 2 * tau * R m + b m)
    (hzero : ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ r : ℝ in atTop,
      2 * (sigma - epsilon) * r ≤ (zeroCount data r : ℝ))
    (hpole : ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ r : ℝ in atTop,
      (poleCount data r : ℝ) ≤ 2 * (rho + epsilon) * r) :
    sigma ≤ rho + tau := by
  have horder0 := counting_order_zero data hF0analytic hF0
  have hepsilon : ∀ epsilon : ℝ, 0 < epsilon →
      sigma - rho - 2 * epsilon ≤ tau := by
    intro epsilon hepsilon
    obtain ⟨Tz, hTz⟩ := (eventually_atTop.1 (hzero epsilon hepsilon))
    obtain ⟨Tp, hTp⟩ := (eventually_atTop.1 (hpole epsilon hepsilon))
    let T : ℝ := max 1 (max Tz Tp)
    have hT : 0 < T := lt_of_lt_of_le zero_lt_one (le_max_left 1 (max Tz Tp))
    have hTzT : Tz ≤ T :=
      (le_max_left Tz Tp).trans (le_max_right 1 (max Tz Tp))
    have hTpT : Tp ≤ T :=
      (le_max_right Tz Tp).trans (le_max_right 1 (max Tz Tp))
    have hzlarge : ∀ t : ℝ, T ≤ t →
        2 * (sigma - epsilon) * t ≤ (zeroCount data t : ℝ) := by
      intro t ht
      exact hTz t (hTzT.trans ht)
    have hplarge : ∀ t : ℝ, T ≤ t →
        (poleCount data t : ℝ) ≤ 2 * (rho + epsilon) * t := by
      intro t ht
      exact hTp t (hTpT.trans ht)
    let C : ℝ := -Real.log ‖F 0‖ - zeroLogSum data T + poleLogSum data T
    have hRm : ∀ᶠ m in atTop, T ≤ R m :=
      hRtendsto.eventually (eventually_ge_atTop T)
    have hcomparison : ∀ᶠ m in atTop,
        2 * (sigma - rho - 2 * epsilon) * (1 - T / R m) ≤
          2 * tau + b m / R m + C / R m := by
      filter_upwards [hRm, hboundary] with m hTRm hbm
      have hzeroInt : 2 * (sigma - epsilon) * (R m - T) ≤
          zeroLogSum data (R m) - zeroLogSum data T := by
        rw [zeroLogSum_sub_eq_integral data horder0 hT hTRm]
        calc
          2 * (sigma - epsilon) * (R m - T) =
              ∫ _t in T..R m, 2 * (sigma - epsilon) := by
            simp only [intervalIntegral.integral_const, smul_eq_mul]
            ring
          _ ≤ ∫ t in T..R m, (zeroCount data t : ℝ) * t⁻¹ := by
            apply intervalIntegral.integral_mono_on hTRm intervalIntegrable_const
              (intervalIntegrable_zeroCount data hT hTRm)
            intro t ht
            have htpos : 0 < t := hT.trans_le ht.1
            calc
              2 * (sigma - epsilon) =
                  (2 * (sigma - epsilon) * t) * t⁻¹ := by
                field_simp
              _ ≤ (zeroCount data t : ℝ) * t⁻¹ :=
                mul_le_mul_of_nonneg_right (hzlarge t ht.1) (inv_nonneg.mpr htpos.le)
      have hpoleInt : poleLogSum data (R m) - poleLogSum data T ≤
          2 * (rho + epsilon) * (R m - T) := by
        rw [poleLogSum_sub_eq_integral data horder0 hT hTRm]
        calc
          (∫ t in T..R m, (poleCount data t : ℝ) * t⁻¹) ≤
              ∫ _t in T..R m, 2 * (rho + epsilon) := by
            apply intervalIntegral.integral_mono_on hTRm
              (intervalIntegrable_poleCount data hT hTRm) intervalIntegrable_const
            intro t ht
            have htpos : 0 < t := hT.trans_le ht.1
            calc
              (poleCount data t : ℝ) * t⁻¹ ≤
                  (2 * (rho + epsilon) * t) * t⁻¹ :=
                mul_le_mul_of_nonneg_right (hplarge t ht.1) (inv_nonneg.mpr htpos.le)
              _ = 2 * (rho + epsilon) := by field_simp
          _ = 2 * (rho + epsilon) * (R m - T) := by
            simp only [intervalIntegral.integral_const, smul_eq_mul]
            ring
      have hjensen := circleLogMean_jensen data hF0analytic hF0 (hRpos m) (hclean m)
      have hsigned : zeroLogSum data (R m) - poleLogSum data (R m) ≤
          2 * tau * R m + b m - Real.log ‖F 0‖ := by
        linarith
      have hraw : 2 * (sigma - rho - 2 * epsilon) * (R m - T) ≤
          2 * tau * R m + b m + C := by
        dsimp only [C]
        linarith
      have hRmpos := hRpos m
      calc
        2 * (sigma - rho - 2 * epsilon) * (1 - T / R m) =
            (2 * (sigma - rho - 2 * epsilon) * (R m - T)) / R m := by
          field_simp
        _ ≤ (2 * tau * R m + b m + C) / R m :=
          div_le_div_of_nonneg_right hraw hRmpos.le
        _ = 2 * tau + b m / R m + C / R m := by
          field_simp
    have hTdiv : Tendsto (fun m => T / R m) atTop (nhds 0) :=
      hRtendsto.const_div_atTop T
    have hCdiv : Tendsto (fun m => C / R m) atTop (nhds 0) :=
      hRtendsto.const_div_atTop C
    have hleft : Tendsto
        (fun m => 2 * (sigma - rho - 2 * epsilon) * (1 - T / R m)) atTop
        (nhds (2 * (sigma - rho - 2 * epsilon))) := by
      have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
      simpa using (hone.sub hTdiv).const_mul
        (2 * (sigma - rho - 2 * epsilon))
    have hright : Tendsto
        (fun m => 2 * tau + b m / R m + C / R m) atTop (nhds (2 * tau)) := by
      simpa using (tendsto_const_nhds.add hb).add hCdiv
    have hlimit : 2 * (sigma - rho - 2 * epsilon) ≤ 2 * tau :=
      le_of_tendsto_of_tendsto hleft hright hcomparison
    linarith
  by_contra h
  have hgap : 0 < sigma - (rho + tau) := sub_pos.mpr (lt_of_not_ge h)
  have hfinal := hepsilon ((sigma - (rho + tau)) / 4) (by positivity)
  linarith

end Theorem12.Generic
