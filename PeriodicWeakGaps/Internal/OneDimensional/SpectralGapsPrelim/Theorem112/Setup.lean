import SpectralGapsPrelim.Theorem112.Definitions

noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform SchwartzMap

namespace SpectralGapsPrelim.Theorem112

/-!
Setup lemmas for the one-dimensional nonuniqueness proof.
-/

theorem AContext.finite_volume {A : Set ℝ} (hA : AContext A) : volume A < ∞ := by
  -- Proof idea: use `hA.subset_Icc` and finite volume of `[0,1]`.
  exact
    lt_of_le_of_lt (measure_mono hA.subset_Icc)
      (measure_Icc_lt_top (a := (0 : ℝ)) (b := 1) (μ := volume))

theorem AContext.measurableSet_spectrum {A : Set ℝ} (hA : AContext A) :
    MeasurableSet (spectrum A) := by
  -- Proof idea: express `spectrum A` as a countable union of integer
  -- translates of `A`, then use measurability of translations.
  change MeasurableSet {xi | ∃ k : ℤ, xi ∈ intTranslate A k}
  convert MeasurableSet.iUnion (fun k : ℤ =>
    hA.measurable.preimage
      ((continuous_id.sub (continuous_const : Continuous fun _ : ℝ => (k : ℝ))).measurable)) using 1
  ext xi
  simp [intTranslate]

theorem spectrum_eq_iUnion_intTranslate (A : Set ℝ) :
    spectrum A = ⋃ k : ℤ, intTranslate A k := by
  -- Proof idea: unfold `spectrum` and `intTranslate`; both sides express
  -- membership as belonging to one integer translate of `A`.
  ext xi
  simp [spectrum]

theorem measurableSet_intTranslate {A : Set ℝ}
    (hA : MeasurableSet A) (k : ℤ) :
    MeasurableSet (intTranslate A k) := by
  -- Proof idea: `intTranslate A k` is the preimage of `A` under the
  -- continuous map `xi ↦ xi - k`.
  change MeasurableSet ((fun xi : ℝ => xi - (k : ℝ)) ⁻¹' A)
  exact hA.preimage ((continuous_id.sub continuous_const).measurable)

theorem integerObstructionSet_finite {K : Set ℝ} {y : ℝ}
    (hK : IsCompact K) :
    (integerObstructionSet K y).Finite := by
  -- Proof idea: `(K - y) ∩ ℤ` is bounded by compactness of `K` and
  -- discrete because it is a subset of the integer lattice.
  let T : Set ℤ := {z | ((z : ℝ) + y) ∈ K}
  have hT_compact : IsCompact T := by
    have hKpre : IsCompact ((Homeomorph.addRight y : ℝ ≃ₜ ℝ) ⁻¹' K) :=
      (Homeomorph.addRight y : ℝ ≃ₜ ℝ).isCompact_preimage.mpr hK
    change IsCompact ((fun z : ℤ => ((z : ℝ) + y)) ⁻¹' K)
    simpa [Set.preimage_preimage, Homeomorph.coe_addRight] using
      (Int.isClosedEmbedding_coe_real.isCompact_preimage hKpre)
  have hT_finite : T.Finite := hT_compact.finite_of_discrete
  refine (hT_finite.image fun z : ℤ => (z : ℝ)).subset ?_
  intro d hd
  rw [integerObstructionSet] at hd
  rcases hd.1 with ⟨z, rfl⟩
  exact ⟨z, hd.2, rfl⟩

noncomputable def integerObstructions
    (K : Set ℝ) (y : ℝ) (hK : IsCompact K) : FiniteSet ℝ :=
  integerObstructionsOfFinite K y (integerObstructionSet_finite hK)

theorem zero_not_mem_integerObstructionSet {K : Set ℝ} {y : ℝ}
    (hyK : y ∉ K) :
    0 ∉ integerObstructionSet K y := by
  -- Proof idea: if `0` were an obstruction, then `0 + y ∈ K`.
  intro h
  exact hyK (by simpa [integerObstructionSet] using h.2)

theorem mem_spectrum_of_mem_translate {A : Set ℝ} {t : ℝ}
    (ht : t ∈ A) (k : ℤ) :
    t + (k : ℝ) ∈ spectrum A := by
  -- Proof idea: use the integer translate indexed by `k`; after
  -- rewriting `(t + k) - k = t`, the claim is exactly `ht`.
  refine ⟨k, ?_⟩
  simpa [intTranslate, add_sub_cancel_right] using ht

theorem ae_disjoint_int_translates {A : Set ℝ}
    (hA_sub : A ⊆ Set.Icc 0 1)
    {k l : ℤ} (hkl : k ≠ l) :
    volume (intTranslate A k ∩ intTranslate A l) = 0 := by
  -- Proof idea: if a point lies in both translates, then two points of
  -- `A ⊆ [0,1]` differ by the nonzero integer `k-l`; the intersection is
  -- therefore contained in an endpoint fibre, hence null.
  refine measure_mono_null ?_
    (((Set.finite_singleton (a := (k : ℝ))).union
      (Set.finite_singleton (a := (l : ℝ)))).measure_zero volume)
  intro x hx
  show x ∈ ({(k : ℝ)} ∪ {(l : ℝ)} : Set ℝ)
  simp only [Set.mem_union, Set.mem_singleton_iff]
  have hxkA : x - (k : ℝ) ∈ A := hx.1
  have hxlA : x - (l : ℝ) ∈ A := hx.2
  have hxkI : x - (k : ℝ) ∈ Set.Icc (0 : ℝ) 1 := hA_sub hxkA
  have hxlI : x - (l : ℝ) ∈ Set.Icc (0 : ℝ) 1 := hA_sub hxlA
  have hx_le_k1 : x ≤ (k : ℝ) + 1 := by linarith [hxkI.2]
  have hl_le_x : (l : ℝ) ≤ x := by linarith [hxlI.1]
  have hx_le_l1 : x ≤ (l : ℝ) + 1 := by linarith [hxlI.2]
  have hk_le_x : (k : ℝ) ≤ x := by linarith [hxkI.1]
  rcases lt_or_gt_of_ne hkl with hlt | hgt
  · have hkl_succ : k + 1 ≤ l := Int.add_one_le_iff.mpr hlt
    have hkl_real : (k : ℝ) + 1 ≤ (l : ℝ) := by exact_mod_cast hkl_succ
    right
    linarith
  · have hlk_succ : l + 1 ≤ k := Int.add_one_le_iff.mpr hgt
    have hlk_real : (l : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hlk_succ
    left
    linarith

theorem PhiZeroExt_eq_of_mem {A : Set ℝ} {Phi : ℝ → ℂ} {t : ℝ}
    (ht : t ∈ A) :
    PhiZeroExt A Phi t = Phi t := by
  -- Proof idea: unfold `PhiZeroExt` and use the indicator value on `A`.
  simpa [PhiZeroExt] using Set.indicator_of_mem ht Phi

theorem PhiZeroExt_eq_zero_of_not_mem {A : Set ℝ} {Phi : ℝ → ℂ} {t : ℝ}
    (ht : t ∉ A) :
    PhiZeroExt A Phi t = 0 := by
  -- Proof idea: unfold `PhiZeroExt` and use the indicator value off `A`.
  simpa [PhiZeroExt] using Set.indicator_of_notMem ht Phi

private lemma sobolevPower_nonneg (alpha xi : ℝ) :
    0 ≤ sobolevPower alpha xi := by
  unfold sobolevPower
  split_ifs
  · norm_num
  · positivity

lemma one_le_sobolevWeight (alpha xi : ℝ) :
    1 ≤ sobolevWeight alpha xi := by
  -- Proof idea: `sobolevWeight = 1 + nonnegative term`.
  unfold sobolevWeight
  linarith [sobolevPower_nonneg alpha xi]

lemma sobolevWeight_nonneg (alpha xi : ℝ) :
    0 ≤ sobolevWeight alpha xi := by
  -- Proof idea: combine `one_le_sobolevWeight` with `0 ≤ 1`.
  linarith [one_le_sobolevWeight alpha xi]

private lemma aestronglyMeasurable_abs_rpow
    (q : ℝ) (μ : Measure ℝ) :
    AEStronglyMeasurable (fun xi : ℝ => |xi| ^ q) μ := by
  refine (measurable_of_continuousOn_compl_singleton (0 : ℝ) ?_).aestronglyMeasurable
  intro x hx
  exact
    (continuousAt_id.abs.rpow_const
      (Or.inl (by simpa using abs_ne_zero.mpr hx))).continuousWithinAt

private lemma aestronglyMeasurable_sobolevWeight
    (alpha : ℝ) (μ : Measure ℝ) :
    AEStronglyMeasurable (fun xi : ℝ => sobolevWeight alpha xi) μ := by
  unfold sobolevWeight sobolevPower
  split_ifs with halpha
  · fun_prop
  · exact aestronglyMeasurable_const.add (aestronglyMeasurable_abs_rpow (2 * alpha) μ)

lemma weightedEnergy_nonneg (alpha : ℝ) (A : Set ℝ) (P : ℝ → ℂ) :
    0 ≤ weightedEnergy alpha A P := by
  -- Proof idea: prove the integrand is nonnegative from
  -- `sobolevWeight_nonneg` and `sq_nonneg`, then apply integral nonnegativity.
  unfold weightedEnergy
  exact integral_nonneg fun xi =>
    mul_nonneg (sobolevWeight_nonneg alpha xi) (sq_nonneg ‖P xi‖)

lemma weightedNorm_nonneg (alpha : ℝ) (A : Set ℝ) (P : ℝ → ℂ) :
    0 ≤ weightedNorm alpha A P := by
  -- Proof idea: unfold `weightedNorm` and use nonnegativity of `Real.sqrt`.
  simp [weightedNorm]

theorem WeightedEnergyIntegrable.smul
    {A : Set ℝ} {alpha : ℝ} {P : ℝ → ℂ}
    (z : ℂ) (hP : WeightedEnergyIntegrable alpha A P) :
    WeightedEnergyIntegrable alpha A (fun xi => z * P xi) := by
  -- Proof idea: scalar multiplication pulls out as the constant `‖z‖^2`
  -- from the weighted-energy integrand.
  unfold WeightedEnergyIntegrable at hP ⊢
  convert hP.const_mul (‖z‖ ^ 2) using 1
  ext xi
  rw [norm_mul]
  ring

theorem WeightedEnergyIntegrable.add
    {A : Set ℝ} {alpha : ℝ} {P Q : ℝ → ℂ}
    (hP_meas : AEStronglyMeasurable P (volume.restrict (spectrum A)))
    (hQ_meas : AEStronglyMeasurable Q (volume.restrict (spectrum A)))
    (hP : WeightedEnergyIntegrable alpha A P)
    (hQ : WeightedEnergyIntegrable alpha A Q) :
    WeightedEnergyIntegrable alpha A (fun xi => P xi + Q xi) := by
  -- Proof idea: use `‖P + Q‖^2 ≤ 2 * (‖P‖^2 + ‖Q‖^2)` and the
  -- integrability of the two weighted square functions.
  unfold WeightedEnergyIntegrable at hP hQ ⊢
  let μ := volume.restrict (spectrum A)
  let eP : ℝ → ℝ := fun xi => sobolevWeight alpha xi * ‖P xi‖ ^ 2
  let eQ : ℝ → ℝ := fun xi => sobolevWeight alpha xi * ‖Q xi‖ ^ 2
  have hdom_int : Integrable (fun xi => 2 * (eP xi + eQ xi)) μ := by
    exact (hP.add hQ).const_mul 2
  refine hdom_int.mono_nonneg ?_ ?_ ?_
  · exact
      (aestronglyMeasurable_sobolevWeight alpha μ).mul
        ((hP_meas.add hQ_meas).norm.pow 2)
  · exact Filter.Eventually.of_forall fun xi =>
      mul_nonneg (sobolevWeight_nonneg alpha xi) (sq_nonneg ‖P xi + Q xi‖)
  · exact Filter.Eventually.of_forall fun xi => by
      have hw : 0 ≤ sobolevWeight alpha xi := sobolevWeight_nonneg alpha xi
      have hnorm : ‖P xi + Q xi‖ ≤ ‖P xi‖ + ‖Q xi‖ := norm_add_le (P xi) (Q xi)
      have hsq :
          ‖P xi + Q xi‖ ^ 2 ≤ 2 * (‖P xi‖ ^ 2 + ‖Q xi‖ ^ 2) := by
        nlinarith [sq_nonneg (‖P xi‖ - ‖Q xi‖), norm_nonneg (P xi),
          norm_nonneg (Q xi), norm_nonneg (P xi + Q xi), hnorm]
      dsimp [eP, eQ]
      nlinarith

theorem WeightedEnergyIntegrable.neg
    {A : Set ℝ} {alpha : ℝ} {P : ℝ → ℂ}
    (hP : WeightedEnergyIntegrable alpha A P) :
    WeightedEnergyIntegrable alpha A (fun xi => -P xi) := by
  -- Proof idea: the weighted square norm is unchanged by negation.
  simpa [WeightedEnergyIntegrable] using hP

theorem WeightedEnergyIntegrable.sub
    {A : Set ℝ} {alpha : ℝ} {P Q : ℝ → ℂ}
    (hP_meas : AEStronglyMeasurable P (volume.restrict (spectrum A)))
    (hQ_meas : AEStronglyMeasurable Q (volume.restrict (spectrum A)))
    (hP : WeightedEnergyIntegrable alpha A P)
    (hQ : WeightedEnergyIntegrable alpha A Q) :
    WeightedEnergyIntegrable alpha A (fun xi => P xi - Q xi) := by
  -- Proof idea: rewrite subtraction as addition with `-Q` and use the
  -- preceding closure lemmas.
  simpa [sub_eq_add_neg] using
    WeightedEnergyIntegrable.add hP_meas (by fun_prop) hP
      (WeightedEnergyIntegrable.neg hQ)

theorem WeightedEnergyIntegrable.finset_sum
    {ι : Type*} {A : Set ℝ} {alpha : ℝ}
    {s : Finset ι} {F : ι → ℝ → ℂ}
    (hF_meas : ∀ i ∈ s, AEStronglyMeasurable (F i) (volume.restrict (spectrum A)))
    (hF : ∀ i ∈ s, WeightedEnergyIntegrable alpha A (F i)) :
    WeightedEnergyIntegrable alpha A
      (fun xi => s.sum (fun i => F i xi)) := by
  -- Proof idea: induct on the finite set using additive closure.
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [WeightedEnergyIntegrable]
  | insert a s ha ih =>
      have hsum_meas :
          AEStronglyMeasurable (fun xi => s.sum (fun i => F i xi))
            (volume.restrict (spectrum A)) :=
        Finset.aestronglyMeasurable_fun_sum s fun i hi => hF_meas i (by simp [hi])
      simpa [Finset.sum_insert, ha] using
        WeightedEnergyIntegrable.add (hF_meas a (by simp))
          hsum_meas
          (hF a (by simp))
          (ih (fun i hi => hF_meas i (by simp [hi])) fun i hi => hF i (by simp [hi]))

theorem SupportedInSpectrumAE.smul
    {A : Set ℝ} {P : ℝ → ℂ}
    (z : ℂ) (hP : SupportedInSpectrumAE A P) :
    SupportedInSpectrumAE A (fun xi => z * P xi) := by
  -- Proof idea: a scalar multiple preserves a.e. spectral support.
  filter_upwards [hP] with xi hxi hxi_not_mem
  simp [hxi hxi_not_mem]

lemma weightedEnergy_smul
    {A : Set ℝ} {alpha : ℝ} {P : ℝ → ℂ}
    (z : ℂ) (hP : WeightedEnergyIntegrable alpha A P) :
    weightedEnergy alpha A (fun xi => z * P xi)
      = ‖z‖ ^ 2 * weightedEnergy alpha A P := by
  -- Proof idea: use `‖z * P xi‖^2 = ‖z‖^2 * ‖P xi‖^2` and pull the
  -- nonnegative constant through the restricted integral.
  have _ : WeightedEnergyIntegrable alpha A P := hP
  unfold weightedEnergy
  rw [← integral_const_mul]
  congr 1
  ext xi
  rw [norm_mul]
  ring

lemma weightedNorm_smul
    {A : Set ℝ} {alpha : ℝ} {P : ℝ → ℂ}
    (z : ℂ) (hP : WeightedEnergyIntegrable alpha A P) :
    weightedNorm alpha A (fun xi => z * P xi)
      = ‖z‖ * weightedNorm alpha A P := by
  -- Proof idea: combine `weightedEnergy_smul`, nonnegativity of
  -- `weightedEnergy`, and `Real.sqrt_mul` for the scalar square.
  unfold weightedNorm
  rw [weightedEnergy_smul z hP]
  rw [Real.sqrt_mul (sq_nonneg ‖z‖)]
  rw [Real.sqrt_sq_eq_abs]
  rw [abs_of_nonneg (norm_nonneg z)]

private def weightedL2Fun (alpha : ℝ) (P : ℝ → ℂ) : ℝ → ℂ :=
  fun xi => (Real.sqrt (sobolevWeight alpha xi) : ℂ) * P xi

private lemma weightedL2Fun_aestronglyMeasurable
    {A : Set ℝ} {alpha : ℝ} {P : ℝ → ℂ}
    (hP_meas : AEStronglyMeasurable P (volume.restrict (spectrum A))) :
    AEStronglyMeasurable (weightedL2Fun alpha P) (volume.restrict (spectrum A)) := by
  unfold weightedL2Fun
  exact
    (Complex.continuous_ofReal.comp_aestronglyMeasurable
      (Real.continuous_sqrt.comp_aestronglyMeasurable
        (aestronglyMeasurable_sobolevWeight alpha _))).mul hP_meas

private lemma weightedL2Fun_sq_norm_eq
    (alpha : ℝ) (P : ℝ → ℂ) (xi : ℝ) :
    ‖weightedL2Fun alpha P xi‖ ^ 2 =
      sobolevWeight alpha xi * ‖P xi‖ ^ 2 := by
  unfold weightedL2Fun
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    (Real.sqrt (sobolevWeight alpha xi) * ‖P xi‖) ^ 2
        = (Real.sqrt (sobolevWeight alpha xi)) ^ 2 * ‖P xi‖ ^ 2 := by ring
    _ = sobolevWeight alpha xi * ‖P xi‖ ^ 2 := by
        rw [Real.sq_sqrt (sobolevWeight_nonneg alpha xi)]

private lemma weightedL2Fun_memLp_two
    {A : Set ℝ} {alpha : ℝ} {P : ℝ → ℂ}
    (hP_meas : AEStronglyMeasurable P (volume.restrict (spectrum A)))
    (hP : WeightedEnergyIntegrable alpha A P) :
    MemLp (weightedL2Fun alpha P) 2 (volume.restrict (spectrum A)) := by
  refine (memLp_two_iff_integrable_sq_norm (weightedL2Fun_aestronglyMeasurable hP_meas)).2 ?_
  unfold WeightedEnergyIntegrable at hP
  rw [show (fun xi => ‖weightedL2Fun alpha P xi‖ ^ 2) =
      (fun xi => sobolevWeight alpha xi * ‖P xi‖ ^ 2) by
        funext xi
        exact weightedL2Fun_sq_norm_eq alpha P xi]
  exact hP

private lemma weightedEnergy_eq_integral_weightedL2Fun
    {A : Set ℝ} {alpha : ℝ} {P : ℝ → ℂ} :
    weightedEnergy alpha A P =
      ∫ xi, ‖weightedL2Fun alpha P xi‖ ^ 2 ∂(volume.restrict (spectrum A)) := by
  unfold weightedEnergy
  rw [show (fun xi => sobolevWeight alpha xi * ‖P xi‖ ^ 2) =
      (fun xi => ‖weightedL2Fun alpha P xi‖ ^ 2) by
        funext xi
        exact (weightedL2Fun_sq_norm_eq alpha P xi).symm]

private lemma weightedNorm_eq_lpNorm_weightedL2Fun
    {A : Set ℝ} {alpha : ℝ} {P : ℝ → ℂ}
    (hP_meas : AEStronglyMeasurable P (volume.restrict (spectrum A))) :
    weightedNorm alpha A P =
      lpNorm (weightedL2Fun alpha P) 2 (volume.restrict (spectrum A)) := by
  have hmeas :=
    weightedL2Fun_aestronglyMeasurable
      (A := A) (alpha := alpha) (P := P) hP_meas
  rw [weightedNorm, weightedEnergy_eq_integral_weightedL2Fun,
    lpNorm_eq_integral_norm_rpow_toReal
      (p := (2 : ℝ≥0∞)) (by norm_num) (by simp) hmeas]
  norm_num
  rw [Real.sqrt_eq_rpow]

lemma weightedNorm_add_le
    {A : Set ℝ} {alpha : ℝ} {P Q : ℝ → ℂ}
    (hP_meas : AEStronglyMeasurable P (volume.restrict (spectrum A)))
    (hQ_meas : AEStronglyMeasurable Q (volume.restrict (spectrum A)))
    (hP : WeightedEnergyIntegrable alpha A P)
    (hQ : WeightedEnergyIntegrable alpha A Q) :
    weightedNorm alpha A (fun xi => P xi + Q xi)
      ≤ weightedNorm alpha A P + weightedNorm alpha A Q := by
  -- Proof idea: this is the triangle inequality in the weighted `L^2`
  -- seminorm over `spectrum A`.
  let μ := volume.restrict (spectrum A)
  have hPQ_meas : AEStronglyMeasurable (fun xi => P xi + Q xi) μ :=
    hP_meas.add hQ_meas
  have hP_l2 : MemLp (weightedL2Fun alpha P) 2 μ :=
    weightedL2Fun_memLp_two hP_meas hP
  have _hQ_l2 : MemLp (weightedL2Fun alpha Q) 2 μ :=
    weightedL2Fun_memLp_two hQ_meas hQ
  have hsum_eq :
      weightedL2Fun alpha (fun xi => P xi + Q xi)
        = weightedL2Fun alpha P + weightedL2Fun alpha Q := by
    funext xi
    simp [weightedL2Fun, mul_add]
  rw [weightedNorm_eq_lpNorm_weightedL2Fun hPQ_meas,
    weightedNorm_eq_lpNorm_weightedL2Fun hP_meas,
    weightedNorm_eq_lpNorm_weightedL2Fun hQ_meas, hsum_eq]
  exact
    lpNorm_add_le hP_l2 (g := weightedL2Fun alpha Q)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)

lemma weightedNorm_finset_sum_le
    {ι : Type*} {A : Set ℝ} {alpha : ℝ}
    {s : Finset ι} {F : ι → ℝ → ℂ}
    (hF_meas : ∀ i ∈ s, AEStronglyMeasurable (F i) (volume.restrict (spectrum A)))
    (hF : ∀ i ∈ s, WeightedEnergyIntegrable alpha A (F i)) :
    weightedNorm alpha A (fun xi => s.sum (fun i => F i xi))
      ≤ s.sum (fun i => weightedNorm alpha A (F i)) := by
  -- Proof idea: induct on the finite set using `weightedNorm_add_le`.
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [weightedNorm, weightedEnergy]
  | insert a s ha ih =>
      have htail :
          WeightedEnergyIntegrable alpha A (fun xi => s.sum (fun i => F i xi)) :=
        WeightedEnergyIntegrable.finset_sum
          (fun i hi => hF_meas i (by simp [hi])) fun i hi => hF i (by simp [hi])
      have htail_meas :
          AEStronglyMeasurable (fun xi => s.sum (fun i => F i xi))
            (volume.restrict (spectrum A)) :=
        Finset.aestronglyMeasurable_fun_sum s fun i hi => hF_meas i (by simp [hi])
      have hstep :
          weightedNorm alpha A (fun xi => F a xi + s.sum (fun i => F i xi))
            ≤ weightedNorm alpha A (F a) +
                weightedNorm alpha A (fun xi => s.sum (fun i => F i xi)) :=
        weightedNorm_add_le (hF_meas a (by simp)) htail_meas (hF a (by simp)) htail
      have hih :=
        ih (fun i hi => hF_meas i (by simp [hi])) fun i hi => hF i (by simp [hi])
      have hmain :
          weightedNorm alpha A (fun xi => s.sum (fun i => F i xi) + F a xi)
            ≤ s.sum (fun i => weightedNorm alpha A (F i)) + weightedNorm alpha A (F a) := by
        calc
          weightedNorm alpha A (fun xi => s.sum (fun i => F i xi) + F a xi)
              = weightedNorm alpha A (fun xi => F a xi + s.sum (fun i => F i xi)) := by
                congr 1
                ext xi
                abel
          _ ≤ weightedNorm alpha A (F a) +
                weightedNorm alpha A (fun xi => s.sum (fun i => F i xi)) := hstep
          _ ≤ weightedNorm alpha A (F a) + s.sum (fun i => weightedNorm alpha A (F i)) :=
                add_le_add le_rfl hih
          _ = s.sum (fun i => weightedNorm alpha A (F i)) + weightedNorm alpha A (F a) := by
                abel
      simpa [Finset.sum_insert, ha, add_comm] using hmain

lemma sobolevWeight_on_translate_le {A : Set ℝ} {alpha t : ℝ}
    (halpha : AlphaLeHalf alpha)
    (hA_sub : A ⊆ Set.Icc 0 1)
    (ht : t ∈ A)
    {k : ℕ} (hk : 1 ≤ k) :
    sobolevWeight alpha (t + (k : ℝ))
      ≤ 2 * (1 + (k : ℝ)) ^ (2 * alpha) := by
  -- Proof idea: use `t ∈ [0,1]`, `k ≥ 1`, and `0 ≤ alpha ≤ 1/2` to
  -- compare the Sobolev weight on `A+k` with a polynomial weight in `k`.
  have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := hA_sub ht
  have ht_nonneg : 0 ≤ t := htIcc.1
  have ht_le_one : t ≤ 1 := htIcc.2
  have hk_real : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hx_nonneg : 0 ≤ t + (k : ℝ) := by nlinarith
  have hx_le : t + (k : ℝ) ≤ 1 + (k : ℝ) := by nlinarith
  have hbase_one : 1 ≤ 1 + (k : ℝ) := by nlinarith
  have hp_nonneg : 0 ≤ 2 * alpha := by nlinarith [halpha.nonneg]
  by_cases hzero : alpha = 0
  · simp [sobolevWeight, sobolevPower, hzero]
    norm_num
  · have hpow_le :
        |t + (k : ℝ)| ^ (2 * alpha) ≤ (1 + (k : ℝ)) ^ (2 * alpha) := by
      rw [abs_of_nonneg hx_nonneg]
      exact Real.rpow_le_rpow hx_nonneg hx_le hp_nonneg
    have hone_le : 1 ≤ (1 + (k : ℝ)) ^ (2 * alpha) :=
      Real.one_le_rpow hbase_one hp_nonneg
    unfold sobolevWeight sobolevPower
    rw [if_neg hzero]
    nlinarith

private lemma inverseFourierIntegral_eq_fourierInv (P : ℝ → ℂ) :
    (fun x : ℝ => inverseFourierIntegral P x) = (𝓕⁻ P : ℝ → ℂ) := by
  funext x
  rw [inverseFourierIntegral, Real.fourierInv_eq']
  simp [exp2piI, mul_comm, mul_left_comm, mul_assoc]

private lemma continuous_inverseFourierIntegral_of_integrable {P : ℝ → ℂ}
    (hP_int : Integrable P volume) :
    Continuous (fun x : ℝ => inverseFourierIntegral P x) := by
  have hFourier : Continuous (𝓕 P : ℝ → ℂ) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hP_int
  have hInv : Continuous (𝓕⁻ P : ℝ → ℂ) := by
    rw [show (𝓕⁻ P : ℝ → ℂ) = (fun x : ℝ => 𝓕 P (-x)) by
      funext x
      exact Real.fourierInv_eq_fourier_neg P x]
    exact hFourier.comp continuous_neg
  simpa [inverseFourierIntegral_eq_fourierInv P] using hInv

private lemma fourierInv_toLp_ae_eq_fourierInv_of_integrable_memL2
    {P : ℝ → ℂ}
    (hP_int : Integrable P volume)
    (hP_L2 : MemLp P 2 volume) :
    (((𝓕⁻ (hP_L2.toLp P : Lp (α := ℝ) ℂ 2 volume)) :
        Lp (α := ℝ) ℂ 2 volume) : ℝ → ℂ)
      =ᵐ[volume] (𝓕⁻ P : ℝ → ℂ) := by
  let u : Lp (α := ℝ) ℂ 2 volume :=
    𝓕⁻ (hP_L2.toLp P : Lp (α := ℝ) ℂ 2 volume)
  have hu_loc : LocallyIntegrable (u : ℝ → ℂ) volume :=
    (Lp.memLp u).locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hcont : Continuous (𝓕⁻ P : ℝ → ℂ) := by
    simpa [inverseFourierIntegral_eq_fourierInv P] using
      (continuous_inverseFourierIntegral_of_integrable hP_int)
  have hFourier_loc : LocallyIntegrable (𝓕⁻ P : ℝ → ℂ) volume :=
    hcont.locallyIntegrable
  refine ae_eq_of_integral_contDiff_smul_eq hu_loc hFourier_loc ?_
  intro g hg_smooth hg_cpt
  let φ : 𝓢(ℝ, ℂ) :=
    (hg_cpt.comp_left rfl).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp hg_smooth)
  have hswap :
      ∫ ξ : ℝ, (𝓕⁻ P ξ) • φ ξ ∂volume =
        ∫ x : ℝ, P x • (𝓕⁻ (φ : ℝ → ℂ) x) ∂volume := by
    simpa [Real.fourierInv_eq, VectorFourier.fourierIntegral,
      innerₗ_apply_apply, real_inner_comm, mul_comm] using
      (VectorFourier.integral_fourierIntegral_smul_eq_flip
        (L := -innerₗ ℝ) Real.continuous_fourierChar continuous_inner.neg
        hP_int (φ.integrable (μ := volume)))
  calc
    ∫ x : ℝ, g x • u x ∂volume
        = ∫ x : ℝ, φ x • u x ∂volume := by
            apply integral_congr_ae
            filter_upwards with x
            simp [φ]
    _ = (u : TemperedDistribution ℝ ℂ) φ := by
            rw [MeasureTheory.Lp.toTemperedDistribution_apply]
    _ =
        (𝓕⁻ ((hP_L2.toLp P : Lp (α := ℝ) ℂ 2 volume) :
          TemperedDistribution ℝ ℂ)) φ := by
            change
              ((((𝓕⁻ (hP_L2.toLp P : Lp (α := ℝ) ℂ 2 volume)) :
                    Lp (α := ℝ) ℂ 2 volume) : TemperedDistribution ℝ ℂ) φ)
                =
              (𝓕⁻ ((hP_L2.toLp P : Lp (α := ℝ) ℂ 2 volume) :
                TemperedDistribution ℝ ℂ)) φ
            rw [← MeasureTheory.Lp.fourierInv_toTemperedDistribution_eq
              (hP_L2.toLp P : Lp (α := ℝ) ℂ 2 volume)]
    _ =
        ((hP_L2.toLp P : Lp (α := ℝ) ℂ 2 volume) :
          TemperedDistribution ℝ ℂ) (𝓕⁻ φ) := by
            rw [TemperedDistribution.fourierInv_apply]
    _ =
        ∫ x : ℝ, (𝓕⁻ φ) x •
          ((hP_L2.toLp P : Lp (α := ℝ) ℂ 2 volume) : ℝ → ℂ) x ∂volume := by
            rw [MeasureTheory.Lp.toTemperedDistribution_apply]
    _ = ∫ x : ℝ, (𝓕⁻ φ) x • P x ∂volume := by
            apply integral_congr_ae
            filter_upwards [hP_L2.coeFn_toLp] with x hx
            rw [hx]
    _ = ∫ x : ℝ, P x • (𝓕⁻ (φ : ℝ → ℂ) x) ∂volume := by
            apply integral_congr_ae
            filter_upwards with x
            simp [SchwartzMap.fourierInv_coe, mul_comm]
    _ = ∫ x : ℝ, (𝓕⁻ P x) • φ x ∂volume := hswap.symm
    _ = ∫ x : ℝ, φ x • (𝓕⁻ P x) ∂volume := by
            apply integral_congr_ae
            filter_upwards with x
            simp [mul_comm]
    _ = ∫ x : ℝ, g x • (𝓕⁻ P : ℝ → ℂ) x ∂volume := by
            apply integral_congr_ae
            filter_upwards with x
            simp [φ]

theorem fourierInv_toLp_eq_inverseFourierIntegral_of_integrable_memL2
    {P : ℝ → ℂ}
    (hP_int : Integrable P volume)
    (hP_L2 : MemLp P 2 volume) :
    ∃ hF : MemLp (fun x => inverseFourierIntegral P x) 2 volume,
      (𝓕⁻ (hP_L2.toLp P : Lp (α := ℝ) ℂ 2 volume) :
          Lp (α := ℝ) ℂ 2 volume)
        = hF.toLp (fun x => inverseFourierIntegral P x) := by
  -- Proof idea: connect the explicit inverse Fourier integral used in
  -- this definition with Mathlib's Plancherel inverse Fourier transform.
  let u : Lp (α := ℝ) ℂ 2 volume :=
    𝓕⁻ (hP_L2.toLp P : Lp (α := ℝ) ℂ 2 volume)
  have hAeFourier : (u : ℝ → ℂ) =ᵐ[volume] (𝓕⁻ P : ℝ → ℂ) := by
    simpa [u] using
      fourierInv_toLp_ae_eq_fourierInv_of_integrable_memL2 hP_int hP_L2
  have hAe : (u : ℝ → ℂ) =ᵐ[volume] fun x => inverseFourierIntegral P x := by
    simpa [inverseFourierIntegral_eq_fourierInv P] using hAeFourier
  have hF : MemLp (fun x => inverseFourierIntegral P x) 2 volume :=
    MemLp.ae_eq hAe (Lp.memLp u)
  refine ⟨hF, ?_⟩
  calc
    (𝓕⁻ (hP_L2.toLp P : Lp (α := ℝ) ℂ 2 volume) :
        Lp (α := ℝ) ℂ 2 volume) = u := rfl
    _ = (Lp.memLp u).toLp (u : ℝ → ℂ) :=
        (Lp.toLp_coeFn u (Lp.memLp u)).symm
    _ = hF.toLp (fun x => inverseFourierIntegral P x) :=
        MemLp.toLp_congr (Lp.memLp u) hF hAe

theorem continuousInvFourierRep_of_integrable_memL2 {P f : ℝ → ℂ}
    (hP_int : Integrable P volume)
    (hP_L2 : MemLp P 2 volume)
    (hf : ∀ x, f x = inverseFourierIntegral P x) :
    ContinuousInvFourierRep P f := by
  -- Proof idea: use continuity of inverse Fourier integrals for
  -- integrable Fourier-side data and identify the explicit integral with the
  -- inverse Fourier transform of the `Lp` class given by `hP_L2`. The `MemLp`
  -- hypothesis is explicit because `ContinuousInvFourierRep` stores an `L^2`
  -- Plancherel representative.
  refine ⟨hP_L2, ?_, ?_⟩
  · have hcont := continuous_inverseFourierIntegral_of_integrable hP_int
    have hf_eq : f = fun x : ℝ => inverseFourierIntegral P x := by
      funext x
      exact hf x
    simpa [hf_eq] using hcont
  · rcases fourierInv_toLp_eq_inverseFourierIntegral_of_integrable_memL2
        hP_int hP_L2 with ⟨hF, hEq⟩
    have hAe :
        ((𝓕⁻ (hP_L2.toLp P : Lp (α := ℝ) ℂ 2 volume) :
            Lp (α := ℝ) ℂ 2 volume) : ℝ → ℂ)
          =ᵐ[volume] fun x => inverseFourierIntegral P x := by
      rw [hEq]
      exact hF.coeFn_toLp
    exact hAe.trans (Filter.Eventually.of_forall fun x => (hf x).symm)

theorem WeightedFourierWitness.smul
    {A : Set ℝ} {alpha : ℝ} {f P : ℝ → ℂ}
    (c : ℂ)
    (h : WeightedFourierWitness alpha A f P) :
    WeightedFourierWitness alpha A (fun x => c * f x) (fun xi => c * P xi) := by
  -- Proof idea: support is unchanged by scalar multiplication, weighted
  -- energy scales by `‖c‖^2`, and the inverse Fourier representative is linear.
  refine ⟨?_, ?_, ?_⟩
  · exact SupportedInSpectrumAE.smul c h.supported
  · exact WeightedEnergyIntegrable.smul c h.weightedIntegrable
  · have hcP : (c • P) = (fun xi : ℝ => c * P xi) := by
      ext xi
      simp [Pi.smul_apply, smul_eq_mul]
    have hcf : (c • f) = (fun x : ℝ => c * f x) := by
      ext x
      simp [Pi.smul_apply, smul_eq_mul]
    have hmem : MemLp (fun xi : ℝ => c * P xi) 2 volume := by
      simpa [hcP] using h.invRep.memL2.const_smul c
    refine ⟨hmem, continuous_const.mul h.invRep.cont, ?_⟩
    have htoLp :
        hmem.toLp (fun xi : ℝ => c * P xi) =
          c • h.invRep.memL2.toLp P := by
      simpa [hcP] using h.invRep.memL2.toLp_const_smul c
    have hLpEq :
        (𝓕⁻ (hmem.toLp (fun xi : ℝ => c * P xi)) :
            Lp (α := ℝ) ℂ 2 volume) =
          c • (𝓕⁻ (h.invRep.memL2.toLp P :
            Lp (α := ℝ) ℂ 2 volume) : Lp (α := ℝ) ℂ 2 volume) := by
      rw [htoLp]
      simp
    rw [hLpEq]
    simpa [hcf] using
      (Lp.coeFn_smul (α := ℝ) (p := 2) (μ := volume) c
        (𝓕⁻ (h.invRep.memL2.toLp P : Lp (α := ℝ) ℂ 2 volume) :
          Lp (α := ℝ) ℂ 2 volume)).trans
        (h.invRep.invPlancherel_ae.const_smul c)

theorem WeightedFourierWitness.continuous
    {A : Set ℝ} {alpha : ℝ} {f P : ℝ → ℂ}
    (h : WeightedFourierWitness alpha A f P) :
    Continuous f :=
  h.invRep.cont

theorem WeightedFourierWitness.aestronglyMeasurable
    {A : Set ℝ} {alpha : ℝ} {f P : ℝ → ℂ}
    (h : WeightedFourierWitness alpha A f P) :
    AEStronglyMeasurable P volume := by
  -- Proof idea: this follows from the `MemLp` field in the inverse
  -- Fourier representative.
  exact h.invRep.memL2.aestronglyMeasurable

theorem WeightedFourierWitness.invPlancherel_ae
    {A : Set ℝ} {alpha : ℝ} {f P : ℝ → ℂ}
    (h : WeightedFourierWitness alpha A f P) :
    ((𝓕⁻ (h.invRep.memL2.toLp P : Lp (α := ℝ) ℂ 2 volume) :
        Lp (α := ℝ) ℂ 2 volume) : ℝ → ℂ) =ᵐ[volume] f :=
  h.invRep.invPlancherel_ae

theorem memLp_two_of_supported_weightedIntegrable
    {A : Set ℝ} {alpha : ℝ} {P : ℝ → ℂ}
    (hA : AContext A)
    (hP_meas : AEStronglyMeasurable P volume)
    (hsupp : SupportedInSpectrumAE A P)
    (hint : WeightedEnergyIntegrable alpha A P) :
    MemLp P 2 volume := by
  -- Proof idea: combine weighted integrability on `spectrum A`,
  -- `1 ≤ sobolevWeight`, finite volume of `A`-fibres, and the a.e. support
  -- statement outside `spectrum A`.
  have _hspec : MeasurableSet (spectrum A) := hA.measurableSet_spectrum
  have hnormsq_meas :
      AEStronglyMeasurable (fun xi : ℝ => ‖P xi‖ ^ 2)
        (volume.restrict (spectrum A)) := by
    fun_prop
  have hnormsq_int_restrict :
      Integrable (fun xi : ℝ => ‖P xi‖ ^ 2)
        (volume.restrict (spectrum A)) := by
    refine hint.mono_nonneg hnormsq_meas ?_ ?_
    · exact Filter.Eventually.of_forall fun xi => sq_nonneg ‖P xi‖
    · exact Filter.Eventually.of_forall fun xi => by
        have hw : 1 ≤ sobolevWeight alpha xi := one_le_sobolevWeight alpha xi
        have hn : 0 ≤ ‖P xi‖ ^ 2 := sq_nonneg ‖P xi‖
        nlinarith
  have hnormsq_int_global : Integrable (fun xi : ℝ => ‖P xi‖ ^ 2) volume := by
    exact
      IntegrableOn.integrable_of_ae_notMem_eq_zero
        (s := spectrum A) (μ := volume) hnormsq_int_restrict
        (hsupp.mono fun xi hxi hnot => by simp [hxi hnot])
  exact (memLp_two_iff_integrable_sq_norm hP_meas).2 hnormsq_int_global

theorem WeightedFourierWitness.add
    {A : Set ℝ} {alpha : ℝ} {f g P Q : ℝ → ℂ}
    (hf : WeightedFourierWitness alpha A f P)
    (hg : WeightedFourierWitness alpha A g Q) :
    WeightedFourierWitness alpha A (fun x => f x + g x) (fun xi => P xi + Q xi) := by
  -- Proof idea: combine a.e. support, weighted integrability by the
  -- elementary square bound, and linearity of the inverse Fourier transform.
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hf.supported, hg.supported] with xi hP hQ hnot
    simp [hP hnot, hQ hnot]
  · exact
      WeightedEnergyIntegrable.add hf.aestronglyMeasurable.restrict
        hg.aestronglyMeasurable.restrict hf.weightedIntegrable hg.weightedIntegrable
  · have hPQ : (P + Q) = (fun xi : ℝ => P xi + Q xi) := by
      ext xi
      rfl
    have hfg : (f + g) = (fun x : ℝ => f x + g x) := by
      ext x
      rfl
    have hmem : MemLp (fun xi : ℝ => P xi + Q xi) 2 volume := by
      simpa [hPQ] using hf.invRep.memL2.add hg.invRep.memL2
    refine ⟨hmem, hf.invRep.cont.add hg.invRep.cont, ?_⟩
    have htoLp :
        hmem.toLp (fun xi : ℝ => P xi + Q xi) =
          hf.invRep.memL2.toLp P + hg.invRep.memL2.toLp Q := by
      simpa [hPQ] using hf.invRep.memL2.toLp_add hg.invRep.memL2
    have hLpEq :
        (𝓕⁻ (hmem.toLp (fun xi : ℝ => P xi + Q xi)) :
            Lp (α := ℝ) ℂ 2 volume) =
          (𝓕⁻ (hf.invRep.memL2.toLp P : Lp (α := ℝ) ℂ 2 volume) :
            Lp (α := ℝ) ℂ 2 volume) +
          (𝓕⁻ (hg.invRep.memL2.toLp Q : Lp (α := ℝ) ℂ 2 volume) :
            Lp (α := ℝ) ℂ 2 volume) := by
      rw [htoLp]
      simp
    rw [hLpEq]
    simpa [hfg] using
      (Lp.coeFn_add
        (𝓕⁻ (hf.invRep.memL2.toLp P : Lp (α := ℝ) ℂ 2 volume) :
          Lp (α := ℝ) ℂ 2 volume)
        (𝓕⁻ (hg.invRep.memL2.toLp Q : Lp (α := ℝ) ℂ 2 volume) :
          Lp (α := ℝ) ℂ 2 volume)).trans
        (hf.invRep.invPlancherel_ae.add hg.invRep.invPlancherel_ae)

private lemma WeightedFourierWitness.zero {A : Set ℝ} {alpha : ℝ} :
    WeightedFourierWitness alpha A (fun _ : ℝ => 0) (fun _ : ℝ => 0) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Filter.Eventually.of_forall fun _ _ => rfl
  · simp [WeightedEnergyIntegrable]
  · refine continuousInvFourierRep_of_integrable_memL2
      (integrable_zero ℝ ℂ volume)
      (MemLp.zero' (α := ℝ) (ε := ℂ) (μ := volume) (p := 2)) ?_
    intro x
    simp [inverseFourierIntegral]

theorem weightedFourierWitness_finset_sum
    {ι : Type*} {A : Set ℝ} {alpha : ℝ}
    {s : Finset ι} {f P : ι → ℝ → ℂ}
    (h : ∀ i ∈ s, WeightedFourierWitness alpha A (f i) (P i)) :
    WeightedFourierWitness alpha A
      (fun x => s.sum (fun i => f i x))
      (fun xi => s.sum (fun i => P i xi)) := by
  -- Proof idea: induct on the finite set using
  -- `WeightedFourierWitness.add` and the zero witness.
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using (WeightedFourierWitness.zero (A := A) (alpha := alpha))
  | insert a s ha ih =>
      simpa [Finset.sum_insert, ha] using
        WeightedFourierWitness.add (h a (by simp))
          (ih fun i hi => h i (by simp [hi]))

lemma AlphaLeHalf.two_mul_nonneg {alpha : ℝ} (halpha : AlphaLeHalf alpha) :
    0 ≤ 2 * alpha := by
  -- Proof idea: multiply `halpha.nonneg` by the nonnegative constant `2`.
  nlinarith [halpha.nonneg]

lemma AlphaLeHalf.two_mul_le_one {alpha : ℝ} (halpha : AlphaLeHalf alpha) :
    2 * alpha ≤ 1 := by
  -- Proof idea: multiply `halpha.le_half` by `2`.
  nlinarith [halpha.le_half]

end SpectralGapsPrelim.Theorem112
