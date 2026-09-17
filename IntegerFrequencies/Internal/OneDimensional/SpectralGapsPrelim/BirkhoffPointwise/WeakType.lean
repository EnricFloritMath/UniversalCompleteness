import SpectralGapsPrelim.BirkhoffPointwise.FiniteMaximal

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Topology ENNReal

namespace SpectralGapsPrelim.BirkhoffPointwise

variable {X : Type*} [MeasurableSpace X]
variable {μ : Measure X} [IsProbabilityMeasure μ] {τ : X → X}

omit [MeasurableSpace X] in
private lemma abs_birkhoffAverage_le_birkhoffAverage_abs
    (F : X → ℝ) {N : ℕ} (_hN : 0 < N) (x : X) :
    |birkhoffAverage ℝ τ F N x|
      ≤ birkhoffAverage ℝ τ (fun y => |F y|) N x := by
  rw [birkhoffAverage, birkhoffAverage]
  simp only [smul_eq_mul]
  rw [abs_mul]
  have hInv_nonneg : 0 ≤ ((N : ℝ)⁻¹) := inv_nonneg.mpr (Nat.cast_nonneg N)
  rw [abs_of_nonneg hInv_nonneg]
  exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hInv_nonneg

omit [IsProbabilityMeasure μ] in
private lemma birkhoffAverage_stronglyMeasurable
    (hτ_mp : MeasurePreserving τ μ μ)
    {F : X → ℝ} (hF : StronglyMeasurable F) (N : ℕ) :
    StronglyMeasurable (fun x => birkhoffAverage ℝ τ F N x) := by
  unfold birkhoffAverage birkhoffSum
  have hsum : StronglyMeasurable
      (fun x : X => ∑ k ∈ Finset.range N, F (τ^[k] x)) :=
    Finset.stronglyMeasurable_fun_sum (Finset.range N) (fun k _hk =>
      hF.comp_measurable (hτ_mp.measurable.iterate k))
  simpa using hsum.const_mul ((N : ℝ)⁻¹)

omit [IsProbabilityMeasure μ] in
private lemma positiveAvgMaxSetFinite_measurable
    (hτ_mp : MeasurePreserving τ μ μ)
    {F : X → ℝ} (hF : StronglyMeasurable F)
    {lambda : ℝ} (K : ℕ) :
    MeasurableSet (positiveAvgMaxSetFinite τ F lambda K) := by
  unfold positiveAvgMaxSetFinite
  rw [show
      {x : X | ∃ N : ℕ, 0 < N ∧ N ≤ K ∧
        lambda < birkhoffAverage ℝ τ (fun y => |F y|) N x} =
      (⋃ N : ℕ,
        {x : X | 0 < N ∧ N ≤ K ∧
          lambda < birkhoffAverage ℝ τ (fun y => |F y|) N x}) by
    ext x
    simp]
  apply MeasurableSet.iUnion
  intro N
  by_cases hN : 0 < N
  · by_cases hNK : N ≤ K
    · have hF_abs : StronglyMeasurable (fun y => |F y|) := by
        simpa [Real.norm_eq_abs] using hF.norm
      have havg :
          StronglyMeasurable
            (fun x => birkhoffAverage ℝ τ (fun y => |F y|) N x) :=
        birkhoffAverage_stronglyMeasurable (μ := μ) hτ_mp hF_abs N
      have hset :
          MeasurableSet
            {x | lambda < birkhoffAverage ℝ τ (fun y => |F y|) N x} :=
        (stronglyMeasurable_const :
          StronglyMeasurable (fun _ : X => lambda)).measurableSet_lt havg
      simpa [hN, hNK] using hset
    · simp [hNK]
  · simp [hN]

omit [MeasurableSpace X] in
private lemma absMaxSetFinite_subset_positiveAvgMaxSetFinite
    (F : X → ℝ) (lambda : ℝ) (K : ℕ) :
    absMaxSetFinite τ F lambda K
      ⊆ positiveAvgMaxSetFinite τ F lambda K := by
  intro x hx
  rcases hx with ⟨N, hN, hNK, hlt⟩
  exact ⟨N, hN, hNK,
    lt_of_lt_of_le hlt (abs_birkhoffAverage_le_birkhoffAverage_abs (τ := τ) F hN x)⟩

private lemma positive_average_lt_iff_partialSum_sub_pos
    {F : X → ℝ} {lambda : ℝ} {N : ℕ} (hN : 0 < N) (x : X) :
    lambda < birkhoffAverage ℝ τ (fun y => |F y|) N x ↔
      0 < partialSum τ (fun y => |F y| - lambda) N x := by
  rw [birkhoffAverage_eq_sum_div]
  unfold partialSum
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hNreal : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  constructor
  · intro h
    have hmul : lambda * (N : ℝ) <
        ∑ q ∈ Finset.range N, |F (τ^[q] x)| := by
      exact (lt_div_iff₀ hNreal).mp h
    nlinarith
  · intro h
    have hmul : lambda * (N : ℝ) <
        ∑ q ∈ Finset.range N, |F (τ^[q] x)| := by
      nlinarith
    exact (lt_div_iff₀ hNreal).mpr hmul

private lemma positiveAvgMaxSetFinite_eq_finitePositiveMaxSet
    {F : X → ℝ} {lambda : ℝ} (K : ℕ) :
    positiveAvgMaxSetFinite τ F lambda K =
      finitePositiveMaxSet τ (fun x => |F x| - lambda) K := by
  ext x
  constructor
  · rintro ⟨N, hN, hNK, hlt⟩
    exact ⟨N, hN, hNK,
      (positive_average_lt_iff_partialSum_sub_pos (τ := τ) hN x).mp hlt⟩
  · rintro ⟨N, hN, hNK, hpos⟩
    exact ⟨N, hN, hNK,
      (positive_average_lt_iff_partialSum_sub_pos (τ := τ) hN x).mpr hpos⟩

omit [IsProbabilityMeasure μ] in
private lemma setIntegral_abs_le_integral_abs
    {F : X → ℝ} (hF : Integrable F μ) {s : Set X}
    (_hs : MeasurableSet s) :
    ∫ x in s, |F x| ∂μ ≤ ∫ x, |F x| ∂μ := by
  simpa [Real.norm_eq_abs] using
    (setIntegral_le_integral (μ := μ) (s := s) hF.norm
      (Eventually.of_forall fun x => norm_nonneg (F x)))

omit [IsProbabilityMeasure μ] in
private lemma integral_const_on_set
    {s : Set X} (_hs : MeasurableSet s) (lambda : ℝ) :
    ∫ _ in s, lambda ∂μ = lambda * (μ s).toReal := by
  rw [setIntegral_const]
  simp [Measure.real, mul_comm]

private lemma lambda_mul_measure_posAvgMaxSetFinite_toReal_le
    (hτ_mp : MeasurePreserving τ μ μ)
    {F : X → ℝ} (hF_meas : StronglyMeasurable F) (hF_int : Integrable F μ)
    {lambda : ℝ} (_hlambda : 0 < lambda) (K : ℕ) :
    lambda * (μ (positiveAvgMaxSetFinite τ F lambda K)).toReal
      ≤ ∫ x, |F x| ∂μ := by
  let E : Set X := positiveAvgMaxSetFinite τ F lambda K
  have hE_meas : MeasurableSet E :=
    positiveAvgMaxSetFinite_measurable (μ := μ) hτ_mp hF_meas K
  have hF_abs_meas : StronglyMeasurable (fun x => |F x|) := by
    simpa [Real.norm_eq_abs] using hF_meas.norm
  have hF_abs_int : Integrable (fun x => |F x|) μ := by
    simpa [Real.norm_eq_abs] using hF_int.norm
  have hg_meas : StronglyMeasurable (fun x => |F x| - lambda) :=
    hF_abs_meas.sub stronglyMeasurable_const
  have hg_int : Integrable (fun x => |F x| - lambda) μ :=
    hF_abs_int.sub (integrable_const lambda)
  have hHopf : 0 ≤ ∫ x in E, |F x| - lambda ∂μ := by
    have h0 := finite_maximal_ergodic_nonneg_integral (μ := μ) hτ_mp hg_meas hg_int K
    simpa [E, positiveAvgMaxSetFinite_eq_finitePositiveMaxSet (τ := τ) (F := F)
      (lambda := lambda) K] using h0
  have hSub :
      ∫ x in E, |F x| - lambda ∂μ =
        ∫ x in E, |F x| ∂μ - ∫ x in E, lambda ∂μ := by
    rw [integral_sub]
    · exact hF_abs_int.restrict
    · exact integrable_const lambda
  have hSet :
      lambda * (μ E).toReal ≤ ∫ x in E, |F x| ∂μ := by
    rw [hSub, integral_const_on_set (μ := μ) hE_meas lambda] at hHopf
    linarith
  exact hSet.trans (setIntegral_abs_le_integral_abs (μ := μ) hF_int hE_meas)

private lemma measure_le_of_mul_toReal_le
    {s : Set X} (_hs_meas : MeasurableSet s)
    {lambda C : ℝ} (hlambda : 0 < lambda) (_hC_nonneg : 0 ≤ C)
    (h : lambda * (μ s).toReal ≤ C) :
    μ s ≤ ENNReal.ofReal (C / lambda) := by
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ s)]
  exact ENNReal.ofReal_le_ofReal
    ((le_div_iff₀ hlambda).mpr (by simpa [mul_comm] using h))

private theorem measure_positiveAvgMaxSetFinite_le_strong
    (hτ_mp : MeasurePreserving τ μ μ)
    {F : X → ℝ} (hF_meas : StronglyMeasurable F) (hF_int : Integrable F μ)
    {lambda : ℝ} (hlambda : 0 < lambda) (K : ℕ) :
    μ (positiveAvgMaxSetFinite τ F lambda K)
      ≤ ENNReal.ofReal ((∫ x, |F x| ∂μ) / lambda) := by
  exact measure_le_of_mul_toReal_le (μ := μ)
    (positiveAvgMaxSetFinite_measurable (μ := μ) hτ_mp hF_meas K)
    hlambda
    (integral_nonneg fun x => abs_nonneg (F x))
    (lambda_mul_measure_posAvgMaxSetFinite_toReal_le
      (μ := μ) hτ_mp hF_meas hF_int hlambda K)

omit [IsProbabilityMeasure μ] in
private lemma absMaxSetFinite_measurable
    (hτ_mp : MeasurePreserving τ μ μ)
    {F : X → ℝ} (hF : StronglyMeasurable F) {lambda : ℝ} (K : ℕ) :
    MeasurableSet (absMaxSetFinite τ F lambda K) := by
  unfold absMaxSetFinite
  rw [show
      {x : X | ∃ N : ℕ, 0 < N ∧ N ≤ K ∧
        lambda < |birkhoffAverage ℝ τ F N x|} =
      (⋃ N : ℕ,
        {x : X | 0 < N ∧ N ≤ K ∧ lambda < |birkhoffAverage ℝ τ F N x|}) by
    ext x
    simp]
  apply MeasurableSet.iUnion
  intro N
  by_cases hN : 0 < N
  · by_cases hNK : N ≤ K
    · have havg : StronglyMeasurable (fun x => birkhoffAverage ℝ τ F N x) :=
        birkhoffAverage_stronglyMeasurable (μ := μ) hτ_mp hF N
      have hAbs : StronglyMeasurable (fun x => |birkhoffAverage ℝ τ F N x|) := by
        simpa [Real.norm_eq_abs] using havg.norm
      have hset :
          MeasurableSet {x | lambda < |birkhoffAverage ℝ τ F N x|} :=
        (stronglyMeasurable_const :
          StronglyMeasurable (fun _ : X => lambda)).measurableSet_lt hAbs
      simpa [hN, hNK] using hset
    · simp [hNK]
  · simp [hN]

omit [IsProbabilityMeasure μ] in
private lemma absMaxSetFinite_ae_eq_of_ae_eq
    (hτ_mp : MeasurePreserving τ μ μ)
    {F G : X → ℝ} (hFG : F =ᵐ[μ] G) (lambda : ℝ) (K : ℕ) :
    absMaxSetFinite τ F lambda K =ᵐ[μ] absMaxSetFinite τ G lambda K := by
  have hAll :
      ∀ᵐ x ∂μ, ∀ N : ℕ,
        birkhoffAverage ℝ τ F N x = birkhoffAverage ℝ τ G N x := by
    exact ae_all_iff.mpr fun N =>
      birkhoffAverage_ae_eq_of_ae_eq (μ := μ) hτ_mp hFG N
  filter_upwards [hAll] with x hx
  apply propext
  constructor
  · rintro ⟨N, hN, hNK, hlt⟩
    exact ⟨N, hN, hNK, by simpa [hx N] using hlt⟩
  · rintro ⟨N, hN, hNK, hlt⟩
    exact ⟨N, hN, hNK, by simpa [hx N] using hlt⟩

private theorem measure_absMaxSetFinite_le_strong
    (hτ_mp : MeasurePreserving τ μ μ)
    {F : X → ℝ} (hF_meas : StronglyMeasurable F) (hF_int : Integrable F μ)
    {lambda : ℝ} (hlambda : 0 < lambda) (K : ℕ) :
    μ (absMaxSetFinite τ F lambda K)
      ≤ ENNReal.ofReal ((∫ x, |F x| ∂μ) / lambda) := by
  exact (measure_mono
    (absMaxSetFinite_subset_positiveAvgMaxSetFinite (τ := τ) F lambda K)).trans
      (measure_positiveAvgMaxSetFinite_le_strong (μ := μ) hτ_mp hF_meas hF_int hlambda K)

omit [IsProbabilityMeasure μ] in
private lemma absMaxSet_measurable
    (hτ_mp : MeasurePreserving τ μ μ)
    {F : X → ℝ} (hF : StronglyMeasurable F) {lambda : ℝ} :
    MeasurableSet (absMaxSet τ F lambda) := by
  unfold absMaxSet
  rw [show
      {x : X | ∃ N : ℕ, 0 < N ∧ lambda < |birkhoffAverage ℝ τ F N x|} =
      (⋃ N : ℕ, {x : X | 0 < N ∧ lambda < |birkhoffAverage ℝ τ F N x|}) by
    ext x
    simp]
  apply MeasurableSet.iUnion
  intro N
  by_cases hN : 0 < N
  · have havg : StronglyMeasurable (fun x => birkhoffAverage ℝ τ F N x) :=
      birkhoffAverage_stronglyMeasurable (μ := μ) hτ_mp hF N
    have hAbs : StronglyMeasurable (fun x => |birkhoffAverage ℝ τ F N x|) := by
      simpa [Real.norm_eq_abs] using havg.norm
    have hset :
        MeasurableSet {x | lambda < |birkhoffAverage ℝ τ F N x|} :=
      (stronglyMeasurable_const :
        StronglyMeasurable (fun _ : X => lambda)).measurableSet_lt hAbs
    simpa [hN] using hset
  · simp [hN]

omit [MeasurableSpace X] in
private lemma absMaxSet_iUnion_finite
    (F : X → ℝ) (lambda : ℝ) :
    absMaxSet τ F lambda =
      ⋃ K : ℕ, absMaxSetFinite τ F lambda K := by
  ext x
  simp only [absMaxSet, absMaxSetFinite, Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨N, hN, hlt⟩
    exact ⟨N, N, hN, le_rfl, hlt⟩
  · rintro ⟨K, N, hN, _hNK, hlt⟩
    exact ⟨N, hN, hlt⟩

omit [MeasurableSpace X] in
private lemma absMaxSetFinite_mono
    (F : X → ℝ) (lambda : ℝ) :
    Monotone (fun K : ℕ => absMaxSetFinite τ F lambda K) := by
  intro K L hKL x hx
  rcases hx with ⟨N, hN, hNK, hlt⟩
  exact ⟨N, hN, hNK.trans hKL, hlt⟩

omit [IsProbabilityMeasure μ] in
private lemma measure_absMaxSet_le_of_forall_finite_le
    (_hτ_mp : MeasurePreserving τ μ μ)
    {F : X → ℝ} (_hF : StronglyMeasurable F)
    {lambda : ℝ} {C : ℝ≥0∞}
    (hfinite : ∀ K : ℕ, μ (absMaxSetFinite τ F lambda K) ≤ C) :
    μ (absMaxSet τ F lambda) ≤ C := by
  rw [absMaxSet_iUnion_finite (τ := τ) F lambda]
  rw [(absMaxSetFinite_mono (τ := τ) F lambda).measure_iUnion]
  exact iSup_le hfinite

private theorem measure_absMaxSet_le_strong
    (hτ_mp : MeasurePreserving τ μ μ)
    {F : X → ℝ} (hF_meas : StronglyMeasurable F) (hF_int : Integrable F μ)
    {lambda : ℝ} (hlambda : 0 < lambda) :
    μ (absMaxSet τ F lambda)
      ≤ ENNReal.ofReal ((∫ x, |F x| ∂μ) / lambda) := by
  exact measure_absMaxSet_le_of_forall_finite_le (μ := μ) hτ_mp hF_meas
    (fun K => measure_absMaxSetFinite_le_strong (μ := μ) hτ_mp hF_meas hF_int hlambda K)

omit [IsProbabilityMeasure μ] in
private lemma absMaxSet_ae_eq_of_ae_eq
    (hτ_mp : MeasurePreserving τ μ μ)
    {F G : X → ℝ} (hFG : F =ᵐ[μ] G) (lambda : ℝ) :
    absMaxSet τ F lambda =ᵐ[μ] absMaxSet τ G lambda := by
  have hAll :
      ∀ᵐ x ∂μ, ∀ N : ℕ,
        birkhoffAverage ℝ τ F N x = birkhoffAverage ℝ τ G N x := by
    exact ae_all_iff.mpr fun N =>
      birkhoffAverage_ae_eq_of_ae_eq (μ := μ) hτ_mp hFG N
  filter_upwards [hAll] with x hx
  apply propext
  constructor
  · rintro ⟨N, hN, hlt⟩
    exact ⟨N, hN, by simpa [hx N] using hlt⟩
  · rintro ⟨N, hN, hlt⟩
    exact ⟨N, hN, by simpa [hx N] using hlt⟩

omit [IsProbabilityMeasure μ] in
private lemma measure_absMaxSet_congr_ae
    (hτ_mp : MeasurePreserving τ μ μ)
    {F G : X → ℝ} (hFG : F =ᵐ[μ] G) (lambda : ℝ) :
    μ (absMaxSet τ F lambda) = μ (absMaxSet τ G lambda) := by
  exact measure_congr (absMaxSet_ae_eq_of_ae_eq (μ := μ) hτ_mp hFG lambda)

omit [IsProbabilityMeasure μ] in
private lemma integral_abs_congr_ae
    {F G : X → ℝ} (hFG : F =ᵐ[μ] G) :
    ∫ x, |F x| ∂μ = ∫ x, |G x| ∂μ := by
  exact integral_congr_ae (hFG.mono fun _ hx => by simp [hx])

/-- Weak type `(1,1)` maximal inequality for Birkhoff averages. -/
theorem measure_absMaxSet_le
    (hτ_mp : MeasurePreserving τ μ μ)
    {F : X → ℝ} (hF : Integrable F μ)
    {lambda : ℝ} (hlambda : 0 < lambda) :
    μ (absMaxSet τ F lambda)
      ≤ ENNReal.ofReal ((∫ x, |F x| ∂μ) / lambda) := by
  let F0 : X → ℝ := strongRep (μ := μ) hF
  have hF_eq : F =ᵐ[μ] F0 := strongRep_ae_eq (μ := μ) hF
  have hmeasure : μ (absMaxSet τ F lambda) = μ (absMaxSet τ F0 lambda) :=
    measure_absMaxSet_congr_ae (μ := μ) hτ_mp hF_eq lambda
  have hintegral : ∫ x, |F x| ∂μ = ∫ x, |F0 x| ∂μ :=
    integral_abs_congr_ae (μ := μ) hF_eq
  rw [hmeasure, hintegral]
  exact measure_absMaxSet_le_strong (μ := μ) hτ_mp
    (strongRep_stronglyMeasurable (μ := μ) hF)
    (strongRep_integrable (μ := μ) hF) hlambda

end SpectralGapsPrelim.BirkhoffPointwise
