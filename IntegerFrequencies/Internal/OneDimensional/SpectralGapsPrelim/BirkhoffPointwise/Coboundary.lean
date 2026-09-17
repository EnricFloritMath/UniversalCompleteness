import SpectralGapsPrelim.BirkhoffPointwise.DenseCore

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Topology ENNReal

namespace SpectralGapsPrelim.BirkhoffPointwise

variable {X : Type*} [MeasurableSpace X]
variable {μ : Measure X} [IsProbabilityMeasure μ] {τ : X → X}

private lemma finite_sum_measure_large_level_toReal_le
    {g : X → ℝ} (hg_meas : StronglyMeasurable g) (hg : Integrable g μ)
    {eps : ℝ} (heps : 0 < eps) (M : ℕ) :
    (Finset.sum (Finset.range M) fun N : ℕ =>
      (μ {x | eps * ((N + 1 : ℕ) : ℝ) < |g x|}).toReal)
      ≤ eps⁻¹ * ∫ x, |g x| ∂μ := by
  let A : ℕ → Set X := fun N => {x | eps * ((N + 1 : ℕ) : ℝ) < |g x|}
  have hA_meas : ∀ N, MeasurableSet (A N) := by
    intro N
    dsimp [A]
    simpa [Real.norm_eq_abs] using
      (stronglyMeasurable_const.measurableSet_lt hg_meas.norm :
        MeasurableSet {x : X | eps * ((N + 1 : ℕ) : ℝ) < ‖g x‖})
  have hpoint : ∀ x, (∑ N ∈ Finset.range M,
        (A N).indicator (fun _ => (1 : ℝ)) x) ≤ eps⁻¹ * |g x| := by
    intro x
    induction M with
    | zero =>
        simp [mul_nonneg (inv_nonneg.mpr heps.le) (abs_nonneg (g x))]
    | succ M ih =>
        rw [Finset.sum_range_succ]
        by_cases hxA : x ∈ A M
        · have hterm_le : ∀ N ∈ Finset.range M,
              (A N).indicator (fun _ => (1 : ℝ)) x ≤ 1 := by
            intro N hN
            by_cases hxN : x ∈ A N
            · simp [Set.indicator_of_mem hxN]
            · simp [Set.indicator_of_notMem hxN]
          have hprev_le :
              (∑ N ∈ Finset.range M,
                (A N).indicator (fun _ => (1 : ℝ)) x) ≤ (M : ℝ) := by
            calc
              (∑ N ∈ Finset.range M,
                (A N).indicator (fun _ => (1 : ℝ)) x)
                  ≤ ∑ N ∈ Finset.range M, (1 : ℝ) := Finset.sum_le_sum hterm_le
              _ = (M : ℝ) := by simp
          have hM_lt : (((M + 1 : ℕ) : ℝ)) < eps⁻¹ * |g x| := by
            have hxA' : eps * (((M + 1 : ℕ) : ℝ)) < |g x| := by
              simpa [A] using hxA
            rw [inv_mul_eq_div]
            rw [lt_div_iff₀ heps]
            nlinarith [hxA']
          calc
            (∑ N ∈ Finset.range M,
                (A N).indicator (fun _ => (1 : ℝ)) x) +
              (A M).indicator (fun _ => (1 : ℝ)) x
                ≤ (M : ℝ) + 1 := by
                  gcongr
                  simp [Set.indicator_of_mem hxA]
            _ = (((M + 1 : ℕ) : ℝ)) := by norm_num
            _ ≤ eps⁻¹ * |g x| := le_of_lt hM_lt
        · have hzero : (A M).indicator (fun _ => (1 : ℝ)) x = 0 := by
            simp [Set.indicator_of_notMem hxA]
          simpa [hzero] using ih
  have hind_int : ∀ N, Integrable (fun x => (A N).indicator (fun _ => (1 : ℝ)) x) μ := by
    intro N
    exact (integrable_const (1 : ℝ)).indicator (hA_meas N)
  have hsum_int :
      Integrable (fun x => ∑ N ∈ Finset.range M,
        (A N).indicator (fun _ => (1 : ℝ)) x) μ := by
    exact integrable_finsetSum (Finset.range M) (fun N _hN => hind_int N)
  have hbound_int : Integrable (fun x => eps⁻¹ * |g x|) μ := by
    exact hg.norm.const_mul eps⁻¹
  calc
    (Finset.sum (Finset.range M) fun N : ℕ =>
      (μ {x | eps * ((N + 1 : ℕ) : ℝ) < |g x|}).toReal)
        = ∑ N ∈ Finset.range M, ∫ x, (A N).indicator (fun _ => (1 : ℝ)) x ∂μ := by
          apply Finset.sum_congr rfl
          intro N _hN
          change μ.real (A N) = ∫ x, (A N).indicator (fun _ => (1 : ℝ)) x ∂μ
          rw [← integral_indicator_one (hA_meas N)]
          rfl
    _ = ∫ x, ∑ N ∈ Finset.range M,
          (A N).indicator (fun _ => (1 : ℝ)) x ∂μ := by
          rw [integral_finsetSum]
          exact fun N hN => hind_int N
    _ ≤ ∫ x, eps⁻¹ * |g x| ∂μ := by
          exact integral_mono hsum_int hbound_int hpoint
    _ = eps⁻¹ * ∫ x, |g x| ∂μ := by
          rw [integral_const_mul]

private lemma tsum_measure_ne_top_of_partial_toReal_le
    {A : ℕ → Set X}
    {C : ℝ} (hC_nonneg : 0 ≤ C)
    (hpartial :
      ∀ M : ℕ,
        (Finset.sum (Finset.range M)
          fun N : ℕ => (μ (A N)).toReal) ≤ C) :
    (∑' N : ℕ, μ (A N)) ≠ ∞ := by
  have hle : (∑' N : ℕ, μ (A N)) ≤ ENNReal.ofReal C := by
    apply ENNReal.tsum_le_of_sum_range_le
    intro M
    have hfin : (∑ N ∈ Finset.range M, μ (A N)) ≠ ∞ := by
      exact ENNReal.sum_ne_top.2 (fun N _hN => measure_ne_top μ (A N))
    rw [← ENNReal.ofReal_toReal hfin]
    exact (ENNReal.ofReal_le_ofReal_iff hC_nonneg).2
      (by simpa [ENNReal.toReal_sum] using hpartial M)
  exact ne_top_of_le_ne_top (ENNReal.ofReal_ne_top : ENNReal.ofReal C ≠ ∞) hle

private lemma tsum_measure_large_level_ne_top_strong
    {g : X → ℝ} (hg_meas : StronglyMeasurable g) (hg : Integrable g μ)
    {eps : ℝ} (heps : 0 < eps) :
    (∑' N : ℕ,
      μ {x | eps * ((N + 1 : ℕ) : ℝ) < |g x|}) ≠ ∞ := by
  have hC_nonneg : 0 ≤ eps⁻¹ * ∫ x, |g x| ∂μ := by
    have h_int_nonneg : 0 ≤ ∫ x, |g x| ∂μ := by
      exact integral_nonneg (fun x => abs_nonneg (g x))
    exact mul_nonneg (inv_nonneg.mpr heps.le) h_int_nonneg
  exact tsum_measure_ne_top_of_partial_toReal_le hC_nonneg
    (fun M => finite_sum_measure_large_level_toReal_le hg_meas hg heps M)

omit [IsProbabilityMeasure μ] in
private lemma measure_large_iterate_eq
    (hτ_mp : MeasurePreserving τ μ μ)
    {g : X → ℝ} (hg_meas : StronglyMeasurable g)
    {eps : ℝ} (N : ℕ) :
    μ {x | eps * ((N + 1 : ℕ) : ℝ)
          < |g (τ^[N + 1] x)|}
      =
    μ {x | eps * ((N + 1 : ℕ) : ℝ) < |g x|} := by
  let s : Set X := {x | eps * ((N + 1 : ℕ) : ℝ) < |g x|}
  have hs : MeasurableSet s := by
    dsimp [s]
    simpa [Real.norm_eq_abs] using
      (stronglyMeasurable_const.measurableSet_lt hg_meas.norm :
        MeasurableSet {x : X | eps * ((N + 1 : ℕ) : ℝ) < ‖g x‖})
  have hpre :
      {x | eps * ((N + 1 : ℕ) : ℝ) < |g (τ^[N + 1] x)|} =
        (τ^[N + 1]) ⁻¹' s := by
    rfl
  rw [hpre]
  exact (hτ_mp.iterate (N + 1)).measure_preimage hs.nullMeasurableSet

private lemma tsum_measure_large_iterates_ne_top_strong
    (hτ_mp : MeasurePreserving τ μ μ)
    {g : X → ℝ} (hg_meas : StronglyMeasurable g) (hg : Integrable g μ)
    {eps : ℝ} (heps : 0 < eps) :
    (∑' N : ℕ,
      μ {x | eps * ((N + 1 : ℕ) : ℝ)
          < |g (τ^[N + 1] x)|}) ≠ ∞ := by
  have h_eq :
      (fun N : ℕ =>
        μ {x | eps * ((N + 1 : ℕ) : ℝ) < |g (τ^[N + 1] x)|}) =
        (fun N : ℕ =>
          μ {x | eps * ((N + 1 : ℕ) : ℝ) < |g x|}) := by
    funext N
    exact measure_large_iterate_eq hτ_mp hg_meas N
  rw [h_eq]
  exact
    tsum_measure_large_level_ne_top_strong (μ := μ) hg_meas hg heps

private theorem ae_tendsto_comp_iterate_div_atTop_zero_stronglyMeasurable
    (hτ_mp : MeasurePreserving τ μ μ)
    {g : X → ℝ} (hg_meas : StronglyMeasurable g) (hg : Integrable g μ) :
    ∀ᵐ x ∂μ,
      Tendsto (fun N : ℕ => g (τ^[N] x) / (N : ℝ))
        atTop (nhds 0) := by
  have h_all :
      ∀ᵐ x ∂μ, ∀ m : ℕ,
        ∀ᶠ N in atTop,
          x ∉ {x | (1 / ((m + 1 : ℕ) : ℝ)) * ((N + 1 : ℕ) : ℝ)
              < |g (τ^[N + 1] x)|} := by
    rw [ae_all_iff]
    intro m
    have hδpos : 0 < (1 / ((m + 1 : ℕ) : ℝ)) := by positivity
    exact MeasureTheory.ae_eventually_notMem
      (tsum_measure_large_iterates_ne_top_strong hτ_mp hg_meas hg hδpos)
  filter_upwards [h_all] with x hx
  apply (tendsto_add_atTop_iff_nat 1).1
  rw [Metric.tendsto_nhds]
  intro ε hε
  rcases exists_nat_one_div_lt hε with ⟨m, hm⟩
  have hm' : 1 / (((m + 1 : ℕ) : ℝ)) < ε := by
    simpa [Nat.cast_add, Nat.cast_one] using hm
  filter_upwards [hx m] with N hN
  have hden_pos : 0 < (((N + 1 : ℕ) : ℝ)) := by positivity
  have hle : |g (τ^[N + 1] x)| ≤
      (1 / ((m + 1 : ℕ) : ℝ)) * ((N + 1 : ℕ) : ℝ) := by
    exact le_of_not_gt (by simpa using hN)
  have hdiv_le :
      |g (τ^[N + 1] x) / (((N + 1 : ℕ) : ℝ))| ≤
        1 / ((m + 1 : ℕ) : ℝ) := by
    calc
      |g (τ^[N + 1] x) / (((N + 1 : ℕ) : ℝ))|
          = |g (τ^[N + 1] x)| / (((N + 1 : ℕ) : ℝ)) := by
            rw [abs_div, abs_of_pos hden_pos]
      _ ≤ ((1 / ((m + 1 : ℕ) : ℝ)) * ((N + 1 : ℕ) : ℝ)) /
            (((N + 1 : ℕ) : ℝ)) := by
            exact div_le_div_of_nonneg_right hle hden_pos.le
      _ = 1 / ((m + 1 : ℕ) : ℝ) := by
            field_simp [hden_pos.ne']
  have hdist :
      dist (g (τ^[N + 1] x) / (((N + 1 : ℕ) : ℝ))) 0 < ε := by
    simpa [Real.dist_eq, abs_div, abs_of_pos hden_pos] using
      lt_of_le_of_lt hdiv_le hm'
  simpa [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc] using hdist

/-- Boundary term `g(τ^N x)/N -> 0` for raw integrable `g`. -/
theorem ae_tendsto_comp_iterate_div_atTop_zero
    (hτ_mp : MeasurePreserving τ μ μ)
    {g : X → ℝ} (hg : Integrable g μ) :
    ∀ᵐ x ∂μ,
      Tendsto (fun N : ℕ => g (τ^[N] x) / (N : ℝ))
        atTop (nhds 0) := by
  let g0 : X → ℝ := strongRep (μ := μ) hg
  have hstrong :
      ∀ᵐ x ∂μ,
        Tendsto (fun N : ℕ => g0 (τ^[N] x) / (N : ℝ))
          atTop (nhds 0) := by
    exact ae_tendsto_comp_iterate_div_atTop_zero_stronglyMeasurable
      hτ_mp (strongRep_stronglyMeasurable (μ := μ) hg)
      (strongRep_integrable (μ := μ) hg)
  have heq_iter :
      ∀ᵐ x ∂μ, ∀ n : ℕ, g (τ^[n] x) = g0 (τ^[n] x) := by
    exact ae_forall_iterate_eq_of_ae_eq hτ_mp (strongRep_ae_eq (μ := μ) hg)
  filter_upwards [hstrong, heq_iter] with x hlim heq
  refine Tendsto.congr' ?_ hlim
  filter_upwards with N
  simp [g0, heq N]

private lemma telescoping_coboundary_sum
    (g : X → ℝ) {N : ℕ} (hN : 0 < N) (x : X) :
    birkhoffAverage ℝ τ (fun y => g y - g (τ y)) N x
      =
    (g x - g (τ^[N] x)) / (N : ℝ) := by
  have _hN_ne : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
  rw [birkhoffAverage_eq_sum_div]
  congr 1
  calc
    (∑ q ∈ Finset.range N, (g (τ^[q] x) - g (τ (τ^[q] x))))
        = ∑ q ∈ Finset.range N, (g (τ^[q] x) - g (τ^[q + 1] x)) := by
          apply Finset.sum_congr rfl
          intro q _hq
          simp [Function.iterate_succ_apply']
    _ = g x - g (τ^[N] x) := by
          simpa using (Finset.sum_range_sub' (fun q : ℕ => g (τ^[q] x)) N)

/-- Birkhoff averages of a raw coboundary converge a.e. to zero. -/
theorem ae_tendsto_coboundary_birkhoffAverage_zero
    (hτ_mp : MeasurePreserving τ μ μ)
    {g : X → ℝ} (hg : Integrable g μ) :
    ∀ᵐ x ∂μ,
      Tendsto
        (fun N : ℕ =>
          birkhoffAverage ℝ τ (fun y => g y - g (τ y)) N x)
        atTop (nhds 0) := by
  filter_upwards [ae_tendsto_comp_iterate_div_atTop_zero hτ_mp hg] with x hboundary
  have hconst_div : Tendsto (fun N : ℕ => g x / (N : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
  have hdiff :
      Tendsto (fun N : ℕ => g x / (N : ℝ) - g (τ^[N] x) / (N : ℝ))
        atTop (nhds 0) := by
    simpa using hconst_div.sub hboundary
  refine Tendsto.congr' ?_ hdiff
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  rw [telescoping_coboundary_sum g hN x]
  have hN_ne : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
  field_simp [hN_ne]

private lemma integral_core_toFun
    (hτ_mp : MeasurePreserving τ μ μ)
    (C : L2CoboundaryCore (X := X) τ μ) :
    ∫ y, C.toFun (τ := τ) y ∂μ = C.c := by
  have hconst : Integrable (fun _ : X => C.c) μ := integrable_const C.c
  have hg : Integrable (fun y : X => C.g y) μ := C.integrable_g
  have hgc : Integrable (fun y : X => C.g (τ y)) μ := C.integrable_g_comp (τ := τ) hτ_mp
  calc
    ∫ y, C.c + C.g y - C.g (τ y) ∂μ
        = ∫ y, C.c + C.g y ∂μ - ∫ y, C.g (τ y) ∂μ := by
          simpa [Pi.add_apply, Pi.sub_apply] using
            (integral_sub (hconst.add hg) hgc)
    _ = (∫ y, C.c ∂μ) + (∫ y, C.g y ∂μ) - ∫ y, C.g (τ y) ∂μ := by
          rw [integral_add hconst hg]
    _ = C.c := by
          rw [integral_comp_measurePreserving hτ_mp hg]
          simp

/-- A.e. convergence on the dense coboundary core. -/
theorem ae_tendsto_core_birkhoffAverage_integral
    (hτ_mp : MeasurePreserving τ μ μ)
    (C : L2CoboundaryCore (X := X) τ μ) :
    ∀ᵐ x ∂μ,
      Tendsto
        (fun N : ℕ =>
          birkhoffAverage ℝ τ (C.toFun (τ := τ)) N x)
        atTop
        (nhds (∫ y, C.toFun (τ := τ) y ∂μ)) := by
  rw [integral_core_toFun hτ_mp C]
  have hcob := ae_tendsto_coboundary_birkhoffAverage_zero hτ_mp C.integrable_g
  filter_upwards [hcob] with x hlim
  have htarget :
      Tendsto
        (fun N : ℕ =>
          C.c + birkhoffAverage ℝ τ (fun y : X => C.g y - C.g (τ y)) N x)
        atTop (nhds C.c) := by
    simpa using (tendsto_const_nhds.add hlim)
  refine Tendsto.congr' ?_ htarget
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hconst :
      birkhoffAverage ℝ τ (fun _ : X => C.c) N x = C.c := by
    have hcomp : (fun _ : X => C.c) ∘ τ = (fun _ : X => C.c) := rfl
    have hN_ne : ((N : ℝ) ≠ 0) := by exact_mod_cast (ne_of_gt hN)
    simpa using
      congrFun (birkhoffAverage_of_comp_eq (R := ℝ) (f := τ)
        (g := fun _ : X => C.c) hcomp hN_ne) x
  have hfun :
      C.toFun (τ := τ) =
        ((fun _ : X => C.c) + fun y : X => C.g y - C.g (τ y)) := by
    funext y
    change C.c + C.g y - C.g (τ y) = C.c + (C.g y - C.g (τ y))
    ring
  rw [hfun, birkhoffAverage_add]
  simp [Pi.add_apply, hconst]

end SpectralGapsPrelim.BirkhoffPointwise
