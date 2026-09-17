import SpectralGapsPrelim.BirkhoffPointwise.WeakType

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Topology ENNReal

namespace SpectralGapsPrelim.BirkhoffPointwise

variable {X : Type*} [MeasurableSpace X]
variable {μ : Measure X} [IsProbabilityMeasure μ] {τ : X → X}

omit [IsProbabilityMeasure μ] in
private lemma integral_error_controls_integral_sub
    {F G : X → ℝ} (hF : Integrable F μ) (hG : Integrable G μ) :
    |(∫ x, F x ∂μ) - (∫ x, G x ∂μ)|
      ≤ ∫ x, |F x - G x| ∂μ := by
  rw [← Real.norm_eq_abs, ← integral_sub hF hG]
  simpa [Real.norm_eq_abs] using
    (norm_integral_le_integral_norm (μ := μ) (fun x => F x - G x))

private lemma basisEps_pos (m : ℕ) : 0 < basisEps m := by
  have hm : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_pos m
  simpa [basisEps] using inv_pos.mpr hm

private lemma basisLambda_pos (m : ℕ) : 0 < basisLambda m := by
  exact div_pos (basisEps_pos m) (by norm_num : (0 : ℝ) < 4)

private lemma three_basisLambda_lt_basisEps (m : ℕ) :
    3 * basisLambda m < basisEps m := by
  have hpos : 0 < basisEps m := basisEps_pos m
  rw [basisLambda]
  nlinarith

private lemma basisEps_tendsto_zero :
    Tendsto basisEps atTop (nhds 0) := by
  change Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ))⁻¹) atTop (nhds 0)
  simpa [one_div, Nat.cast_add, Nat.cast_one] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

private lemma exists_basisEps_lt {eps : ℝ} (heps : 0 < eps) :
    ∃ m : ℕ, basisEps m < eps := by
  exact ((tendsto_order.1 basisEps_tendsto_zero).2 eps heps).exists

omit [IsProbabilityMeasure μ] in
private lemma integrable_error
    {F G : X → ℝ} (hF : Integrable F μ) (hG : Integrable G μ) :
    Integrable (fun x => F x - G x) μ := by
  exact hF.sub hG

private lemma tsum_ofReal_error_div_ne_top
    {e : ℕ → ℝ} (_he_nonneg : ∀ j, 0 ≤ e j)
    (he_sum : Summable e) {lambda : ℝ} (_hlambda : 0 < lambda) :
    (∑' j : ℕ, ENNReal.ofReal (e j / lambda)) ≠ ∞ := by
  exact (he_sum.div_const lambda).tsum_ofReal_ne_top

private lemma tsum_measure_badMax_ne_top
    (hτ_mp : MeasurePreserving τ μ μ)
    {F : X → ℝ} (hF : Integrable F μ)
    {D : ℕ → X → ℝ} (hD_int : ∀ j, Integrable (D j) μ)
    {lambda : ℝ} (hlambda : 0 < lambda)
    (hD_summable :
      Summable (fun j : ℕ => ∫ x, |F x - D j x| ∂μ)) :
    (∑' j : ℕ,
      μ (absMaxSet τ (fun x => F x - D j x) lambda)) ≠ ∞ := by
  have hle :
      (∑' j : ℕ,
        μ (absMaxSet τ (fun x => F x - D j x) lambda))
        ≤
      (∑' j : ℕ,
        ENNReal.ofReal ((∫ x, |F x - D j x| ∂μ) / lambda)) := by
    refine ENNReal.tsum_le_tsum fun j => ?_
    exact measure_absMaxSet_le (μ := μ) (τ := τ) hτ_mp
      (integrable_error hF (hD_int j)) hlambda
  have hfinite :
      (∑' j : ℕ,
        ENNReal.ofReal ((∫ x, |F x - D j x| ∂μ) / lambda)) ≠ ∞ :=
    tsum_ofReal_error_div_ne_top
      (fun j => integral_nonneg fun x => abs_nonneg (F x - D j x))
      hD_summable hlambda
  exact ne_top_of_le_ne_top hfinite hle

private lemma ae_eventually_not_badMax_all_basis
    (hτ_mp : MeasurePreserving τ μ μ)
    {F : X → ℝ} (hF : Integrable F μ)
    {D : ℕ → X → ℝ}
    (hD_int : ∀ j, Integrable (D j) μ)
    (hD_summable :
      Summable (fun j : ℕ => ∫ x, |F x - D j x| ∂μ)) :
    ∀ᵐ x ∂μ,
      ∀ m : ℕ,
        ∀ᶠ j in atTop,
          x ∉ absMaxSet τ (fun y => F y - D j y) (basisLambda m) := by
  refine ae_all_iff.mpr fun m => ?_
  exact MeasureTheory.ae_eventually_notMem
    (μ := μ)
    (s := fun j : ℕ =>
      absMaxSet τ (fun y => F y - D j y) (basisLambda m))
    (tsum_measure_badMax_ne_top (μ := μ) (τ := τ) hτ_mp hF hD_int
      (basisLambda_pos m) hD_summable)

omit [IsProbabilityMeasure μ] in
private lemma ae_tendsto_D_all
    {D : ℕ → X → ℝ}
    (hD_tendsto :
      ∀ j,
        ∀ᵐ x ∂μ,
          Tendsto
            (fun N : ℕ => birkhoffAverage ℝ τ (D j) N x)
            atTop
            (nhds (∫ y, D j y ∂μ))) :
    ∀ᵐ x ∂μ,
      ∀ j,
        Tendsto
          (fun N : ℕ => birkhoffAverage ℝ τ (D j) N x)
          atTop
          (nhds (∫ y, D j y ∂μ)) := by
  exact ae_all_iff.mpr hD_tendsto

omit [IsProbabilityMeasure μ] in
private lemma error_integrals_tendsto_zero
    {F : X → ℝ} {D : ℕ → X → ℝ}
    (hD_summable :
      Summable (fun j : ℕ => ∫ x, |F x - D j x| ∂μ)) :
    Tendsto (fun j : ℕ => ∫ x, |F x - D j x| ∂μ)
      atTop (nhds 0) := by
  exact hD_summable.tendsto_atTop_zero

omit [MeasurableSpace X] in
private lemma birkhoffAverage_sub_error
    (F G : X → ℝ) (N : ℕ) (x : X) :
    birkhoffAverage ℝ τ (fun y => F y - G y) N x
      =
    birkhoffAverage ℝ τ F N x
      - birkhoffAverage ℝ τ G N x := by
  change birkhoffAverage ℝ τ (F - G) N x =
    birkhoffAverage ℝ τ F N x - birkhoffAverage ℝ τ G N x
  simpa using
    congrFun (congrFun
      (birkhoffAverage_sub (R := ℝ) (f := τ) (g := F) (g' := G)) N) x

omit [MeasurableSpace X] in
private lemma eventual_close_of_not_absMaxSet_atTop
    {lambda : ℝ} (_hlambda : 0 < lambda)
    {F G : X → ℝ} {x : X}
    (hx : x ∉ absMaxSet τ (fun y => F y - G y) lambda) :
    ∀ᶠ N in atTop,
      |birkhoffAverage ℝ τ F N x
        - birkhoffAverage ℝ τ G N x| ≤ lambda := by
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hnot : ¬ lambda <
      |birkhoffAverage ℝ τ (fun y => F y - G y) N x| := by
    intro hlt
    exact hx ⟨N, hN, hlt⟩
  have hle : |birkhoffAverage ℝ τ (fun y => F y - G y) N x| ≤ lambda :=
    le_of_not_gt hnot
  simpa [birkhoffAverage_sub_error (τ := τ) F G N x] using hle

private lemma ae_eventually_close_for_all_basis
    (hτ_mp : MeasurePreserving τ μ μ)
    {F : X → ℝ} (hF : Integrable F μ)
    {D : ℕ → X → ℝ}
    (hD_int : ∀ j, Integrable (D j) μ)
    (hD_tendsto :
      ∀ j,
        ∀ᵐ x ∂μ,
          Tendsto
            (fun N : ℕ => birkhoffAverage ℝ τ (D j) N x)
            atTop
            (nhds (∫ y, D j y ∂μ)))
    (hD_summable :
      Summable (fun j : ℕ => ∫ x, |F x - D j x| ∂μ)) :
    ∀ᵐ x ∂μ,
      ∀ m : ℕ,
        ∃ j : ℕ,
          (∀ᶠ N in atTop,
            |birkhoffAverage ℝ τ F N x
              - birkhoffAverage ℝ τ (D j) N x| ≤ basisLambda m)
          ∧
          (∀ᶠ N in atTop,
            |birkhoffAverage ℝ τ (D j) N x - ∫ y, D j y ∂μ|
              < basisLambda m)
          ∧
          |(∫ y, D j y ∂μ) - ∫ y, F y ∂μ| < basisLambda m := by
  have hBadAE :
      ∀ᵐ x ∂μ,
        ∀ m : ℕ,
          ∀ᶠ j in atTop,
            x ∉ absMaxSet τ (fun y => F y - D j y) (basisLambda m) :=
    ae_eventually_not_badMax_all_basis (μ := μ) (τ := τ)
      hτ_mp hF hD_int hD_summable
  have hTendAE :
      ∀ᵐ x ∂μ,
        ∀ j,
          Tendsto
            (fun N : ℕ => birkhoffAverage ℝ τ (D j) N x)
            atTop
            (nhds (∫ y, D j y ∂μ)) :=
    ae_tendsto_D_all (μ := μ) (τ := τ) hD_tendsto
  filter_upwards [hBadAE, hTendAE] with x hxBad hxTend
  intro m
  have hErrSmall :
      ∀ᶠ j in atTop, (∫ x, |F x - D j x| ∂μ) < basisLambda m :=
    (tendsto_order.1 (error_integrals_tendsto_zero (μ := μ) hD_summable)).2
      (basisLambda m) (basisLambda_pos m)
  have hIntSmall :
      ∀ᶠ j in atTop,
        |(∫ y, D j y ∂μ) - ∫ y, F y ∂μ| < basisLambda m := by
    filter_upwards [hErrSmall] with j hj
    have hcontrol :
        |(∫ y, D j y ∂μ) - ∫ y, F y ∂μ|
          ≤ ∫ x, |F x - D j x| ∂μ := by
      simpa [abs_sub_comm] using
        (integral_error_controls_integral_sub (μ := μ) hF (hD_int j))
    exact lt_of_le_of_lt hcontrol hj
  rcases ((hxBad m).and hIntSmall).exists with ⟨j, hbad, hint⟩
  refine ⟨j,
    eventual_close_of_not_absMaxSet_atTop (τ := τ)
      (basisLambda_pos m) hbad,
    ?_,
    hint⟩
  simpa [Real.dist_eq] using
    (Metric.tendsto_nhds.mp (hxTend j) (basisLambda m) (basisLambda_pos m))

omit [IsProbabilityMeasure μ] in
private lemma eventual_close_to_integral_of_approximant
    {m : ℕ} {F G : X → ℝ} {x : X}
    (hFG :
      ∀ᶠ N in atTop,
        |birkhoffAverage ℝ τ F N x -
          birkhoffAverage ℝ τ G N x| ≤ basisLambda m)
    (hG :
      ∀ᶠ N in atTop,
        |birkhoffAverage ℝ τ G N x - ∫ y, G y ∂μ| < basisLambda m)
    (hInt :
      |(∫ y, G y ∂μ) - ∫ y, F y ∂μ| < basisLambda m) :
    ∀ᶠ N in atTop,
      |birkhoffAverage ℝ τ F N x - ∫ y, F y ∂μ| < basisEps m := by
  filter_upwards [hFG, hG] with N hFGN hGN
  have htri :
      |birkhoffAverage ℝ τ F N x - ∫ y, F y ∂μ|
        ≤
      |birkhoffAverage ℝ τ F N x -
          birkhoffAverage ℝ τ G N x|
        + |birkhoffAverage ℝ τ G N x - ∫ y, G y ∂μ|
        + |(∫ y, G y ∂μ) - ∫ y, F y ∂μ| := by
    calc
      |birkhoffAverage ℝ τ F N x - ∫ y, F y ∂μ|
          =
        |(birkhoffAverage ℝ τ F N x -
            birkhoffAverage ℝ τ G N x)
          + (birkhoffAverage ℝ τ G N x - ∫ y, G y ∂μ)
          + ((∫ y, G y ∂μ) - ∫ y, F y ∂μ)| := by ring_nf
      _ ≤
        |birkhoffAverage ℝ τ F N x -
            birkhoffAverage ℝ τ G N x|
          + |birkhoffAverage ℝ τ G N x - ∫ y, G y ∂μ|
          + |(∫ y, G y ∂μ) - ∫ y, F y ∂μ| := by
        exact abs_add_three _ _ _
  have hsum :
      |birkhoffAverage ℝ τ F N x -
          birkhoffAverage ℝ τ G N x|
        + |birkhoffAverage ℝ τ G N x - ∫ y, G y ∂μ|
        + |(∫ y, G y ∂μ) - ∫ y, F y ∂μ|
        < 3 * basisLambda m := by
    nlinarith [hFGN, hGN, hInt]
  exact lt_of_le_of_lt htri (hsum.trans (three_basisLambda_lt_basisEps m))

private lemma tendsto_of_eventually_close_basis
    {u : ℕ → ℝ} {a : ℝ}
    (h :
      ∀ m : ℕ,
        ∀ᶠ N in atTop, |u N - a| < basisEps m) :
    Tendsto u atTop (nhds a) := by
  refine Metric.tendsto_nhds.mpr fun eps heps => ?_
  rcases exists_basisEps_lt heps with ⟨m, hm⟩
  filter_upwards [h m] with N hN
  simpa [Real.dist_eq] using hN.trans hm

/-- Maximal dense-transfer theorem from summable `L1` approximation. -/
theorem ae_tendsto_of_summable_L1_approx
    (hτ_mp : MeasurePreserving τ μ μ)
    {F : X → ℝ} (hF : Integrable F μ)
    {D : ℕ → X → ℝ}
    (hD_int : ∀ j, Integrable (D j) μ)
    (hD_tendsto :
      ∀ j,
        ∀ᵐ x ∂μ,
          Tendsto
            (fun N : ℕ => birkhoffAverage ℝ τ (D j) N x)
            atTop
            (nhds (∫ y, D j y ∂μ)))
    (hD_summable :
      Summable (fun j : ℕ => ∫ x, |F x - D j x| ∂μ)) :
    ∀ᵐ x ∂μ,
      Tendsto
        (fun N : ℕ => birkhoffAverage ℝ τ F N x)
        atTop
        (nhds (∫ y, F y ∂μ)) := by
  have hCloseAE :
      ∀ᵐ x ∂μ,
        ∀ m : ℕ,
          ∃ j : ℕ,
            (∀ᶠ N in atTop,
              |birkhoffAverage ℝ τ F N x
                - birkhoffAverage ℝ τ (D j) N x| ≤ basisLambda m)
            ∧
            (∀ᶠ N in atTop,
              |birkhoffAverage ℝ τ (D j) N x - ∫ y, D j y ∂μ|
                < basisLambda m)
            ∧
            |(∫ y, D j y ∂μ) - ∫ y, F y ∂μ| < basisLambda m :=
    ae_eventually_close_for_all_basis (μ := μ) (τ := τ)
      hτ_mp hF hD_int hD_tendsto hD_summable
  filter_upwards [hCloseAE] with x hxClose
  refine tendsto_of_eventually_close_basis (a := ∫ y, F y ∂μ) ?_
  intro m
  rcases hxClose m with ⟨j, hFG, hG, hInt⟩
  exact eventual_close_to_integral_of_approximant (μ := μ) (τ := τ)
    (m := m) (F := F) (G := D j) (x := x) hFG hG hInt

end SpectralGapsPrelim.BirkhoffPointwise
