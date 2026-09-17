import PeriodicWeakGapsHD.HigherDim.Setup

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Topology ENNReal FourierTransform

namespace SpectralGapsPrelim.HigherDim

/-!
Escaping enumerations of infinite uniformly discrete sets.
-/

private lemma uniformlyDiscrete_isClosed {d : ℕ}
    {Lambda : Set (E d)} (hLambda : UniformlyDiscrete Lambda) :
    IsClosed Lambda := by
  rcases hLambda with ⟨delta, hdelta_pos, hsep⟩
  exact Metric.isClosed_of_pairwise_le_dist hdelta_pos hsep

private lemma uniformlyDiscrete_isDiscrete {d : ℕ}
    {Lambda : Set (E d)} (hLambda : UniformlyDiscrete Lambda) :
    IsDiscrete Lambda := by
  rcases hLambda with ⟨delta, hdelta_pos, hsep⟩
  rw [isDiscrete_iff_forall_exists_isOpen]
  intro x hx
  refine ⟨Metric.ball x (delta / 2), Metric.isOpen_ball, ?_⟩
  ext y
  constructor
  · rintro ⟨hy_ball, hyLambda⟩
    by_contra hyx
    have hxy : x ≠ y := fun h => hyx h.symm
    have hdist_lt_half : dist x y < delta / 2 := by
      simpa [Metric.mem_ball, dist_comm] using hy_ball
    have hdist_lt : dist x y < delta := by linarith
    exact (not_lt_of_ge (hsep x hx y hyLambda hxy)) hdist_lt
  · intro hyx
    subst y
    exact ⟨by simp [Metric.mem_ball, hdelta_pos], hx⟩

theorem uniformlyDiscrete_finite_inter_closedBall {d : ℕ}
    {Lambda : Set (E d)}
    (hLambda : UniformlyDiscrete Lambda)
    (R : ℝ) :
    (Lambda ∩ Metric.closedBall (0 : E d) R).Finite := by
  have hfinite :
      (Metric.closedBall (0 : E d) R ∩ Lambda).Finite :=
    Metric.finite_isBounded_inter_isClosed
      (K := Metric.closedBall (0 : E d) R) (s := Lambda)
      (uniformlyDiscrete_isDiscrete hLambda)
      Metric.isBounded_closedBall
      (uniformlyDiscrete_isClosed hLambda)
  simpa [Set.inter_comm] using hfinite

theorem uniformlyDiscrete_countable {d : ℕ} {Lambda : Set (E d)}
    (hLambda : UniformlyDiscrete Lambda) :
    Lambda.Countable := by
  have hcover :
      Lambda ⊆ ⋃ n : ℕ, Lambda ∩ Metric.closedBall (0 : E d) (n : ℝ) := by
    intro x hx
    obtain ⟨n, hn⟩ := exists_nat_ge ‖x‖
    refine Set.mem_iUnion.2 ⟨n, hx, ?_⟩
    simpa [Metric.mem_closedBall, dist_zero_right] using hn
  exact Set.Countable.mono hcover <|
    Set.countable_iUnion fun n =>
      (uniformlyDiscrete_finite_inter_closedBall hLambda (n : ℝ)).countable

theorem uniformlyDiscrete_unbounded_of_infinite {d : ℕ}
    {Lambda : Set (E d)}
    (hLambda : UniformlyDiscrete Lambda)
    (hLambda_inf : Lambda.Infinite) :
    ∀ R : ℝ, ∃ x ∈ Lambda, R < ‖x‖ := by
  intro R
  by_contra h
  push Not at h
  have hfinite_Lambda : Lambda.Finite := by
    refine (uniformlyDiscrete_finite_inter_closedBall hLambda R).subset ?_
    intro x hx
    exact ⟨hx, by simpa [Metric.mem_closedBall, dist_zero_right] using h x hx⟩
  exact hLambda_inf hfinite_Lambda

theorem exists_unlisted_point_outside_closedBall {d : ℕ}
    {Lambda : Set (E d)}
    (hLambda : UniformlyDiscrete Lambda)
    (hLambda_inf : Lambda.Infinite)
    (listed : Finset (E d)) (R : ℝ) :
    ∃ x ∈ Lambda, x ∉ listed ∧ x ∉ Metric.closedBall (0 : E d) R := by
  have hfinite_forbidden :
      ((listed : Set (E d)) ∪
        (Lambda ∩ Metric.closedBall (0 : E d) R)).Finite :=
    listed.finite_toSet.union (uniformlyDiscrete_finite_inter_closedBall hLambda R)
  obtain ⟨x, hxLambda, hx_not_forbidden⟩ :=
    hLambda_inf.exists_notMem_finite hfinite_forbidden
  refine ⟨x, hxLambda, ?_, ?_⟩
  · intro hx_listed
    exact hx_not_forbidden (Set.mem_union_left _ hx_listed)
  · intro hx_ball
    exact hx_not_forbidden
      (Set.mem_union_right _ ⟨hxLambda, hx_ball⟩)

private lemma eventually_notMem_finite_nat {s : Set ℕ} (hs : s.Finite) :
    ∀ᶠ n in atTop, n ∉ s := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp
  · obtain ⟨N, _hNs, hNmax⟩ := Set.exists_max_image s id hs hne
    rw [eventually_atTop]
    refine ⟨N + 1, fun n hn hns => ?_⟩
    have hn_le : n ≤ N := by
      simpa using hNmax n hns
    exact (Nat.not_lt_of_ge hn_le) (Nat.lt_of_succ_le hn)

private lemma tendsto_norm_atTop_of_injective_mem
    {d : ℕ} {Lambda : Set (E d)}
    (hLambda_finite_closedBall :
      ∀ R : ℝ, (Lambda ∩ Metric.closedBall (0 : E d) R).Finite)
    {lambda : ℕ → E d}
    (hlambda_inj : Function.Injective lambda)
    (hlambda_mem : ∀ n, lambda n ∈ Lambda) :
    Tendsto (fun n : ℕ => ‖lambda n‖) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro b
  let R : ℝ := max b 0
  have hpreimage_finite :
      {n : ℕ | lambda n ∈ Lambda ∩ Metric.closedBall (0 : E d) R}.Finite := by
    change (lambda ⁻¹' (Lambda ∩ Metric.closedBall (0 : E d) R)).Finite
    exact (hLambda_finite_closedBall R).preimage
      (fun n _ m _ hnm => hlambda_inj hnm)
  filter_upwards [eventually_notMem_finite_nat hpreimage_finite] with n hn
  by_contra hnb
  have hnorm_lt : ‖lambda n‖ < b := lt_of_not_ge hnb
  have hnorm_le_R : ‖lambda n‖ ≤ R :=
    hnorm_lt.le.trans (le_max_left b 0)
  have hball : lambda n ∈ Metric.closedBall (0 : E d) R := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm_le_R
  exact hn ⟨hlambda_mem n, hball⟩

theorem exists_escaping_enumeration {d : ℕ} {Lambda : Set (E d)}
    (hLambda : UniformlyDiscrete Lambda)
    (hLambda_inf : Lambda.Infinite) :
    ∃ lambda : ℕ → E d,
      Function.Injective lambda ∧
      (∀ n, lambda n ∈ Lambda) ∧
      (∀ x ∈ Lambda, ∃ n, lambda n = x) ∧
      Tendsto (fun n => ‖lambda n‖) atTop atTop := by
  letI : Countable Lambda := (uniformlyDiscrete_countable hLambda).to_subtype
  letI : Infinite Lambda := hLambda_inf.to_subtype
  letI : Denumerable Lambda := Classical.choice (nonempty_denumerable Lambda)
  let lambda : ℕ → E d := fun n => (Denumerable.ofNat Lambda n : E d)
  have hofNat_inj : Function.Injective (Denumerable.ofNat Lambda) := by
    intro n m hnm
    have henc := congrArg (fun x : Lambda => Encodable.encode x) hnm
    simpa using henc
  have hlambda_inj : Function.Injective lambda := by
    intro n m hnm
    apply hofNat_inj
    exact Subtype.ext (by simpa [lambda] using hnm)
  have hlambda_mem : ∀ n, lambda n ∈ Lambda := by
    intro n
    exact (Denumerable.ofNat Lambda n).property
  have hlambda_surj : ∀ x ∈ Lambda, ∃ n, lambda n = x := by
    intro x hx
    refine ⟨Encodable.encode (⟨x, hx⟩ : Lambda), ?_⟩
    simp [lambda]
  refine ⟨lambda, hlambda_inj, hlambda_mem, hlambda_surj, ?_⟩
  exact tendsto_norm_atTop_of_injective_mem
    (fun R => uniformlyDiscrete_finite_inter_closedBall hLambda R)
    hlambda_inj hlambda_mem

theorem correctionCompact_isCompact {d : ℕ}
    (lambda : ℕ → E d) (n : ℕ) :
    IsCompact (correctionCompact lambda n) := by
  by_cases hzero : lambda n = 0
  · simp [correctionCompact, hzero]
  · simpa [correctionCompact, hzero] using
      isCompact_closedBall (0 : E d) (correctionRadius lambda n)

theorem lambda_not_mem_correctionCompact {d : ℕ}
    (lambda : ℕ → E d) (n : ℕ) :
    lambda n ∉ correctionCompact lambda n := by
  intro hmem
  by_cases hzero : lambda n = 0
  · simp [correctionCompact, hzero] at hmem
  · have hnorm_le : ‖lambda n‖ ≤ correctionRadius lambda n := by
      simpa [correctionCompact, hzero, Metric.mem_closedBall, dist_zero_right]
        using hmem
    have hrad_le : correctionRadius lambda n ≤ ‖lambda n‖ / 2 := by
      exact min_le_right _ _
    have hnorm_pos : 0 < ‖lambda n‖ := norm_pos_iff.mpr hzero
    linarith

theorem correctionRadius_tendsto_atTop {d : ℕ} {lambda : ℕ → E d}
    (hlambda_escape : Tendsto (fun n => ‖lambda n‖) atTop atTop) :
    Tendsto (fun n => correctionRadius lambda n) atTop atTop := by
  have hleft : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ)
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hright : Tendsto (fun n : ℕ => ‖lambda n‖ / 2) atTop atTop :=
    Tendsto.atTop_div_const (show (0 : ℝ) < 2 by norm_num) hlambda_escape
  refine tendsto_atTop.2 ?_
  intro b
  filter_upwards [tendsto_atTop.1 hleft b, tendsto_atTop.1 hright b] with n hn_left hn_right
  exact le_min hn_left hn_right

theorem correctionCompact_eventually_contains_closedBall {d : ℕ}
    {lambda : ℕ → E d}
    (hlambda_escape : Tendsto (fun n => ‖lambda n‖) atTop atTop)
    (R : ℝ) :
    ∀ᶠ n in atTop,
      Metric.closedBall (0 : E d) R ⊆ correctionCompact lambda n := by
  have hrad :
      ∀ᶠ n in atTop, max R 0 < correctionRadius lambda n :=
    (correctionRadius_tendsto_atTop hlambda_escape).eventually_gt_atTop (max R 0)
  filter_upwards [hrad] with n hn x hx
  have hlambda_ne : lambda n ≠ 0 := by
    intro hzero
    have hrad_zero : correctionRadius lambda n = 0 := by
      have hnonneg : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
      rw [correctionRadius, hzero, norm_zero, zero_div, min_eq_right hnonneg]
    have hmax_nonneg : (0 : ℝ) ≤ max R 0 := le_max_right R 0
    linarith
  have hx_dist : dist x (0 : E d) ≤ R := by
    simpa [Metric.mem_closedBall] using hx
  have hx_dist_rad : dist x (0 : E d) ≤ correctionRadius lambda n :=
    hx_dist.trans ((le_max_left R 0).trans hn.le)
  simpa [correctionCompact, hlambda_ne, Metric.mem_closedBall] using hx_dist_rad

theorem correctionCompact_eventually_contains_compact {d : ℕ}
    {lambda : ℕ → E d}
    (hlambda_escape : Tendsto (fun n => ‖lambda n‖) atTop atTop)
    {K : Set (E d)} (hK : IsCompact K) :
    ∀ᶠ n in atTop, K ⊆ correctionCompact lambda n := by
  obtain ⟨R, _hR_pos, hR⟩ := hK.isBounded.exists_pos_norm_le
  filter_upwards [correctionCompact_eventually_contains_closedBall
      hlambda_escape R] with n hn x hxK
  exact hn (by simpa [Metric.mem_closedBall, dist_zero_right] using hR x hxK)

end SpectralGapsPrelim.HigherDim
