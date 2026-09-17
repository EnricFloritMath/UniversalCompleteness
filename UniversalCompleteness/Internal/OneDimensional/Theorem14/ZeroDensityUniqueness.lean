import Theorem14.Definitions
import Theorem14.FourierLaplace
import Theorem14.EntireCountingData
import Theorem12.FourierUniqueness
import Theorem12.GenericAuxiliary

/-! # Theorem 1.4: initial-arc zero-density uniqueness -/

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace Theorem14.Internal

/- Proof idea: continuous a.e.-zero implies pointwise zero. -/
private lemma exists_fourierCoeff_ne_zero_of_continuous_ne_zero
    {g : C(AddCircle (1 : ℝ), ℂ)} (hg : g ≠ 0) :
    ∃ m : ℤ, fourierCoeff g m ≠ 0 := by
  /- Proof idea: If every coefficient vanished, Fourier uniqueness gives Haar-a.e. zero. A continuous
  function nonzero at one point is nonzero on a nonempty open neighborhood of positive Haar
  measure, contradiction. -/
  classical
  by_contra hall
  push Not at hall
  have hgint : Integrable (g : AddCircle (1 : ℝ) → ℂ) AddCircle.haarAddCircle :=
    g.continuous.integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset isClosed_closure (Set.subset_univ _))
  have hae : (g : AddCircle (1 : ℝ) → ℂ) =ᵐ[AddCircle.haarAddCircle] 0 :=
    Theorem12.Generic.ae_eq_zero_of_all_fourierCoeff_eq_zero g hgint hall
  have hpoint : (g : AddCircle (1 : ℝ) → ℂ) = 0 :=
    (g.continuous.ae_eq_iff_eq AddCircle.haarAddCircle continuous_zero).mp hae
  apply hg
  ext x
  exact congrFun hpoint x

/- Proof idea: inject n ↦ n-m directly into positive divisor orders inside the caller's open disk. -/
private lemma symmetricFourierZeroCount_le_shifted_zeroCount
    (g : C(AddCircle (1 : ℝ), ℂ)) (m : ℤ)
    (D : EntireCountingData (shiftedFourierLaplace g m))
    (N : ℕ) (R : ℝ) (hR : (N : ℝ) + |(m : ℝ)| < R) :
    symmetricFourierZeroCount g N ≤
      Theorem12.Generic.zeroCount D.data R := by
  /- Proof idea: Continuous `g` is Haar-integrable, so `analyticOnNhd_fourierLaplace` makes its Fourier--Laplace transform entire
  and composition with `z↦z+m` makes the shift entire. Map each filtered integer `n` injectively
  to `((n-m:Int):Complex)`. `fourierLaplace_intCast` identifies it as a shifted-transform zero; entire
  analyticity plus the finite-order counting data makes its integer order at least one. The
  bound `‖n-m‖ <= N+|m| < R` places it directly in the radius-`R` open disk. Compare the
  filtered card with the positive-order sum. -/
  classical
  have hgint : Integrable (g : AddCircle (1 : ℝ) → ℂ) AddCircle.haarAddCircle :=
    g.continuous.integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset isClosed_closure (Set.subset_univ _))
  have hshiftAnalytic :
      AnalyticOnNhd ℂ (shiftedFourierLaplace g m) Set.univ := by
    intro z _
    change AnalyticAt ℂ (fun w : ℂ => fourierLaplace g (w + (m : ℂ))) z
    have haffine : AnalyticAt ℂ (fun w : ℂ => w + (m : ℂ)) z :=
      analyticAt_id.add analyticAt_const
    simpa only [Function.comp_def] using
      AnalyticAt.comp (f := fun w : ℂ => w + (m : ℂ))
        (analyticOnNhd_fourierLaplace hgint (z + (m : ℂ)) (Set.mem_univ _)) haffine
  let shiftEmbedding : ℤ ↪ ℂ :=
    ⟨fun n => ((n - m : ℤ) : ℂ), fun a b hab => by
      have hab' : a - m = b - m := Int.cast_injective hab
      omega⟩
  let K : Finset ℤ :=
    (Finset.Icc (-(N : ℤ)) (N : ℤ)).filter fun n => fourierCoeff g n = 0
  let Z : Finset ℂ := K.map shiftEmbedding
  let s : Finset ℂ := (D.data.finite_orderSupport_closedBall R).toFinset
  have hpoint (n : ℤ) (hnK : n ∈ K) :
      ‖shiftEmbedding n‖ < R ∧ 1 ≤ Int.toNat (D.data.order (shiftEmbedding n)) := by
    have hnIcc : n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) :=
      (Finset.mem_filter.mp hnK).1
    have hnzero : fourierCoeff g n = 0 := (Finset.mem_filter.mp hnK).2
    have hnabs : |n| ≤ (N : ℤ) := (abs_le).2 (by simpa using hnIcc)
    have hnnorm : ‖(n : ℂ)‖ ≤ (N : ℝ) := by
      simpa using (show (|n| : ℝ) ≤ (N : ℝ) by exact_mod_cast hnabs)
    have hnorm : ‖shiftEmbedding n‖ < R := by
      calc
        ‖shiftEmbedding n‖ = ‖(n : ℂ) - (m : ℂ)‖ := by
          simp [shiftEmbedding]
        _ ≤ ‖(n : ℂ)‖ + ‖(m : ℂ)‖ := norm_sub_le _ _
        _ ≤ (N : ℝ) + |(m : ℝ)| := by
          gcongr
          simp
        _ < R := hR
    have hvalue : shiftedFourierLaplace g m (shiftEmbedding n) = 0 := by
      rw [shiftedFourierLaplace]
      have harg : shiftEmbedding n + (m : ℂ) = (n : ℂ) := by
        simp [shiftEmbedding]
      rw [harg, fourierLaplace_intCast hgint n, hnzero]
    have horderNe : D.data.order (shiftEmbedding n) ≠ 0 := by
      intro hord
      have hanalyticOrder :
          analyticOrderAt (shiftedFourierLaplace g m) (shiftEmbedding n) = 0 := by
        rw [← ENat.map_natCast_eq_zero (α := ℤ)]
        rw [← (hshiftAnalytic (shiftEmbedding n) (Set.mem_univ _)).meromorphicOrderAt_eq,
          ← D.data.order_spec (shiftEmbedding n), hord]
        simp
      exact ((hshiftAnalytic (shiftEmbedding n) (Set.mem_univ _)).analyticOrderAt_eq_zero.mp
        hanalyticOrder) hvalue
    have horderPos : 0 < D.data.order (shiftEmbedding n) :=
      lt_of_le_of_ne (D.order_nonneg (shiftEmbedding n)) (Ne.symm horderNe)
    refine ⟨hnorm, ?_⟩
    omega
  have hZsub : Z ⊆ s := by
    intro z hz
    rcases Finset.mem_map.mp hz with ⟨n, hnK, rfl⟩
    apply (Set.Finite.mem_toFinset _).mpr
    refine ⟨?_, ?_⟩
    · intro hord
      have hmult := (hpoint n hnK).2
      simp [hord] at hmult
    · rw [Metric.mem_closedBall, dist_zero_right]
      exact (hpoint n hnK).1.le
  have hRpos : 0 < R := by
    have hnonneg : 0 ≤ (N : ℝ) + |(m : ℝ)| := by positivity
    exact hnonneg.trans_lt hR
  rw [Theorem12.Generic.zeroCount, if_neg (not_le.mpr hRpos)]
  change K.card ≤ ∑ z ∈ s, if ‖z‖ < R then Int.toNat (D.data.order z) else 0
  calc
    K.card = Z.card := by simp [Z]
    _ = ∑ _z ∈ Z, 1 := by simp
    _ ≤ ∑ z ∈ Z, if ‖z‖ < R then Int.toNat (D.data.order z) else 0 := by
      apply Finset.sum_le_sum
      intro z hz
      rcases Finset.mem_map.mp hz with ⟨n, hnK, rfl⟩
      rw [if_pos (hpoint n hnK).1]
      exact (hpoint n hnK).2
    _ ≤ ∑ z ∈ s, if ‖z‖ < R then Int.toNat (D.data.order z) else 0 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hZsub
      intro z hz hzZ
      exact Nat.zero_le _

/- Proof idea: split eta≥sigma; otherwise apply the finite injection at the final radius itself. -/
private theorem shiftedFourierLaplace_zeroCount_lowerDensity
    {g : C(AddCircle (1 : ℝ), ℂ)} {m : ℤ} {sigma : ℝ}
    (D : EntireCountingData (shiftedFourierLaplace g m))
    (hsigma : 0 < sigma)
    (hden : HasEventuallySymmetricFourierZeroDensity g sigma) :
    ∀ eta > 0, ∀ᶠ r : ℝ in atTop,
      2 * (sigma - eta) * r ≤
        (Theorem12.Generic.zeroCount D.data r : ℝ) := by
  /- Proof idea: Split on `eta>=sigma`; the nonpositive branch follows from zero-count nonnegativity.
  Otherwise, for large `r`, choose `N=Nat.floor (r-|m|-1)`, prove `(N:Real)+|m|<r`, invoke
  `symmetricFourierZeroCount_le_shifted_zeroCount` directly with radius `r`, apply the eventual symmetric-density inequality, expand
  `2*N+1`, and absorb the fixed floor/shift loss into `eta*r`. -/
  intro eta heta
  by_cases hetaSigma : sigma ≤ eta
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
    have hlhs : 2 * (sigma - eta) * r ≤ 0 := by
      have : sigma - eta ≤ 0 := sub_nonpos.mpr hetaSigma
      nlinarith
    exact hlhs.trans (Nat.cast_nonneg _)
  · change ∀ᶠ N : ℕ in atTop,
      sigma * (2 * (N : ℝ) + 1) ≤ (symmetricFourierZeroCount g N : ℝ) at hden
    obtain ⟨N0, hN0⟩ := eventually_atTop.1 hden
    let M : ℝ := |(m : ℝ)|
    let T : ℝ := max ((N0 : ℝ) + M + 1)
      (sigma * (2 * M + 3) / (2 * eta))
    filter_upwards [eventually_ge_atTop T] with r hr
    let N : ℕ := ⌊r - M - 1⌋₊
    have hN0real : (N0 : ℝ) ≤ r - M - 1 := by
      have hleft : (N0 : ℝ) + M + 1 ≤ T := le_max_left _ _
      exact_mod_cast (show (N0 : ℝ) ≤ r - M - 1 by linarith [hleft.trans hr])
    have hxnonneg : 0 ≤ r - M - 1 := (Nat.cast_nonneg N0).trans hN0real
    have hN0N : N0 ≤ N := by
      dsimp only [N]
      exact Nat.le_floor hN0real
    have hdenN := hN0 N hN0N
    have hfloorLe : (N : ℝ) ≤ r - M - 1 := by
      dsimp only [N]
      exact Nat.floor_le hxnonneg
    have hNR : (N : ℝ) + |(m : ℝ)| < r := by
      dsimp only [M] at hfloorLe
      linarith
    have hinj := symmetricFourierZeroCount_le_shifted_zeroCount g m D N r hNR
    have hinjReal : (symmetricFourierZeroCount g N : ℝ) ≤
        (Theorem12.Generic.zeroCount D.data r : ℝ) := by
      exact_mod_cast hinj
    have hcount : sigma * (2 * (N : ℝ) + 1) ≤
        (Theorem12.Generic.zeroCount D.data r : ℝ) := hdenN.trans hinjReal
    have hfloorLower : r - M - 1 < (N : ℝ) + 1 := by
      dsimp only [N]
      exact Nat.lt_floor_add_one _
    have hquot : sigma * (2 * M + 3) / (2 * eta) ≤ r := by
      have hright : sigma * (2 * M + 3) / (2 * eta) ≤ T := le_max_right _ _
      exact hright.trans hr
    have heta2 : 0 < 2 * eta := by positivity
    have hfixed : sigma * (2 * M + 3) ≤ 2 * eta * r := by
      simpa [mul_comm] using (div_le_iff₀ heta2).mp hquot
    have hlower : 2 * (sigma - eta) * r ≤ sigma * (2 * (N : ℝ) + 1) := by
      nlinarith
    exact hlower.trans hcount

/- Proof idea: choose one shift, one counting witness, and clean radii; Jensen gives sigma≤L. -/
theorem bandlimited_zeroDensity_uniqueness
    (g : C(AddCircle (1 : ℝ), ℂ)) {L sigma : ℝ}
    (hL0 : 0 ≤ L) (hL1 : L < 1)
    (hsupp : SupportedInInitialArc g L) (hLsigma : L < sigma)
    (hden : HasEventuallySymmetricFourierZeroDensity g sigma) :
    g = 0 := by
  /- Proof idea: Assume `g!=0`; choose `m` by `exists_fourierCoeff_ne_zero_of_continuous_ne_zero` and set `F=shiftedFourierLaplace g m`. `analyticOnNhd_fourierLaplace`
  gives entire analyticity and `fourierCoeff g m!=0` gives `F 0!=0`; construct exactly one `D`
  by `exists_entireCountingData` and one `CleanRadii F` from that same `D`. Derive `0<sigma` from `0<=L<sigma`.
  Along the clean radii use `circleLogMean_shiftedFourierLaplace_le_of_clean`; the constant `log(max 1 ‖g‖_1)` divided by radii tends
  to zero. Use `shiftedFourierLaplace_zeroCount_lowerDensity` for zero density and `D.poleCount_eq_zero` for `rho=0`. Invoke Jensen
  with `tau=L`, obtaining `sigma<=L`, contradiction. -/
  classical
  by_contra hg
  obtain ⟨m, hm⟩ := exists_fourierCoeff_ne_zero_of_continuous_ne_zero hg
  have hgint : Integrable (g : AddCircle (1 : ℝ) → ℂ) AddCircle.haarAddCircle :=
    g.continuous.integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset isClosed_closure (Set.subset_univ _))
  let F : ℂ → ℂ := shiftedFourierLaplace g m
  have hFanalytic : AnalyticOnNhd ℂ F Set.univ := by
    intro z _
    change AnalyticAt ℂ (fun w : ℂ => fourierLaplace g (w + (m : ℂ))) z
    have haffine : AnalyticAt ℂ (fun w : ℂ => w + (m : ℂ)) z :=
      analyticAt_id.add analyticAt_const
    simpa only [Function.comp_def] using
      AnalyticAt.comp (f := fun w : ℂ => w + (m : ℂ))
        (analyticOnNhd_fourierLaplace hgint (z + (m : ℂ)) (Set.mem_univ _)) haffine
  have hFm : fourierLaplace g (m : ℂ) ≠ 0 := by
    rw [fourierLaplace_intCast hgint m]
    exact hm
  have hF0 : F 0 ≠ 0 := by
    simpa [F, shiftedFourierLaplace] using hFm
  let D : EntireCountingData F :=
    Classical.choice (exists_entireCountingData hFanalytic hF0)
  let C : CleanRadii F := Classical.choice (exists_cleanRadii hFanalytic D)
  have hRpos (j : ℕ) : 0 < C.radius j := by
    have hj0 : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith [C.lower j]
  have hRtendsto : Tendsto C.radius atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    obtain ⟨N : ℕ, hN : b < N⟩ := exists_nat_gt b
    refine ⟨N, fun n hn => ?_⟩
    have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith [C.lower n]
  let b : ℕ → ℝ := fun _ =>
    Real.log (max 1 (∫ x, ‖g x‖ ∂AddCircle.haarAddCircle))
  have hb : Tendsto (fun j => b j / C.radius j) atTop (nhds 0) := by
    exact hRtendsto.const_div_atTop
      (Real.log (max 1 (∫ x, ‖g x‖ ∂AddCircle.haarAddCircle)))
  have hboundary : ∀ᶠ j : ℕ in atTop,
      Theorem12.Generic.circleLogMean F (C.radius j) ≤
        2 * L * C.radius j + b j := by
    filter_upwards with j
    dsimp only [F, b]
    exact circleLogMean_shiftedFourierLaplace_le_of_clean hgint hsupp hL0 (hRpos j)
      (fun z hz => (C.clean j z hz).2)
  have hsigma : 0 < sigma := hL0.trans_lt hLsigma
  have hzero : ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ r : ℝ in atTop,
      2 * (sigma - epsilon) * r ≤
        (Theorem12.Generic.zeroCount D.data r : ℝ) :=
    shiftedFourierLaplace_zeroCount_lowerDensity D hsigma hden
  have hpole : ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ r : ℝ in atTop,
      (Theorem12.Generic.poleCount D.data r : ℝ) ≤
        2 * ((0 : ℝ) + epsilon) * r := by
    intro epsilon hepsilon
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
    rw [D.poleCount_eq_zero]
    simpa using
      (mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hepsilon.le) hr)
  have hjensen := Theorem12.Generic.jensen_density_comparison F D.data
    (hFanalytic 0 (Set.mem_univ 0)) hF0 C.radius hRpos hRtendsto C.clean
    sigma 0 L b hb hboundary hzero hpole
  linarith

end Theorem14.Internal
