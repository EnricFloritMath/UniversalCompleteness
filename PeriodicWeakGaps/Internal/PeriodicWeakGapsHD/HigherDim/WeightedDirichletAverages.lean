import Mathlib.NumberTheory.Harmonic.Bounds
import PeriodicWeakGapsHD.HigherDim.PositiveBoxPolynomials

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Topology ENNReal FourierTransform

namespace SpectralGapsPrelim.HigherDim

/-!
Weighted positive-box Dirichlet averages and compact-away-from-lattice decay.
-/

theorem a_pos {d : ℕ} (_halpha : AlphaLeDimHalf d alpha)
    (k : Fin d → ℕ) :
    0 < a alpha k := by
  unfold a
  exact one_div_pos.mpr (sobolevWeight_pos alpha (natVec k))

private lemma a_nonneg {d : ℕ} (halpha : AlphaLeDimHalf d alpha)
    (k : Fin d → ℕ) :
    0 ≤ a alpha k :=
  (a_pos halpha k).le

theorem B_pos {d N : ℕ}
    (halpha : AlphaLeDimHalf d alpha) (hN : 1 ≤ N) :
    0 < B d alpha N := by
  unfold B
  exact Finset.sum_pos
    (fun k _ => a_pos halpha k)
    (indexBox_nonempty hN)

theorem c_nonneg {d N : ℕ}
    (halpha : AlphaLeDimHalf d alpha)
    (k : Fin d → ℕ) :
    0 ≤ c alpha N k := by
  unfold c
  split_ifs with hk
  · exact div_nonneg (a_nonneg halpha k)
      (Finset.sum_pos (fun l _ => a_pos halpha l) ⟨k, hk⟩).le
  · exact le_rfl

private lemma norm_ofReal_c {d N : ℕ}
    (halpha : AlphaLeDimHalf d alpha)
    (k : Fin d → ℕ) :
    ‖((c alpha N k : ℝ) : ℂ)‖ = c alpha N k := by
  rw [← Real.norm_of_nonneg (c_nonneg halpha k)]
  norm_num

theorem sum_c_eq_one {d N : ℕ}
    (halpha : AlphaLeDimHalf d alpha) (hN : 1 ≤ N) :
    (indexBox d N).sum (fun k => c alpha N k) = 1 := by
  have hB : B d alpha N ≠ 0 := (B_pos halpha hN).ne'
  calc
    (indexBox d N).sum (fun k => c alpha N k)
        = (indexBox d N).sum (fun k => a alpha k / B d alpha N) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          simp [c, hk]
    _ = B d alpha N / B d alpha N := by
          rw [← Finset.sum_div]
          rfl
    _ = 1 := div_self hB

theorem sum_c_complex_eq_one {d N : ℕ}
    (halpha : AlphaLeDimHalf d alpha) (hN : 1 ≤ N) :
    (indexBox d N).sum (fun k => ((c alpha N k : ℝ) : ℂ)) = 1 := by
  exact_mod_cast sum_c_eq_one halpha hN

theorem Q_zero {d N : ℕ}
    (halpha : AlphaLeDimHalf d alpha) (hN : 1 ≤ N) :
    Q (d := d) alpha N 0 = 1 := by
  simpa [Q] using
    (coeffPolynomial_zero (d := d) (N := N)
      (b := fun k => ((c alpha N k : ℝ) : ℂ))
      (sum_c_complex_eq_one halpha hN))

theorem Q_norm_le_one {d N : ℕ}
    (halpha : AlphaLeDimHalf d alpha) (hN : 1 ≤ N)
    (u : E d) :
    ‖Q (d := d) alpha N u‖ ≤ 1 := by
  calc
    ‖Q (d := d) alpha N u‖
        ≤ (indexBox d N).sum
            (fun k => ‖((c alpha N k : ℝ) : ℂ)‖) := by
          simpa [Q] using
            (coeffPolynomial_norm_le_sum_norm
              (d := d) (N := N)
              (b := fun k => ((c alpha N k : ℝ) : ℂ)) u)
    _ = (indexBox d N).sum (fun k => c alpha N k) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          exact norm_ofReal_c halpha k
    _ = 1 := by
          rw [sum_c_eq_one halpha hN]

theorem B_lower_bound_subcritical {d : ℕ} (hd_pos : 0 < d)
    (halpha : AlphaLeDimHalf d alpha)
    (_hsub : 2 * alpha < (d : ℝ)) :
    ∃ C : ℝ, 0 < C ∧
      Filter.Eventually
        (fun N : ℕ =>
          C * Real.rpow (N : ℝ) ((d : ℝ) - 2 * alpha)
            ≤ B d alpha N)
        atTop := by
  classical
  let C : ℝ := (2 * Real.rpow (Real.sqrt (d : ℝ)) (2 * alpha))⁻¹
  have hd_real_pos : 0 < (d : ℝ) := by exact_mod_cast hd_pos
  have hsqrt_pos : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 hd_real_pos
  have hpow_sqrt_pos :
      0 < Real.rpow (Real.sqrt (d : ℝ)) (2 * alpha) :=
    Real.rpow_pos_of_pos hsqrt_pos _
  have hCpos : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hCpos, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with N hN
  have hN_real_pos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hN_real_nonneg : 0 ≤ (N : ℝ) := hN_real_pos.le
  have hN_real_ge_one : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  let L : ℝ :=
    (2 * Real.rpow (Real.sqrt (d : ℝ) * (N : ℝ)) (2 * alpha))⁻¹
  have hterm : ∀ k ∈ indexBox d N, L ≤ a alpha k := by
    intro k hk
    have hnorm_le := norm_natVec_le_sqrt_d_mul_N (d := d) (N := N) (k := k) hk
    have hnorm_nonneg : 0 ≤ ‖natVec k‖ := norm_nonneg _
    have hexp_nonneg : 0 ≤ 2 * alpha := by linarith [halpha.nonneg]
    have hpower_le :
        sobolevPower alpha (natVec k) ≤
          Real.rpow (Real.sqrt (d : ℝ) * (N : ℝ)) (2 * alpha) := by
      by_cases ha0 : alpha = 0
      · simp [sobolevPower, ha0]
      · simp [sobolevPower, ha0]
        exact Real.rpow_le_rpow hnorm_nonneg hnorm_le hexp_nonneg
    have hweight_le :
        sobolevWeight alpha (natVec k) ≤
          2 * Real.rpow (Real.sqrt (d : ℝ) * (N : ℝ)) (2 * alpha) := by
      unfold sobolevWeight
      have hone_le_power :
          1 ≤ Real.rpow (Real.sqrt (d : ℝ) * (N : ℝ)) (2 * alpha) := by
        have hbase_ge_one : 1 ≤ Real.sqrt (d : ℝ) * (N : ℝ) := by
          have hsqrt_ge_one : 1 ≤ Real.sqrt (d : ℝ) := by
            rw [← (sq_le_sq₀ zero_le_one hsqrt_pos.le),
              Real.sq_sqrt hd_real_pos.le]
            exact_mod_cast hd_pos
          nlinarith
        exact Real.one_le_rpow hbase_ge_one hexp_nonneg
      linarith
    have hden_pos : 0 < sobolevWeight alpha (natVec k) :=
      sobolevWeight_pos alpha (natVec k)
    unfold a
    dsimp [L]
    simpa [one_div] using one_div_le_one_div_of_le hden_pos hweight_le
  have hsum_lower :
      (indexBox d N).sum (fun _k => L) ≤ B d alpha N := by
    unfold B
    exact Finset.sum_le_sum hterm
  have hsum_eval :
      (indexBox d N).sum (fun _k => L) = (N : ℝ) ^ d * L := by
    rw [Finset.sum_const, card_indexBox, nsmul_eq_mul]
    norm_num
  have hbox_lower :
      (N : ℝ) ^ d * L =
        C * Real.rpow (N : ℝ) ((d : ℝ) - 2 * alpha) := by
    dsimp [L, C]
    rw [Real.mul_rpow hsqrt_pos.le hN_real_nonneg]
    rw [← Real.rpow_natCast (N : ℝ) d]
    rw [Real.rpow_sub hN_real_pos (d : ℝ) (2 * alpha)]
    field_simp [hN_real_pos.ne', hpow_sqrt_pos.ne']
  calc
    C * Real.rpow (N : ℝ) ((d : ℝ) - 2 * alpha)
        = (indexBox d N).sum (fun _k => L) := by
          rw [hsum_eval, hbox_lower]
    _ ≤ B d alpha N := hsum_lower

theorem B_lower_bound_critical {d : ℕ} (hd_pos : 0 < d)
    (halpha : AlphaLeDimHalf d alpha)
    (hcrit : 2 * alpha = (d : ℝ)) :
    ∃ C : ℝ, 0 < C ∧
      Filter.Eventually
        (fun N : ℕ =>
          C * Real.log ((N : ℝ) + 1) ≤ B d alpha N)
        atTop := by
  classical
  cases d with
  | zero => omega
  | succ n =>
      let d' : ℕ := n + 1
      let C : ℝ := (2 * Real.rpow (Real.sqrt (d' : ℝ)) (d' : ℝ))⁻¹
      have hd'_pos : 0 < d' := Nat.succ_pos n
      have hd'_real_pos : 0 < (d' : ℝ) := by exact_mod_cast hd'_pos
      have hsqrt_pos : 0 < Real.sqrt (d' : ℝ) :=
        Real.sqrt_pos.2 hd'_real_pos
      have hpow_sqrt_pos :
          0 < Real.rpow (Real.sqrt (d' : ℝ)) (d' : ℝ) :=
        Real.rpow_pos_of_pos hsqrt_pos _
      have hCpos : 0 < C := by
        dsimp [C]
        positivity
      refine ⟨C, hCpos, ?_⟩
      filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with N hN
      let domain : Finset (Σ _m : ℕ, Fin n → ℕ) :=
        (Finset.Icc 1 N).sigma (fun m => indexBox n m)
      let embed : (Σ _m : ℕ, Fin n → ℕ) → (Fin (n + 1) → ℕ) :=
        fun p => Fin.cons p.1 p.2
      let image : Finset (Fin (n + 1) → ℕ) := domain.image embed
      have hembed_inj : Set.InjOn embed ↑domain := by
        intro p hp q hq hpq
        cases p with
        | mk m v =>
            cases q with
            | mk l w =>
                dsimp [embed] at hpq ⊢
                have hml : m = l := congrFun hpq 0
                subst l
                have hvw : v = w := by
                  have htail := congrArg Fin.tail hpq
                  simpa using htail
                subst w
                rfl
      have himage_subset : image ⊆ indexBox (n + 1) N := by
        intro k hk
        rcases Finset.mem_image.mp hk with ⟨p, hp, rfl⟩
        rcases Finset.mem_sigma.mp hp with ⟨hmIcc, hvbox⟩
        rcases Finset.mem_Icc.mp hmIcc with ⟨hm1, hmN⟩
        have hvcoord := (indexBox_mem_iff (d := n) (N := p.1) p.2).1 hvbox
        rw [indexBox_mem_iff]
        intro i
        cases i using Fin.cases with
        | zero =>
            simp [embed, Fin.cons_zero, hm1, hmN]
        | succ j =>
            have hj := hvcoord j
            exact ⟨by simpa [embed] using hj.1,
              by exact_mod_cast (le_trans hj.2 hmN)⟩
      have hsum_image_le_B :
          image.sum (fun k => a alpha k) ≤ B (n + 1) alpha N := by
        unfold B
        exact Finset.sum_le_sum_of_subset_of_nonneg himage_subset
          (fun k _ _ => a_nonneg halpha k)
      have hsum_image_eq :
          image.sum (fun k => a alpha k) =
            domain.sum (fun p => a alpha (embed p)) := by
        dsimp [image]
        exact Finset.sum_image hembed_inj
      have hterm_lower :
          ∀ p ∈ domain,
            C / ((p.1 : ℝ) ^ (n + 1)) ≤ a alpha (embed p) := by
        intro p hp
        rcases Finset.mem_sigma.mp hp with ⟨hmIcc, hvbox⟩
        rcases Finset.mem_Icc.mp hmIcc with ⟨hm1, _hmN⟩
        have hm_real_pos : 0 < (p.1 : ℝ) := by exact_mod_cast hm1
        have hm_real_nonneg : 0 ≤ (p.1 : ℝ) := hm_real_pos.le
        have hm_real_ge_one : 1 ≤ (p.1 : ℝ) := by exact_mod_cast hm1
        have hk_m : embed p ∈ indexBox (n + 1) p.1 := by
          have hvcoord := (indexBox_mem_iff (d := n) (N := p.1) p.2).1 hvbox
          rw [indexBox_mem_iff]
          intro i
          cases i using Fin.cases with
          | zero =>
              exact ⟨hm1, le_rfl⟩
          | succ j =>
              exact ⟨by simpa [embed] using (hvcoord j).1,
                by simpa [embed] using (hvcoord j).2⟩
        let L : ℝ :=
          (2 * Real.rpow (Real.sqrt (d' : ℝ) * (p.1 : ℝ)) (2 * alpha))⁻¹
        have hL_le_a : L ≤ a alpha (embed p) := by
          have hnorm_le :=
            norm_natVec_le_sqrt_d_mul_N
              (d := n + 1) (N := p.1) (k := embed p) hk_m
          have hnorm_nonneg : 0 ≤ ‖natVec (embed p)‖ := norm_nonneg _
          have hexp_nonneg : 0 ≤ 2 * alpha := by
            rw [hcrit]
            exact Nat.cast_nonneg _
          have hpower_le :
              sobolevPower alpha (natVec (embed p)) ≤
                Real.rpow (Real.sqrt (d' : ℝ) * (p.1 : ℝ)) (2 * alpha) := by
            by_cases ha0 : alpha = 0
            · simp [sobolevPower, ha0]
            · simp [sobolevPower, ha0]
              exact Real.rpow_le_rpow hnorm_nonneg hnorm_le hexp_nonneg
          have hweight_le :
              sobolevWeight alpha (natVec (embed p)) ≤
                2 * Real.rpow (Real.sqrt (d' : ℝ) * (p.1 : ℝ)) (2 * alpha) := by
            unfold sobolevWeight
            have hone_le_power :
                1 ≤ Real.rpow (Real.sqrt (d' : ℝ) * (p.1 : ℝ)) (2 * alpha) := by
              have hbase_ge_one : 1 ≤ Real.sqrt (d' : ℝ) * (p.1 : ℝ) := by
                have hsqrt_ge_one : 1 ≤ Real.sqrt (d' : ℝ) := by
                  rw [← (sq_le_sq₀ zero_le_one hsqrt_pos.le),
                    Real.sq_sqrt hd'_real_pos.le]
                  exact_mod_cast hd'_pos
                nlinarith
              exact Real.one_le_rpow hbase_ge_one hexp_nonneg
            linarith
          have hden_pos : 0 < sobolevWeight alpha (natVec (embed p)) :=
            sobolevWeight_pos alpha (natVec (embed p))
          unfold a
          dsimp [L]
          simpa [one_div] using one_div_le_one_div_of_le hden_pos hweight_le
        have hL_eq : L = C / ((p.1 : ℝ) ^ (n + 1)) := by
          dsimp [L, C, d']
          rw [hcrit]
          rw [Real.mul_rpow hsqrt_pos.le hm_real_nonneg]
          rw [Real.rpow_natCast]
          field_simp [hm_real_pos.ne', hpow_sqrt_pos.ne']
          rw [Real.rpow_natCast]
        exact hL_eq ▸ hL_le_a
      have hdomain_lower :
          domain.sum (fun p => C / ((p.1 : ℝ) ^ (n + 1))) ≤
            domain.sum (fun p => a alpha (embed p)) :=
        Finset.sum_le_sum hterm_lower
      have hdomain_eval :
          domain.sum (fun p => C / ((p.1 : ℝ) ^ (n + 1))) =
            C * (Finset.Icc 1 N).sum (fun m : ℕ => 1 / (m : ℝ)) := by
        calc
          domain.sum (fun p => C / ((p.1 : ℝ) ^ (n + 1)))
              =
            (Finset.Icc 1 N).sum
              (fun m : ℕ =>
                (indexBox n m).sum
                  (fun _v : Fin n → ℕ => C / ((m : ℝ) ^ (n + 1)))) := by
              dsimp [domain]
              rw [Finset.sum_sigma]
          _ = (Finset.Icc 1 N).sum
              (fun m : ℕ => ((m : ℝ) ^ n) * (C / ((m : ℝ) ^ (n + 1)))) := by
              refine Finset.sum_congr rfl ?_
              intro m hm
              rw [Finset.sum_const, card_indexBox, nsmul_eq_mul]
              norm_cast
          _ = (Finset.Icc 1 N).sum (fun m : ℕ => C * (1 / (m : ℝ))) := by
              refine Finset.sum_congr rfl ?_
              intro m hm
              rcases Finset.mem_Icc.mp hm with ⟨hm1, _hmN⟩
              have hm_pos : (m : ℝ) ≠ 0 := by
                exact_mod_cast (ne_of_gt hm1)
              field_simp [hm_pos]
              ring
          _ = C * (Finset.Icc 1 N).sum (fun m : ℕ => 1 / (m : ℝ)) := by
              rw [Finset.mul_sum]
      have hlog_le_harm :
          Real.log ((N : ℝ) + 1) ≤
            (Finset.Icc 1 N).sum (fun m : ℕ => 1 / (m : ℝ)) := by
        have h := log_add_one_le_harmonic N
        rw [harmonic_eq_sum_Icc] at h
        simpa [Nat.cast_add, Nat.cast_one, one_div] using h
      calc
        C * Real.log ((N : ℝ) + 1)
            ≤ C * (Finset.Icc 1 N).sum (fun m : ℕ => 1 / (m : ℝ)) :=
              mul_le_mul_of_nonneg_left hlog_le_harm hCpos.le
        _ = domain.sum (fun p => C / ((p.1 : ℝ) ^ (n + 1))) := hdomain_eval.symm
        _ ≤ domain.sum (fun p => a alpha (embed p)) := hdomain_lower
        _ = image.sum (fun k => a alpha k) := hsum_image_eq.symm
        _ ≤ B (n + 1) alpha N := hsum_image_le_B

theorem B_tendsto_atTop {d : ℕ} (hd_pos : 0 < d)
    (halpha : AlphaLeDimHalf d alpha) :
    Tendsto (fun N => B d alpha N) atTop atTop := by
  rcases lt_or_eq_of_le halpha.le_dim with hsub | hcrit
  · rcases B_lower_bound_subcritical hd_pos halpha hsub with ⟨C, hCpos, hC⟩
    have hp_pos : 0 < (d : ℝ) - 2 * alpha := sub_pos.mpr hsub
    have hpow :
        Tendsto
          (fun N : ℕ => Real.rpow (N : ℝ) ((d : ℝ) - 2 * alpha))
          atTop atTop :=
      (tendsto_rpow_atTop hp_pos).comp tendsto_natCast_atTop_atTop
    have hscaled :
        Tendsto
          (fun N : ℕ => C * Real.rpow (N : ℝ) ((d : ℝ) - 2 * alpha))
          atTop atTop :=
      hpow.const_mul_atTop hCpos
    exact tendsto_atTop_mono' atTop hC hscaled
  · rcases B_lower_bound_critical hd_pos halpha hcrit with ⟨C, hCpos, hC⟩
    have hlog :
        Tendsto (fun N : ℕ => Real.log ((N : ℝ) + 1)) atTop atTop := by
      exact Real.tendsto_log_atTop.comp
        (tendsto_atTop_add_const_right atTop (1 : ℝ)
          tendsto_natCast_atTop_atTop)
    have hscaled :
        Tendsto (fun N : ℕ => C * Real.log ((N : ℝ) + 1)) atTop atTop :=
      hlog.const_mul_atTop hCpos
    exact tendsto_atTop_mono' atTop hC hscaled

theorem weighted_coeff_energy_eq_inv_B {d N : ℕ}
    (halpha : AlphaLeDimHalf d alpha) (hN : 1 ≤ N) :
    (indexBox d N).sum
      (fun k =>
        sobolevWeight alpha (natVec k) * (c alpha N k)^2)
      = 1 / B d alpha N := by
  have hB : B d alpha N ≠ 0 := (B_pos halpha hN).ne'
  calc
    (indexBox d N).sum
      (fun k =>
        sobolevWeight alpha (natVec k) * (c alpha N k)^2)
        = (indexBox d N).sum
            (fun k => a alpha k / (B d alpha N)^2) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          have hW : sobolevWeight alpha (natVec k) ≠ 0 :=
            (sobolevWeight_pos alpha (natVec k)).ne'
          have hc : c alpha N k = a alpha k / B d alpha N := by
            simp [c, hk]
          rw [hc]
          unfold a
          field_simp [hW, hB]
    _ = B d alpha N / (B d alpha N)^2 := by
          rw [← Finset.sum_div]
          rfl
    _ = 1 / B d alpha N := by
          field_simp [hB]

theorem weighted_coeff_energy_tendsto_zero {d : ℕ} (hd_pos : 0 < d)
    (halpha : AlphaLeDimHalf d alpha) :
    Tendsto
      (fun N =>
        (indexBox d N).sum
          (fun k =>
            sobolevWeight alpha (natVec k) * (c alpha N k)^2))
      atTop (nhds 0) := by
  have h_inv :
      Tendsto (fun N : ℕ => (B d alpha N)⁻¹) atTop (nhds 0) :=
    Filter.Tendsto.inv_tendsto_atTop (B_tendsto_atTop hd_pos halpha)
  refine Filter.Tendsto.congr' ?_ h_inv
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with N hN
  rw [weighted_coeff_energy_eq_inv_B halpha hN]
  exact (one_div (B d alpha N)).symm

theorem compact_pos_dist_to_integerLattice {d : ℕ} (_hd_pos : 0 < d)
    {K : Set (E d)}
    (hK : IsCompact K)
    (hK_away : ∀ u ∈ K, u ∉ integerLattice d) :
    ∃ rho : ℝ, 0 < rho ∧
      ∀ u ∈ K, ∀ z ∈ integerLattice d, rho ≤ dist u z := by
  have hdisj : Disjoint K (integerLattice d) := by
    rw [Set.disjoint_left]
    intro u huK huL
    exact hK_away u huK huL
  rcases Metric.exists_pos_forall_lt_edist hK (integerLattice_closed d) hdisj with
    ⟨r, hrpos, hr⟩
  refine ⟨(r : ℝ) / 2, half_pos (NNReal.coe_pos.mpr hrpos), ?_⟩
  intro u huK z hz
  have hlt_edist : (r : ℝ≥0∞) < edist u z := hr u huK z hz
  have hlt_ofReal :
      ENNReal.ofReal (r : ℝ) < ENNReal.ofReal (dist u z) := by
    simpa [edist_dist] using hlt_edist
  have hlt_dist : (r : ℝ) < dist u z :=
    (ENNReal.ofReal_lt_ofReal_iff'.mp hlt_ofReal).1
  linarith

theorem exists_coordinate_away_from_int {d : ℕ} (hd_pos : 0 < d)
    {rho : ℝ} (hrho : 0 < rho)
    {u : E d}
    (hu : ∀ z ∈ integerLattice d, rho ≤ dist u z) :
    ∃ i : Fin d, ∀ m : ℤ,
      rho / (2 * Real.sqrt (d : ℝ)) ≤ |coord u i - (m : ℝ)| := by
  classical
  let delta : ℝ := rho / (2 * Real.sqrt (d : ℝ))
  have hd_real_pos : 0 < (d : ℝ) := by exact_mod_cast hd_pos
  have hsqrtd_pos : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 hd_real_pos
  have hdelta_pos : 0 < delta :=
    div_pos hrho (mul_pos (by norm_num) hsqrtd_pos)
  by_contra h
  push Not at h
  choose z hz using h
  have hcoord_le : ∀ i : Fin d, ‖coord (u - intVec z) i‖ ≤ delta := by
    intro i
    rw [Real.norm_eq_abs]
    change |coord u i - (z i : ℝ)| ≤ delta
    exact (hz i).le
  have hsum_le :
      (∑ i : Fin d, ‖coord (u - intVec z) i‖ ^ 2) ≤
        ∑ _i : Fin d, delta ^ 2 := by
    refine Finset.sum_le_sum ?_
    intro i hi
    exact pow_le_pow_left₀ (norm_nonneg _) (hcoord_le i) 2
  have hnorm_le : ‖u - intVec z‖ ≤ Real.sqrt (d : ℝ) * delta := by
    calc
      ‖u - intVec z‖
          = Real.sqrt
              (∑ i : Fin d, ‖coord (u - intVec z) i‖ ^ 2) := by
            simp [coord, PiLp.norm_eq_of_L2]
      _ ≤ Real.sqrt (∑ _i : Fin d, delta ^ 2) :=
            Real.sqrt_le_sqrt hsum_le
      _ = Real.sqrt (d : ℝ) * delta := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul]
            rw [Real.sqrt_mul (Nat.cast_nonneg d)]
            rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hdelta_pos.le]
  have hprod : Real.sqrt (d : ℝ) * delta = rho / 2 := by
    dsimp [delta]
    field_simp [hsqrtd_pos.ne']
  have hdist_lt : dist u (intVec z) < rho := by
    calc
      dist u (intVec z) = ‖u - intVec z‖ := dist_eq_norm u (intVec z)
      _ ≤ Real.sqrt (d : ℝ) * delta := hnorm_le
      _ = rho / 2 := hprod
      _ < rho := by linarith
  exact (not_le_of_gt hdist_lt) (hu (intVec z) ⟨z, rfl⟩)

private lemma exp2piI_ne_one_of_not_int
    {u : ℝ} (hnot : ∀ z : ℤ, u ≠ (z : ℝ)) :
    exp2piI u ≠ 1 := by
  intro hu
  unfold exp2piI at hu
  rcases Complex.exp_eq_one_iff.mp hu with ⟨m, hm⟩
  have him := congrArg Complex.im hm
  simp [Complex.mul_im, Complex.ofReal_mul, mul_comm, mul_left_comm] at him
  have htwo_pi_pos : 0 < (2 * Real.pi : ℝ) := by positivity
  have hu_eq : u = (m : ℝ) := by
    nlinarith
  exact hnot m hu_eq

private lemma exp2piI_nat_mul (k : ℕ) (u : ℝ) :
    exp2piI ((k : ℝ) * u) = exp2piI u ^ k := by
  unfold exp2piI
  have harg :
      (((2 * Real.pi * ((k : ℝ) * u) : ℝ) : ℂ) * Complex.I)
        =
      (k : ℂ) * (((2 * Real.pi * u : ℝ) : ℂ) * Complex.I) := by
    norm_num [Complex.ofReal_mul]
    ring
  rw [harg, Complex.exp_nat_mul]

private lemma exp2piI_sum_Icc_eq_geom (n : ℕ) (u : ℝ) :
    (Finset.Icc 1 n).sum (fun k => exp2piI ((k : ℝ) * u))
      =
    exp2piI u * (Finset.range n).sum (fun i => exp2piI u ^ i) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (show 1 ≤ n + 1 by omega)]
      rw [Finset.sum_range_succ]
      rw [ih]
      rw [exp2piI_nat_mul]
      ring

private lemma geom_norm_le_two_mul_inv_norm
    {z : ℂ} (hz_norm : ‖z‖ = 1) (hz_ne : z ≠ 1) (n : ℕ) :
    ‖z * (Finset.range n).sum (fun i => z ^ i)‖
      ≤ 2 * ‖(z - 1)⁻¹‖ := by
  have hnum : ‖z ^ n - 1‖ ≤ (2 : ℝ) := by
    calc
      ‖z ^ n - 1‖ ≤ ‖z ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by
        rw [norm_pow, hz_norm]
        norm_num
  calc
    ‖z * (Finset.range n).sum (fun i => z ^ i)‖
        = ‖z‖ * ‖(Finset.range n).sum (fun i => z ^ i)‖ := by
          rw [norm_mul]
    _ = ‖(Finset.range n).sum (fun i => z ^ i)‖ := by
          rw [hz_norm, one_mul]
    _ = ‖(z ^ n - 1) * (z - 1)⁻¹‖ := by
          rw [geom_sum_eq hz_ne n]
          rw [div_eq_mul_inv]
    _ ≤ 2 * ‖(z - 1)⁻¹‖ := by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right hnum (norm_nonneg _)

private lemma geometric_partial_sums_bounded_on_compact_away_int
    {K : Set ℝ}
    (hK : IsCompact K)
    (hK_away : ∀ u ∈ K, ∀ z : ℤ, u ≠ (z : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ℕ, ∀ u ∈ K,
        ‖(Finset.Icc 1 n).sum
          (fun k => exp2piI ((k : ℝ) * u))‖ ≤ C := by
  let F : ℝ → ℝ := fun u => 2 * ‖(exp2piI u - 1)⁻¹‖
  have hden_cont : Continuous (fun u : ℝ => exp2piI u - 1) := by
    unfold exp2piI
    fun_prop
  have hden_ne : ∀ u ∈ K, exp2piI u - 1 ≠ 0 := by
    intro u hu hzero
    exact exp2piI_ne_one_of_not_int (fun z => hK_away u hu z)
      (sub_eq_zero.mp hzero)
  have hF_cont : ContinuousOn F K := by
    dsimp [F]
    exact ((hden_cont.continuousOn.inv₀ hden_ne).norm.const_mul 2)
  rcases bddAbove_def.mp (hK.bddAbove_image hF_cont) with ⟨C₀, hC₀⟩
  refine ⟨max 0 C₀, le_max_left 0 C₀, ?_⟩
  intro n u hu
  have hF_le : F u ≤ max 0 C₀ :=
    (hC₀ (F u) ⟨u, hu, rfl⟩).trans (le_max_right 0 C₀)
  have hz_norm : ‖exp2piI u‖ = 1 := by
    simp [exp2piI, Complex.norm_exp]
  have hz_ne : exp2piI u ≠ 1 :=
    exp2piI_ne_one_of_not_int (fun z => hK_away u hu z)
  calc
    ‖(Finset.Icc 1 n).sum (fun k => exp2piI ((k : ℝ) * u))‖
        = ‖exp2piI u * (Finset.range n).sum (fun i => exp2piI u ^ i)‖ := by
          rw [exp2piI_sum_Icc_eq_geom]
    _ ≤ 2 * ‖(exp2piI u - 1)⁻¹‖ :=
          geom_norm_le_two_mul_inv_norm hz_norm hz_ne n
    _ = F u := by
          rfl
    _ ≤ max 0 C₀ := hF_le

private lemma exp2piI_add_int (x : ℝ) (m : ℤ) :
    exp2piI (x + (m : ℝ)) = exp2piI x := by
  unfold exp2piI
  have harg :
      (((2 * Real.pi * (x + (m : ℝ)) : ℝ) : ℂ) * Complex.I)
        =
      (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
        + (m : ℂ) * (2 * Real.pi * Complex.I) := by
    norm_num [Complex.ofReal_mul]
    ring
  rw [harg]
  simpa [mul_assoc] using
    (Complex.exp_periodic.int_mul m
      (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I))

private lemma exp2piI_nat_mul_fract (k : ℕ) (u : ℝ) :
    exp2piI ((k : ℝ) * u) =
      exp2piI ((k : ℝ) * Int.fract u) := by
  have hu : u = Int.fract u + (⌊u⌋ : ℝ) :=
    (Int.fract_add_floor u).symm
  have hsplit :
      (k : ℝ) * (Int.fract u + (⌊u⌋ : ℝ))
        =
      (k : ℝ) * Int.fract u + (((k : ℤ) * ⌊u⌋ : ℤ) : ℝ) := by
    have hcast : (((k : ℤ) * ⌊u⌋ : ℤ) : ℝ) =
        (k : ℝ) * (⌊u⌋ : ℝ) := by
      norm_num
    rw [hcast]
    ring
  calc
    exp2piI ((k : ℝ) * u)
        = exp2piI ((k : ℝ) * (Int.fract u + (⌊u⌋ : ℝ))) := by
          exact congrArg exp2piI (congrArg (fun t : ℝ => (k : ℝ) * t) hu)
    _ = exp2piI
          ((k : ℝ) * Int.fract u + (((k : ℤ) * ⌊u⌋ : ℤ) : ℝ)) := by
          exact congrArg exp2piI hsplit
    _ = exp2piI ((k : ℝ) * Int.fract u) :=
          exp2piI_add_int ((k : ℝ) * Int.fract u) ((k : ℤ) * ⌊u⌋)

private lemma real_last_add_sum_diff_eq_first
    (w : ℕ → ℝ) {N : ℕ} (hN : 1 ≤ N) :
    w N + (Finset.Icc 1 (N - 1)).sum (fun k => w k - w (k + 1))
      = w 1 := by
  revert hN
  induction N with
  | zero =>
      intro hN
      omega
  | succ N ih =>
      intro hN
      cases N with
      | zero =>
          simp
      | succ M =>
          have hle : 1 ≤ Nat.succ M := Nat.succ_pos M
          have htel := Finset.sum_Icc_sub hle w
          rw [Nat.add_sub_cancel_right]
          have hneg := congrArg Neg.neg htel
          simp only [neg_sub] at hneg
          have hflip :
              (Finset.Icc 1 (M + 1)).sum
                  (fun k => w k - w (k + 1))
                =
              - (Finset.Icc 1 (M + 1)).sum
                  (fun k => w (k + 1) - w k) := by
            rw [← Finset.sum_neg_distrib]
            simp only [neg_sub]
          rw [hflip, hneg]
          ring

private lemma abel_summation_monotone
    {N : ℕ} {w : ℕ → ℝ} {b : ℕ → ℂ}
    (hN : 1 ≤ N) :
    (Finset.Icc 1 N).sum (fun k => (w k : ℂ) * b k)
      =
    (w N : ℂ) * (Finset.Icc 1 N).sum b
      +
    (Finset.Icc 1 (N - 1)).sum
      (fun k =>
        (((w k - w (k + 1) : ℝ) : ℂ) *
          (Finset.Icc 1 k).sum b)) := by
  revert hN
  induction N with
  | zero =>
      intro hN
      omega
  | succ N ih =>
      intro hN
      cases N with
      | zero =>
          simp [Finset.Icc_self]
      | succ M =>
          have hM1 : 1 ≤ Nat.succ M := Nat.succ_pos M
          have ihM := ih hM1
          rw [Finset.sum_Icc_succ_top (show 1 ≤ Nat.succ (Nat.succ M) by omega)
                (fun k => (w k : ℂ) * b k)]
          rw [Finset.sum_Icc_succ_top (show 1 ≤ Nat.succ (Nat.succ M) by omega)
                (fun k => b k)]
          rw [Nat.add_sub_cancel_right]
          rw [Finset.sum_Icc_succ_top (show 1 ≤ Nat.succ M by omega)
                (fun k =>
                  (((w k - w (k + 1) : ℝ) : ℂ) *
                    (Finset.Icc 1 k).sum b))]
          rw [Nat.add_sub_cancel_right] at ihM
          rw [ihM]
          simp only [Complex.ofReal_sub]
          ring

private lemma abel_summation_one_coordinate_of_one_le
    {N : ℕ} {u : ℝ} {w : ℕ → ℝ} {Cgeom : ℝ}
    (hN : 1 ≤ N)
    (hCgeom : 0 ≤ Cgeom)
    (hgeom : ∀ n : ℕ,
      ‖(Finset.Icc 1 n).sum
        (fun k : ℕ => exp2piI ((k : ℝ) * u))‖ ≤ Cgeom)
    (hw_nonneg : ∀ k ∈ Finset.Icc 1 N, 0 ≤ w k)
    (hw_mono : ∀ k l, 1 ≤ k → k ≤ l → l ≤ N → w l ≤ w k) :
    ‖(Finset.Icc 1 N).sum
      (fun k : ℕ => (w k : ℂ) * exp2piI ((k : ℝ) * u))‖
      ≤ 2 * Cgeom * w 1 := by
  let e : ℕ → ℂ := fun k => exp2piI ((k : ℝ) * u)
  let S : ℕ → ℂ := fun n => (Finset.Icc 1 n).sum e
  have habel := abel_summation_monotone (N := N) (w := w) (b := e) hN
  have hwN_nonneg : 0 ≤ w N :=
    hw_nonneg N (by exact Finset.mem_Icc.mpr ⟨hN, le_rfl⟩)
  have hw1_nonneg : 0 ≤ w 1 :=
    hw_nonneg 1 (by exact Finset.mem_Icc.mpr ⟨le_rfl, hN⟩)
  have hfirst :
      ‖((w N : ℝ) : ℂ) * S N‖ ≤ w N * Cgeom := by
    calc
      ‖((w N : ℝ) : ℂ) * S N‖
          = w N * ‖S N‖ := by
            rw [norm_mul]
            rw [← Real.norm_of_nonneg hwN_nonneg]
            norm_num
      _ ≤ w N * Cgeom :=
            mul_le_mul_of_nonneg_left (hgeom N) hwN_nonneg
  have hsum :
      ‖(Finset.Icc 1 (N - 1)).sum
        (fun k => (((w k - w (k + 1) : ℝ) : ℂ) * S k))‖
        ≤ (Finset.Icc 1 (N - 1)).sum
          (fun k => (w k - w (k + 1)) * Cgeom) := by
    calc
      ‖(Finset.Icc 1 (N - 1)).sum
        (fun k => (((w k - w (k + 1) : ℝ) : ℂ) * S k))‖
          ≤ (Finset.Icc 1 (N - 1)).sum
              (fun k =>
                ‖(((w k - w (k + 1) : ℝ) : ℂ) * S k)‖) :=
            norm_sum_le _ _
      _ ≤ (Finset.Icc 1 (N - 1)).sum
          (fun k => (w k - w (k + 1)) * Cgeom) := by
            refine Finset.sum_le_sum ?_
            intro k hk
            rcases Finset.mem_Icc.mp hk with ⟨hk1, hkNsub⟩
            have hk_succ_le : k + 1 ≤ N := by omega
            have hd_nonneg : 0 ≤ w k - w (k + 1) :=
              sub_nonneg.mpr (hw_mono k (k + 1) hk1 (Nat.le_succ k) hk_succ_le)
            calc
              ‖(((w k - w (k + 1) : ℝ) : ℂ) * S k)‖
                  = (w k - w (k + 1)) * ‖S k‖ := by
                    rw [norm_mul]
                    rw [← Real.norm_of_nonneg hd_nonneg]
                    norm_num
              _ ≤ (w k - w (k + 1)) * Cgeom :=
                    mul_le_mul_of_nonneg_left (hgeom k) hd_nonneg
  have hmain :
      ‖(Finset.Icc 1 N).sum
        (fun k : ℕ => (w k : ℂ) * exp2piI ((k : ℝ) * u))‖
        ≤ Cgeom * w 1 := by
    calc
      ‖(Finset.Icc 1 N).sum
        (fun k : ℕ => (w k : ℂ) * exp2piI ((k : ℝ) * u))‖
          =
        ‖((w N : ℝ) : ℂ) * S N +
          (Finset.Icc 1 (N - 1)).sum
            (fun k => (((w k - w (k + 1) : ℝ) : ℂ) * S k))‖ := by
            rw [habel]
      _ ≤ w N * Cgeom +
            (Finset.Icc 1 (N - 1)).sum
              (fun k => (w k - w (k + 1)) * Cgeom) :=
            (norm_add_le _ _).trans (add_le_add hfirst hsum)
      _ = Cgeom * w 1 := by
            rw [← Finset.sum_mul]
            rw [← add_mul]
            rw [real_last_add_sum_diff_eq_first w hN]
            ring
  have hnonneg : 0 ≤ Cgeom * w 1 := mul_nonneg hCgeom hw1_nonneg
  calc
    ‖(Finset.Icc 1 N).sum
      (fun k : ℕ => (w k : ℂ) * exp2piI ((k : ℝ) * u))‖
        ≤ Cgeom * w 1 := hmain
    _ ≤ 2 * Cgeom * w 1 := by nlinarith

theorem geometric_partial_sums_bounded_in_coordinate
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ Cgeom : ℝ, 0 < Cgeom ∧
      ∀ u : ℝ,
      (∀ m : ℤ, delta ≤ |u - (m : ℝ)|) →
      ∀ N : ℕ,
        ‖(Finset.Icc 1 N).sum
          (fun k : ℕ => exp2piI ((k : ℝ) * u))‖ ≤ Cgeom := by
  let K : Set ℝ :=
    Set.Icc (0 : ℝ) 1 ∩
      {x : ℝ | ∀ m : ℤ, delta ≤ |x - (m : ℝ)|}
  have hclosed_away :
      IsClosed {x : ℝ | ∀ m : ℤ, delta ≤ |x - (m : ℝ)|} := by
    rw [show
        {x : ℝ | ∀ m : ℤ, delta ≤ |x - (m : ℝ)|}
          =
        ⋂ m : ℤ, {x : ℝ | delta ≤ |x - (m : ℝ)|} by
          ext x
          simp]
    refine isClosed_iInter fun m => ?_
    have hcont : Continuous (fun x : ℝ => |x - (m : ℝ)|) :=
      continuous_abs.comp (continuous_id.sub continuous_const)
    exact isClosed_Ici.preimage hcont
  have hK : IsCompact K := by
    exact isCompact_Icc.inter_right hclosed_away
  have hK_away : ∀ x ∈ K, ∀ z : ℤ, x ≠ (z : ℝ) := by
    intro x hx z hxz
    have hle : delta ≤ |x - (z : ℝ)| := hx.2 z
    rw [hxz, sub_self, abs_zero] at hle
    linarith
  rcases geometric_partial_sums_bounded_on_compact_away_int hK hK_away with
    ⟨C₀, hC₀_nonneg, hgeom⟩
  refine ⟨max 1 C₀, lt_of_lt_of_le zero_lt_one (le_max_left 1 C₀), ?_⟩
  intro u hu N
  have hfract_mem : Int.fract u ∈ K := by
    refine ⟨?_, ?_⟩
    · exact ⟨Int.fract_nonneg u, (Int.fract_lt_one u).le⟩
    · intro m
      have hshift := hu (m + ⌊u⌋)
      have hcast : (((m + ⌊u⌋ : ℤ) : ℝ)) = (m : ℝ) + (⌊u⌋ : ℝ) := by
        norm_num
      have hdiff :
          u - (((m + ⌊u⌋ : ℤ) : ℝ)) = Int.fract u - (m : ℝ) := by
        calc
          u - (((m + ⌊u⌋ : ℤ) : ℝ))
              = u - ((m : ℝ) + (⌊u⌋ : ℝ)) := by
                rw [hcast]
          _ = (Int.fract u + (⌊u⌋ : ℝ)) -
                ((m : ℝ) + (⌊u⌋ : ℝ)) := by
                exact congrArg
                  (fun t : ℝ => t - ((m : ℝ) + (⌊u⌋ : ℝ)))
                  (Int.fract_add_floor u).symm
          _ = Int.fract u - (m : ℝ) := by
                ring
      rw [hdiff] at hshift
      exact hshift
  have hsum_eq :
      (Finset.Icc 1 N).sum
          (fun k : ℕ => exp2piI ((k : ℝ) * u))
        =
      (Finset.Icc 1 N).sum
          (fun k : ℕ => exp2piI ((k : ℝ) * Int.fract u)) := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    exact exp2piI_nat_mul_fract k u
  calc
    ‖(Finset.Icc 1 N).sum
        (fun k : ℕ => exp2piI ((k : ℝ) * u))‖
        =
      ‖(Finset.Icc 1 N).sum
        (fun k : ℕ => exp2piI ((k : ℝ) * Int.fract u))‖ := by
          rw [hsum_eq]
    _ ≤ C₀ := hgeom N (Int.fract u) hfract_mem
    _ ≤ max 1 C₀ := le_max_right 1 C₀

theorem abel_summation_one_coordinate
    {N : ℕ} {u : ℝ} {w : ℕ → ℝ} {Cgeom : ℝ}
    (hN : 1 ≤ N)
    (hCgeom : 0 ≤ Cgeom)
    (hgeom : ∀ n : ℕ,
      ‖(Finset.Icc 1 n).sum
        (fun k : ℕ => exp2piI ((k : ℝ) * u))‖ ≤ Cgeom)
    (hw_nonneg : ∀ k ∈ Finset.Icc 1 N, 0 ≤ w k)
    (hw_mono : ∀ k l, 1 ≤ k → k ≤ l → l ≤ N → w l ≤ w k) :
    ‖(Finset.Icc 1 N).sum
      (fun k : ℕ => (w k : ℂ) * exp2piI ((k : ℝ) * u))‖
      ≤ 2 * Cgeom * w 1 := by
  exact
    abel_summation_one_coordinate_of_one_le
      (N := N) (u := u) (w := w) (Cgeom := Cgeom)
      hN hCgeom hgeom hw_nonneg hw_mono

theorem firstCoordinateSliceWeightSum_d1 {N : ℕ} (alpha : ℝ)
    (_halpha : AlphaLeDimHalf 1 alpha) :
    firstCoordinateSliceWeightSum (d := 1) (by decide) alpha N ≤ 1 := by
  let i0 : Fin 1 := ⟨0, by decide⟩
  let oneVec : Fin 1 → ℕ := fun _ => 1
  have hsubset :
      ((indexBox 1 N).filter (fun k => k i0 = 1)) ⊆ ({oneVec} : Finset (Fin 1 → ℕ)) := by
    intro k hk
    rcases Finset.mem_filter.mp hk with ⟨hk_box, hk0⟩
    have hk_eq : k = oneVec := by
      ext i
      fin_cases i
      exact hk0
    simp [hk_eq]
  have hterm_nonneg : ∀ x ∈ ({oneVec} : Finset (Fin 1 → ℕ)),
      x ∉ (indexBox 1 N).filter (fun k => k i0 = 1) →
      0 ≤ 1 / sobolevWeight alpha (natVec x) := by
    intro x hx hxnot
    exact one_div_nonneg.mpr (sobolevWeight_nonneg alpha (natVec x))
  have hsum_le :
      firstCoordinateSliceWeightSum (d := 1) (by decide) alpha N
        ≤ ({oneVec} : Finset (Fin 1 → ℕ)).sum
            (fun k => 1 / sobolevWeight alpha (natVec k)) := by
    unfold firstCoordinateSliceWeightSum
    simpa [i0, oneVec] using
      Finset.sum_le_sum_of_subset_of_nonneg hsubset hterm_nonneg
  have hsingle :
      ({oneVec} : Finset (Fin 1 → ℕ)).sum
          (fun k => 1 / sobolevWeight alpha (natVec k)) ≤ 1 := by
    have hW : 1 ≤ sobolevWeight alpha (natVec oneVec) :=
      one_le_sobolevWeight alpha (natVec oneVec)
    have hWpos : 0 < sobolevWeight alpha (natVec oneVec) :=
      (zero_lt_one.trans_le hW)
    simpa [oneVec] using
      (div_le_one hWpos).2 hW
  exact hsum_le.trans hsingle

private def transverseShell (r m : ℕ) : Finset (Fin r → ℕ) :=
  (indexBox r m).filter (fun v => ∃ j : Fin r, v j = m)

private lemma transverseShell_card_le (n m : ℕ) :
    (transverseShell (n + 1) m).card ≤ (n + 1) * m ^ n := by
  classical
  induction n with
  | zero =>
      have hsubset :
          transverseShell 1 m ⊆ ({fun _ : Fin 1 => m} : Finset (Fin 1 → ℕ)) := by
        intro v hv
        rcases Finset.mem_filter.mp hv with ⟨_hvbox, hvmax⟩
        rcases hvmax with ⟨j, hj⟩
        have hv_eq : v = fun _ : Fin 1 => m := by
          ext i
          fin_cases i
          fin_cases j
          exact hj
        simp [hv_eq]
      calc
        (transverseShell 1 m).card ≤ ({fun _ : Fin 1 => m} : Finset (Fin 1 → ℕ)).card :=
          Finset.card_le_card hsubset
        _ = (0 + 1) * m ^ 0 := by simp
  | succ n ih =>
      let A : Finset (Fin (n + 2) → ℕ) :=
        (indexBox (n + 2) m).filter (fun v => v 0 = m)
      let B : Finset (Fin (n + 2) → ℕ) :=
        (indexBox (n + 2) m).filter
          (fun v => Fin.tail v ∈ transverseShell (n + 1) m)
      have hsubset : transverseShell (n + 2) m ⊆ A ∪ B := by
        intro v hv
        rcases Finset.mem_filter.mp hv with ⟨hvbox, hvmax⟩
        rcases hvmax with ⟨j, hj⟩
        cases j using Fin.cases with
        | zero =>
            exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hvbox, hj⟩)
        | succ j =>
            refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hvbox, ?_⟩)
            refine Finset.mem_filter.mpr ⟨?_, ⟨j, ?_⟩⟩
            · have hvcoord :=
                (indexBox_mem_iff (d := n + 2) (N := m) v).1 hvbox
              rw [indexBox_mem_iff]
              intro i
              exact hvcoord i.succ
            · simpa [Fin.tail] using hj
      have hAcard : A.card ≤ m ^ (n + 1) := by
        have hmaps :
            Set.MapsTo (fun v : Fin (n + 2) → ℕ => Fin.tail v)
              ↑A ↑(indexBox (n + 1) m) := by
          intro v hv
          rcases Finset.mem_filter.mp hv with ⟨hvbox, _hv0⟩
          have hvcoord :=
            (indexBox_mem_iff (d := n + 2) (N := m) v).1 hvbox
          change Fin.tail v ∈ indexBox (n + 1) m
          rw [indexBox_mem_iff]
          intro i
          exact hvcoord i.succ
        have hinj :
            (A : Set (Fin (n + 2) → ℕ)).InjOn
              (fun v : Fin (n + 2) → ℕ => Fin.tail v) := by
          intro v hv w hw htail
          rcases Finset.mem_filter.mp hv with ⟨_hvbox, hv0⟩
          rcases Finset.mem_filter.mp hw with ⟨_hwbox, hw0⟩
          ext i
          cases i using Fin.cases with
          | zero => simp [hv0, hw0]
          | succ i =>
              exact congrFun htail i
        calc
          A.card ≤ (indexBox (n + 1) m).card :=
            Finset.card_le_card_of_injOn
              (fun v : Fin (n + 2) → ℕ => Fin.tail v) hmaps hinj
          _ = m ^ (n + 1) := card_indexBox (n + 1) m
      have hBcard_le₀ :
          B.card ≤ m * (transverseShell (n + 1) m).card := by
        dsimp [B, indexBox]
        rw [Finset.card_consEquiv_filter_piFinset
          (S := fun _ : Fin (n + 2) => Finset.Icc 1 m)
          (P := fun v : Fin (n + 1) → ℕ =>
            v ∈ transverseShell (n + 1) m)]
        exact Nat.mul_le_mul
          (by simp)
          (Finset.card_le_card (by
            intro v hv
            exact (Finset.mem_filter.mp hv).2))
      have hBcard_le : B.card ≤ (n + 1) * m ^ (n + 1) := by
        calc
          B.card ≤ m * (transverseShell (n + 1) m).card := hBcard_le₀
          _ ≤ m * ((n + 1) * m ^ n) := Nat.mul_le_mul_left m ih
          _ = (n + 1) * m ^ (n + 1) := by ring
      calc
        (transverseShell (n + 2) m).card ≤ (A ∪ B).card :=
          Finset.card_le_card hsubset
        _ ≤ A.card + B.card := Finset.card_union_le A B
        _ ≤ m ^ (n + 1) + (n + 1) * m ^ (n + 1) :=
          Nat.add_le_add hAcard hBcard_le
        _ = (n + 2) * m ^ (n + 1) := by ring

private lemma firstCoordinateSliceWeightSum_tail_sum {n N : ℕ} (alpha : ℝ)
    (hd_pos : 0 < n + 2) :
    firstCoordinateSliceWeightSum (d := n + 2) hd_pos alpha N
      =
        (indexBox (n + 1) N).sum
          (fun v : Fin (n + 1) → ℕ =>
            1 / sobolevWeight alpha (natVec (Fin.cons 1 v))) := by
  classical
  unfold firstCoordinateSliceWeightSum
  let i0 : Fin (n + 2) := ⟨0, hd_pos⟩
  let slice : Finset (Fin (n + 2) → ℕ) :=
    (indexBox (n + 2) N).filter (fun k => k i0 = 1)
  have hsum :
      slice.sum (fun k => 1 / sobolevWeight alpha (natVec k))
        =
      (indexBox (n + 1) N).sum
        (fun v : Fin (n + 1) → ℕ =>
          1 / sobolevWeight alpha (natVec (Fin.cons 1 v))) := by
    refine Finset.sum_bij'
      (s := slice) (t := indexBox (n + 1) N)
      (fun k _hk => Fin.tail k)
      (fun v _hv => Fin.cons 1 v) ?_ ?_ ?_ ?_ ?_
    · intro k hk
      rcases Finset.mem_filter.mp hk with ⟨hkbox, _hk0⟩
      have hkcoord :=
        (indexBox_mem_iff (d := n + 2) (N := N) k).1 hkbox
      rw [indexBox_mem_iff]
      intro i
      exact hkcoord i.succ
    · intro v hv
      have hvcoord :=
        (indexBox_mem_iff (d := n + 1) (N := N) v).1 hv
      have hN : 1 ≤ N := by
        exact (hvcoord 0).1.trans (hvcoord 0).2
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · rw [indexBox_mem_iff]
        intro i
        cases i using Fin.cases with
        | zero =>
            exact ⟨by norm_num, hN⟩
        | succ i =>
            exact hvcoord i
      · simp [i0]
    · intro k hk
      rcases Finset.mem_filter.mp hk with ⟨_hkbox, hk0⟩
      ext i
      cases i using Fin.cases with
      | zero => simpa [i0] using hk0.symm
      | succ i => simp [Fin.tail]
    · intro v hv
      ext i
      simp [Fin.tail]
    · intro k hk
      rcases Finset.mem_filter.mp hk with ⟨_hkbox, hk0⟩
      have hk_cons : Fin.cons 1 (Fin.tail k) = k := by
        ext i
        cases i using Fin.cases with
        | zero => simpa [i0] using hk0.symm
        | succ i => simp [Fin.tail]
      rw [hk_cons]
  simpa [slice, i0] using hsum

private lemma firstCoordinateSliceWeightSum_shell_term_le {n m : ℕ}
    (halpha : AlphaLeDimHalf (n + 2) alpha)
    (hm : m ∈ Finset.Icc 1 m)
    {v : Fin (n + 1) → ℕ} (hv : v ∈ transverseShell (n + 1) m) :
    1 / sobolevWeight alpha (natVec (Fin.cons 1 v))
      ≤ Real.rpow (m : ℝ) (-2 * alpha) := by
  rcases Finset.mem_Icc.mp hm with ⟨hm_one, _⟩
  have hm_pos_nat : 0 < m := Nat.lt_of_lt_of_le Nat.zero_lt_one hm_one
  have hm_pos : 0 < (m : ℝ) := by exact_mod_cast hm_pos_nat
  have hm_nonneg : 0 ≤ (m : ℝ) := hm_pos.le
  rcases Finset.mem_filter.mp hv with ⟨_hvbox, hvmax⟩
  rcases hvmax with ⟨j, hvj⟩
  have hcoord_le_norm :
      (m : ℝ) ≤ ‖natVec (Fin.cons 1 v)‖ := by
    have h :=
      PiLp.norm_apply_le (x := natVec (Fin.cons 1 v)) (i := Fin.succ j)
    have h' :
        ‖((v j : ℕ) : ℝ)‖
          ≤ ‖natVec (Fin.cons 1 v)‖ := by
      simpa [natVec, toE] using h
    simpa [hvj, Real.norm_of_nonneg hm_nonneg] using h'
  have hexp_nonneg : 0 ≤ 2 * alpha := by
    nlinarith [halpha.nonneg]
  have hpow_le_weight :
      Real.rpow (m : ℝ) (2 * alpha)
        ≤ sobolevWeight alpha (natVec (Fin.cons 1 v)) := by
    by_cases hzero : alpha = 0
    · simp [sobolevWeight, sobolevPower, hzero]
    · have hpow_le :
          Real.rpow (m : ℝ) (2 * alpha)
            ≤ Real.rpow ‖natVec (Fin.cons 1 v)‖ (2 * alpha) :=
        Real.rpow_le_rpow hm_nonneg hcoord_le_norm hexp_nonneg
      have hnormpow_le :
          Real.rpow ‖natVec (Fin.cons 1 v)‖ (2 * alpha)
            ≤ 1 + Real.rpow ‖natVec (Fin.cons 1 v)‖ (2 * alpha) := by
        linarith
      simpa [sobolevWeight, sobolevPower, hzero] using hpow_le.trans hnormpow_le
  have hpow_pos : 0 < Real.rpow (m : ℝ) (2 * alpha) :=
    Real.rpow_pos_of_pos hm_pos _
  calc
    1 / sobolevWeight alpha (natVec (Fin.cons 1 v))
        ≤ 1 / Real.rpow (m : ℝ) (2 * alpha) :=
          one_div_le_one_div_of_le hpow_pos hpow_le_weight
    _ = Real.rpow (m : ℝ) (-2 * alpha) := by
          rw [one_div]
          have hneg : -2 * alpha = -(2 * alpha) := by ring
          simpa [hneg] using (Real.rpow_neg hm_nonneg (2 * alpha)).symm

private lemma transverseShell_weight_sum_le {n m : ℕ}
    (halpha : AlphaLeDimHalf (n + 2) alpha)
    (hm : m ∈ Finset.Icc 1 m) :
    (transverseShell (n + 1) m).sum
        (fun v : Fin (n + 1) → ℕ =>
          1 / sobolevWeight alpha (natVec (Fin.cons 1 v)))
      ≤ ((n : ℝ) + 3) *
          Real.rpow (m : ℝ) ((n : ℝ) - 2 * alpha) := by
  classical
  have hcard_nat :
      (transverseShell (n + 1) m).card ≤ (n + 3) * m ^ n := by
    exact (transverseShell_card_le n m).trans
      (Nat.mul_le_mul_right (m ^ n) (by omega))
  have hcard_real :
      ((transverseShell (n + 1) m).card : ℝ)
        ≤ ((n : ℝ) + 3) * Real.rpow (m : ℝ) (n : ℝ) := by
    have hcast : (((n + 3) * m ^ n : ℕ) : ℝ)
        = ((n : ℝ) + 3) * Real.rpow (m : ℝ) (n : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_pow, ← Real.rpow_natCast]
      norm_num
    exact (Nat.cast_le.mpr hcard_nat).trans_eq hcast
  have hm_nonneg : 0 ≤ (m : ℝ) := by positivity
  have hterm_nonneg : 0 ≤ Real.rpow (m : ℝ) (-2 * alpha) :=
    Real.rpow_nonneg hm_nonneg _
  have hsum_le_card :
      (transverseShell (n + 1) m).sum
          (fun v : Fin (n + 1) → ℕ =>
            1 / sobolevWeight alpha (natVec (Fin.cons 1 v)))
        ≤ ((transverseShell (n + 1) m).card : ℝ) *
            Real.rpow (m : ℝ) (-2 * alpha) := by
    calc
      (transverseShell (n + 1) m).sum
          (fun v : Fin (n + 1) → ℕ =>
            1 / sobolevWeight alpha (natVec (Fin.cons 1 v)))
          ≤ (transverseShell (n + 1) m).sum
              (fun _v : Fin (n + 1) → ℕ =>
                Real.rpow (m : ℝ) (-2 * alpha)) := by
            exact Finset.sum_le_sum fun v hv =>
              firstCoordinateSliceWeightSum_shell_term_le
                (n := n) (m := m) (alpha := alpha) halpha hm hv
      _ = ((transverseShell (n + 1) m).card : ℝ) *
            Real.rpow (m : ℝ) (-2 * alpha) := by
            rw [Finset.sum_const, nsmul_eq_mul]
  rcases Finset.mem_Icc.mp hm with ⟨hm_one, _⟩
  have hm_pos_nat : 0 < m := Nat.lt_of_lt_of_le Nat.zero_lt_one hm_one
  have hm_pos : 0 < (m : ℝ) := by exact_mod_cast hm_pos_nat
  calc
    (transverseShell (n + 1) m).sum
        (fun v : Fin (n + 1) → ℕ =>
          1 / sobolevWeight alpha (natVec (Fin.cons 1 v)))
        ≤ ((transverseShell (n + 1) m).card : ℝ) *
            Real.rpow (m : ℝ) (-2 * alpha) := hsum_le_card
    _ ≤ (((n : ℝ) + 3) * Real.rpow (m : ℝ) (n : ℝ)) *
            Real.rpow (m : ℝ) (-2 * alpha) :=
          mul_le_mul_of_nonneg_right hcard_real hterm_nonneg
    _ = ((n : ℝ) + 3) *
          Real.rpow (m : ℝ) ((n : ℝ) - 2 * alpha) := by
          calc
            (((n : ℝ) + 3) * Real.rpow (m : ℝ) (n : ℝ)) *
                Real.rpow (m : ℝ) (-2 * alpha)
                = ((n : ℝ) + 3) *
                    (Real.rpow (m : ℝ) (n : ℝ) *
                      Real.rpow (m : ℝ) (-2 * alpha)) := by ring
            _ = ((n : ℝ) + 3) *
                  Real.rpow (m : ℝ) ((n : ℝ) - 2 * alpha) := by
                have hneg : -2 * alpha = -(2 * alpha) := by ring
                rw [hneg]
                have hadd :
                    Real.rpow (m : ℝ) (n : ℝ) *
                        Real.rpow (m : ℝ) (-(2 * alpha))
                      =
                    Real.rpow (m : ℝ) ((n : ℝ) + -(2 * alpha)) :=
                  (Real.rpow_add hm_pos (n : ℝ) (-(2 * alpha))).symm
                simpa [sub_eq_add_neg] using
                  congrArg (fun t : ℝ => ((n : ℝ) + 3) * t) hadd

private lemma firstCoordinateSliceWeightSum_le_sharp_transverse_shell_sum {d : ℕ}
    (hd_two : 2 ≤ d)
    (halpha : AlphaLeDimHalf d alpha) (N : ℕ) :
    firstCoordinateSliceWeightSum (d := d) (Nat.succ_pos _ |>.trans_le hd_two) alpha N
      ≤ ((d : ℝ) + 1) *
          (Finset.Icc 1 N).sum
            (fun m : ℕ =>
              Real.rpow (m : ℝ) ((d : ℝ) - 2 - 2 * alpha)) := by
  classical
  cases d with
  | zero => omega
  | succ d' =>
      cases d' with
      | zero => omega
      | succ n =>
          let maxTail : (Fin (n + 1) → ℕ) → ℕ :=
            fun v => Finset.univ.sup v
          have htail :=
            firstCoordinateSliceWeightSum_tail_sum
              (n := n) (N := N) (alpha := alpha)
              (hd_pos := Nat.succ_pos (n + 1))
          have hmaps :
              ∀ v ∈ indexBox (n + 1) N, maxTail v ∈ Finset.Icc 1 N := by
            intro v hv
            have hvcoord :=
              (indexBox_mem_iff (d := n + 1) (N := N) v).1 hv
            refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
            · exact (hvcoord 0).1.trans
                (Finset.le_sup (s := Finset.univ) (f := v)
                  (by simp : (0 : Fin (n + 1)) ∈ Finset.univ))
            · exact Finset.sup_le fun j _hj => (hvcoord j).2
          have hfiber_subset :
              ∀ m ∈ Finset.Icc 1 N,
                (indexBox (n + 1) N).filter (fun v => maxTail v = m)
                  ⊆ transverseShell (n + 1) m := by
            intro m hm v hv
            rcases Finset.mem_filter.mp hv with ⟨hvbox, hmax⟩
            have hvcoord :=
              (indexBox_mem_iff (d := n + 1) (N := N) v).1 hvbox
            refine Finset.mem_filter.mpr ⟨?_, ?_⟩
            · rw [indexBox_mem_iff]
              intro j
              refine ⟨(hvcoord j).1, ?_⟩
              exact (Finset.le_sup (s := Finset.univ) (f := v)
                (by simp : j ∈ Finset.univ)).trans_eq hmax
            · rcases Finset.exists_mem_eq_sup (s := Finset.univ)
                (by simp : (Finset.univ : Finset (Fin (n + 1))).Nonempty)
                (f := v) with ⟨j, _hj, hjmax⟩
              exact ⟨j, hjmax.symm.trans hmax⟩
          have hfiber_le :
              ∀ m ∈ Finset.Icc 1 N,
                ((indexBox (n + 1) N).filter (fun v => maxTail v = m)).sum
                    (fun v : Fin (n + 1) → ℕ =>
                      1 / sobolevWeight alpha (natVec (Fin.cons 1 v)))
                  ≤ (transverseShell (n + 1) m).sum
                    (fun v : Fin (n + 1) → ℕ =>
                      1 / sobolevWeight alpha (natVec (Fin.cons 1 v))) := by
            intro m hm
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (hfiber_subset m hm)
              (fun v _hv _hnot =>
                one_div_nonneg.mpr
                  (sobolevWeight_nonneg alpha (natVec (Fin.cons 1 v))))
          have hsums :
              firstCoordinateSliceWeightSum
                  (d := n + 2) (Nat.succ_pos _ |>.trans_le hd_two) alpha N
                ≤ ((n : ℝ) + 3) *
                    (Finset.Icc 1 N).sum
                      (fun m : ℕ =>
                        Real.rpow (m : ℝ) ((n : ℝ) - 2 * alpha)) := by
            rw [firstCoordinateSliceWeightSum_tail_sum
              (n := n) (N := N) (alpha := alpha)
              (hd_pos := (Nat.succ_pos _ |>.trans_le hd_two))]
            rw [← Finset.sum_fiberwise_of_maps_to hmaps
              (fun v : Fin (n + 1) → ℕ =>
                1 / sobolevWeight alpha (natVec (Fin.cons 1 v)))]
            calc
              (Finset.Icc 1 N).sum
                  (fun m : ℕ =>
                    ((indexBox (n + 1) N).filter
                        (fun v : Fin (n + 1) → ℕ => maxTail v = m)).sum
                      (fun v : Fin (n + 1) → ℕ =>
                        1 / sobolevWeight alpha (natVec (Fin.cons 1 v))))
                  ≤ (Finset.Icc 1 N).sum
                    (fun m : ℕ =>
                      (transverseShell (n + 1) m).sum
                        (fun v : Fin (n + 1) → ℕ =>
                          1 / sobolevWeight alpha (natVec (Fin.cons 1 v)))) := by
                    exact Finset.sum_le_sum fun m hm => hfiber_le m hm
              _ ≤ (Finset.Icc 1 N).sum
                    (fun m : ℕ =>
                      ((n : ℝ) + 3) *
                        Real.rpow (m : ℝ) ((n : ℝ) - 2 * alpha)) := by
                    exact Finset.sum_le_sum fun m hm =>
                      transverseShell_weight_sum_le
                        (n := n) (m := m) (alpha := alpha) halpha
                        (show m ∈ Finset.Icc 1 m from
                          Finset.mem_Icc.mpr
                            ⟨(Finset.mem_Icc.mp hm).1, le_rfl⟩)
              _ = ((n : ℝ) + 3) *
                    (Finset.Icc 1 N).sum
                      (fun m : ℕ =>
                        Real.rpow (m : ℝ) ((n : ℝ) - 2 * alpha)) := by
                    rw [Finset.mul_sum]
          have hconst : ((n : ℝ) + (1 + 2)) = (n : ℝ) + 3 := by norm_num
          simpa [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, hconst,
            add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using hsums

private lemma transverse_shell_sum_subcritical_bound {d : ℕ} {alpha : ℝ}
    (hcase : 2 * alpha < (d : ℝ) - 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ N : ℕ,
        (Finset.Icc 1 N).sum
            (fun m : ℕ =>
              Real.rpow (m : ℝ) ((d : ℝ) - 2 - 2 * alpha))
          ≤ C * Real.rpow ((N : ℝ) + 1)
              ((d : ℝ) - 1 - 2 * alpha) := by
  let p : ℝ := (d : ℝ) - 2 - 2 * alpha
  let q : ℝ := (d : ℝ) - 1 - 2 * alpha
  have hp_gt_neg_one : -1 < p := by
    dsimp [p]
    linarith
  have hq_pos : 0 < q := by
    dsimp [q]
    linarith
  have hp_add_one : p + 1 = q := by
    dsimp [p, q]
    ring
  change ∃ C : ℝ, 0 < C ∧
    ∀ N : ℕ,
      (Finset.Icc 1 N).sum (fun m : ℕ => Real.rpow (m : ℝ) p)
        ≤ C * Real.rpow ((N : ℝ) + 1) q
  by_cases hp_nonneg : 0 ≤ p
  · refine ⟨1, by norm_num, ?_⟩
    intro N
    have hbase_pos : 0 < (N : ℝ) + 1 := by positivity
    have hterm :
        ∀ m ∈ Finset.Icc 1 N,
          Real.rpow (m : ℝ) p ≤ Real.rpow ((N : ℝ) + 1) p := by
      intro m hm
      rcases Finset.mem_Icc.mp hm with ⟨_hm_one, hmN⟩
      have hm_nonneg : 0 ≤ (m : ℝ) := by positivity
      have hm_le : (m : ℝ) ≤ (N : ℝ) + 1 := by
        exact_mod_cast (hmN.trans (Nat.le_succ N))
      exact Real.rpow_le_rpow hm_nonneg hm_le hp_nonneg
    have hsum_le_const :
        (Finset.Icc 1 N).sum (fun m : ℕ => Real.rpow (m : ℝ) p)
          ≤ ((Finset.Icc 1 N).card : ℝ) *
              Real.rpow ((N : ℝ) + 1) p := by
      calc
        (Finset.Icc 1 N).sum (fun m : ℕ => Real.rpow (m : ℝ) p)
            ≤ (Finset.Icc 1 N).sum
                (fun _m : ℕ => Real.rpow ((N : ℝ) + 1) p) :=
              Finset.sum_le_sum hterm
        _ = ((Finset.Icc 1 N).card : ℝ) *
              Real.rpow ((N : ℝ) + 1) p := by
              rw [Finset.sum_const, nsmul_eq_mul]
    have hcard_le : ((Finset.Icc 1 N).card : ℝ) ≤ (N : ℝ) + 1 := by
      have hcard_nat : (Finset.Icc 1 N).card ≤ N + 1 := by
        rw [Nat.card_Icc]
        exact Nat.sub_le (N + 1) 1
      exact_mod_cast hcard_nat
    have hrpow_nonneg : 0 ≤ Real.rpow ((N : ℝ) + 1) p :=
      Real.rpow_nonneg hbase_pos.le p
    calc
      (Finset.Icc 1 N).sum (fun m : ℕ => Real.rpow (m : ℝ) p)
          ≤ ((Finset.Icc 1 N).card : ℝ) *
              Real.rpow ((N : ℝ) + 1) p := hsum_le_const
      _ ≤ ((N : ℝ) + 1) * Real.rpow ((N : ℝ) + 1) p :=
            mul_le_mul_of_nonneg_right hcard_le hrpow_nonneg
      _ = Real.rpow ((N : ℝ) + 1) q := by
            rw [← hp_add_one]
            calc
              ((N : ℝ) + 1) * Real.rpow ((N : ℝ) + 1) p
                  = Real.rpow ((N : ℝ) + 1) p * ((N : ℝ) + 1) := by ring
              _ = Real.rpow ((N : ℝ) + 1) (p + 1) := by
                    simpa [Real.rpow_one] using
                      (Real.rpow_add hbase_pos p 1).symm
      _ = 1 * Real.rpow ((N : ℝ) + 1) q := by ring
  · have hp_neg : p < 0 := lt_of_not_ge hp_nonneg
    let C : ℝ := 1 + q⁻¹
    have hC_pos : 0 < C := by
      dsimp [C]
      positivity
    refine ⟨C, hC_pos, ?_⟩
    intro N
    by_cases hN0 : N = 0
    · subst N
      simpa [C] using hC_pos.le
    have hN_pos_nat : 0 < N := Nat.pos_of_ne_zero hN0
    have hN_one : 1 ≤ N := hN_pos_nat
    have hN_real_nonneg : 0 ≤ (N : ℝ) := by positivity
    have hbase_pos : 0 < (N : ℝ) + 1 := by positivity
    have hbase_ge_one : 1 ≤ (N : ℝ) + 1 := by
      nlinarith [hN_real_nonneg]
    have hanti :
        AntitoneOn (fun x : ℝ => Real.rpow x p)
          (Set.Icc ((1 : ℕ) : ℝ) (N : ℝ)) := by
      intro x hx y _hy hxy
      have hx_pos : 0 < x := by
        exact (by norm_num : (0 : ℝ) < ((1 : ℕ) : ℝ)).trans_le hx.1
      exact Real.rpow_le_rpow_of_nonpos hx_pos hxy hp_neg.le
    have htail_le :
        (Finset.Ico 1 N).sum
            (fun m : ℕ => Real.rpow ((m + 1 : ℕ) : ℝ) p)
          ≤ ∫ x in (1 : ℝ)..(N : ℝ), Real.rpow x p := by
      simpa using
        (AntitoneOn.sum_le_integral_Ico
          (f := fun x : ℝ => Real.rpow x p) hN_one hanti)
    have hsum_le_integral :
        (Finset.Icc 1 N).sum (fun m : ℕ => Real.rpow (m : ℝ) p)
          ≤ 1 + ∫ x in (1 : ℝ)..(N : ℝ), Real.rpow x p := by
      calc
        (Finset.Icc 1 N).sum (fun m : ℕ => Real.rpow (m : ℝ) p)
            = (Finset.Ico 1 (N + 1)).sum
                (fun m : ℕ => Real.rpow (m : ℝ) p) := by
                rw [Finset.Ico_add_one_right_eq_Icc]
        _ = Real.rpow (1 : ℝ) p +
              (Finset.Ico (1 + 1) (N + 1)).sum
                (fun m : ℕ => Real.rpow (m : ℝ) p) := by
                rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : 1 < N + 1)]
                norm_num
        _ = 1 +
              (Finset.Ico 1 N).sum
                (fun m : ℕ => Real.rpow ((m + 1 : ℕ) : ℝ) p) := by
                have hone : Real.rpow (1 : ℝ) p = 1 := by
                  simp
                rw [hone]
                rw [Finset.sum_Ico_add' (fun m : ℕ => Real.rpow (m : ℝ) p) 1 N 1]
        _ ≤ 1 + ∫ x in (1 : ℝ)..(N : ℝ), Real.rpow x p :=
              add_le_add le_rfl htail_le
    have hintegral_eval :
        ∫ x in (1 : ℝ)..(N : ℝ), Real.rpow x p =
          (Real.rpow (N : ℝ) q - 1) / q := by
      change ∫ x in (1 : ℝ)..(N : ℝ), x ^ p =
        (((N : ℝ) ^ q) - 1) / q
      rw [integral_rpow (Or.inl hp_gt_neg_one), hp_add_one, Real.one_rpow]
    have hintegral_le :
        ∫ x in (1 : ℝ)..(N : ℝ), Real.rpow x p
          ≤ q⁻¹ * Real.rpow ((N : ℝ) + 1) q := by
      have hN_le_base : (N : ℝ) ≤ (N : ℝ) + 1 := by linarith
      have hpow_le :
          Real.rpow (N : ℝ) q ≤ Real.rpow ((N : ℝ) + 1) q :=
        Real.rpow_le_rpow hN_real_nonneg hN_le_base hq_pos.le
      have hq_inv_nonneg : 0 ≤ q⁻¹ := inv_nonneg.mpr hq_pos.le
      rw [hintegral_eval, div_eq_mul_inv]
      calc
        (Real.rpow (N : ℝ) q - 1) * q⁻¹
            ≤ Real.rpow (N : ℝ) q * q⁻¹ :=
              mul_le_mul_of_nonneg_right (sub_le_self _ zero_le_one) hq_inv_nonneg
        _ ≤ Real.rpow ((N : ℝ) + 1) q * q⁻¹ :=
              mul_le_mul_of_nonneg_right hpow_le hq_inv_nonneg
        _ = q⁻¹ * Real.rpow ((N : ℝ) + 1) q := by ring
    have hone_le_pow : 1 ≤ Real.rpow ((N : ℝ) + 1) q :=
      Real.one_le_rpow hbase_ge_one hq_pos.le
    calc
      (Finset.Icc 1 N).sum (fun m : ℕ => Real.rpow (m : ℝ) p)
          ≤ 1 + ∫ x in (1 : ℝ)..(N : ℝ), Real.rpow x p :=
            hsum_le_integral
      _ ≤ 1 + q⁻¹ * Real.rpow ((N : ℝ) + 1) q :=
            add_le_add le_rfl hintegral_le
      _ ≤ Real.rpow ((N : ℝ) + 1) q +
            q⁻¹ * Real.rpow ((N : ℝ) + 1) q :=
            add_le_add hone_le_pow le_rfl
      _ = C * Real.rpow ((N : ℝ) + 1) q := by
            dsimp [C]
            ring

private lemma transverse_shell_sum_critical_bound {d : ℕ} {alpha : ℝ}
    (hcase : 2 * alpha = (d : ℝ) - 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ N : ℕ,
        (Finset.Icc 1 N).sum
            (fun m : ℕ =>
              Real.rpow (m : ℝ) ((d : ℝ) - 2 - 2 * alpha))
          ≤ C * Real.log ((N : ℝ) + 2) := by
  let C : ℝ := (Real.log (2 : ℝ))⁻¹ + 1
  have hlog2_pos : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro N
  have hexp : (d : ℝ) - 2 - 2 * alpha = -1 := by
    linarith
  have hsum_eq :
      (Finset.Icc 1 N).sum
          (fun m : ℕ =>
            Real.rpow (m : ℝ) ((d : ℝ) - 2 - 2 * alpha))
        = (Finset.Icc 1 N).sum (fun m : ℕ => 1 / (m : ℝ)) := by
    refine Finset.sum_congr rfl ?_
    intro m hm
    simp [hexp, Real.rpow_neg_one, one_div]
  have hharm :
      (Finset.Icc 1 N).sum (fun m : ℕ => 1 / (m : ℝ))
        ≤ 1 + Real.log (N : ℝ) := by
    have h := harmonic_le_one_add_log N
    rw [harmonic_eq_sum_Icc] at h
    simpa [one_div] using h
  have hlog_mono :
      Real.log (N : ℝ) ≤ Real.log ((N : ℝ) + 2) := by
    by_cases hN0 : N = 0
    · subst N
      simpa using (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
    · have hN_pos_nat : 0 < N := Nat.pos_of_ne_zero hN0
      have hN_pos : 0 < (N : ℝ) := by exact_mod_cast hN_pos_nat
      have hle : (N : ℝ) ≤ (N : ℝ) + 2 := by norm_num
      exact Real.log_le_log hN_pos hle
  have hone_le :
      1 ≤ (Real.log (2 : ℝ))⁻¹ * Real.log ((N : ℝ) + 2) := by
    have hlog_ge_two :
        Real.log (2 : ℝ) ≤ Real.log ((N : ℝ) + 2) := by
      refine Real.log_le_log (by norm_num) ?_
      norm_num
    calc
      (1 : ℝ) = (Real.log (2 : ℝ))⁻¹ * Real.log (2 : ℝ) := by
        field_simp [hlog2_pos.ne']
      _ ≤ (Real.log (2 : ℝ))⁻¹ * Real.log ((N : ℝ) + 2) :=
        mul_le_mul_of_nonneg_left hlog_ge_two (inv_nonneg.mpr hlog2_pos.le)
  have hgrowth :
      1 + Real.log (N : ℝ) ≤ C * Real.log ((N : ℝ) + 2) := by
    calc
      1 + Real.log (N : ℝ)
          ≤ (Real.log (2 : ℝ))⁻¹ * Real.log ((N : ℝ) + 2) +
              Real.log ((N : ℝ) + 2) := add_le_add hone_le hlog_mono
      _ = C * Real.log ((N : ℝ) + 2) := by
            dsimp [C]
            ring
  calc
    (Finset.Icc 1 N).sum
        (fun m : ℕ =>
          Real.rpow (m : ℝ) ((d : ℝ) - 2 - 2 * alpha))
        = (Finset.Icc 1 N).sum (fun m : ℕ => 1 / (m : ℝ)) := hsum_eq
    _ ≤ 1 + Real.log (N : ℝ) := hharm
    _ ≤ C * Real.log ((N : ℝ) + 2) := hgrowth

private lemma transverse_shell_sum_supercritical_bound {d : ℕ} {alpha : ℝ}
    (hcase : (d : ℝ) - 1 < 2 * alpha) :
    ∃ C : ℝ, 0 < C ∧
      ∀ N : ℕ,
        (Finset.Icc 1 N).sum
            (fun m : ℕ =>
              Real.rpow (m : ℝ) ((d : ℝ) - 2 - 2 * alpha))
          ≤ C := by
  let p : ℝ := (d : ℝ) - 2 - 2 * alpha
  have hp : p < -1 := by
    dsimp [p]
    linarith
  have hsumm : Summable (fun n : ℕ => Real.rpow (n : ℝ) p) :=
    Real.summable_nat_rpow.mpr hp
  refine ⟨(∑' n : ℕ, Real.rpow (n : ℝ) p) + 1, ?_, ?_⟩
  · have htsum_nonneg : 0 ≤ ∑' n : ℕ, Real.rpow (n : ℝ) p :=
      tsum_nonneg fun n => Real.rpow_nonneg (by positivity) p
    linarith
  · intro N
    have hsum_le :
        (Finset.Icc 1 N).sum (fun m : ℕ => Real.rpow (m : ℝ) p)
          ≤ ∑' n : ℕ, Real.rpow (n : ℝ) p :=
      hsumm.sum_le_tsum (Finset.Icc 1 N)
        (fun n _hn => Real.rpow_nonneg (by positivity) p)
    calc
      (Finset.Icc 1 N).sum
          (fun m : ℕ =>
            Real.rpow (m : ℝ) ((d : ℝ) - 2 - 2 * alpha))
          = (Finset.Icc 1 N).sum (fun m : ℕ => Real.rpow (m : ℝ) p) := by
              rfl
      _ ≤ ∑' n : ℕ, Real.rpow (n : ℝ) p := hsum_le
      _ ≤ (∑' n : ℕ, Real.rpow (n : ℝ) p) + 1 := by linarith

theorem firstCoordinateSliceWeightSum_subcritical {d : ℕ} (hd_pos : 0 < d)
    (halpha : AlphaLeDimHalf d alpha)
    (hcase : 2 * alpha < (d : ℝ) - 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ N : ℕ,
        firstCoordinateSliceWeightSum (d := d) hd_pos alpha N
          ≤ C * Real.rpow ((N : ℝ) + 1)
              ((d : ℝ) - 1 - 2 * alpha) := by
  classical
  by_cases hd1 : d = 1
  · subst d
    have hnonneg : 0 ≤ 2 * alpha := by linarith [halpha.nonneg]
    norm_num at hcase
    linarith
  · have hd_two : 2 ≤ d := by omega
    rcases transverse_shell_sum_subcritical_bound (d := d) (alpha := alpha) hcase with
      ⟨Csum, hCsum_pos, hCsum⟩
    refine ⟨((d : ℝ) + 1) * Csum, ?_, ?_⟩
    · exact mul_pos (by positivity) hCsum_pos
    · intro N
      have hslice :=
        firstCoordinateSliceWeightSum_le_sharp_transverse_shell_sum
          (d := d) (alpha := alpha) hd_two halpha N
      have hhd :
          (Nat.succ_pos _ |>.trans_le hd_two : 0 < d) = hd_pos := by
        exact Subsingleton.elim _ _
      rw [hhd] at hslice
      calc
        firstCoordinateSliceWeightSum (d := d) hd_pos alpha N
            ≤ ((d : ℝ) + 1) *
                (Finset.Icc 1 N).sum
                  (fun m : ℕ =>
                    Real.rpow (m : ℝ) ((d : ℝ) - 2 - 2 * alpha)) := hslice
        _ ≤ ((d : ℝ) + 1) *
              (Csum * Real.rpow ((N : ℝ) + 1)
                ((d : ℝ) - 1 - 2 * alpha)) := by
              exact mul_le_mul_of_nonneg_left (hCsum N) (by positivity)
        _ = (((d : ℝ) + 1) * Csum) *
              Real.rpow ((N : ℝ) + 1)
                ((d : ℝ) - 1 - 2 * alpha) := by ring

theorem firstCoordinateSliceWeightSum_critical {d : ℕ} (hd_pos : 0 < d)
    (halpha : AlphaLeDimHalf d alpha)
    (hcase : 2 * alpha = (d : ℝ) - 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ N : ℕ,
        firstCoordinateSliceWeightSum (d := d) hd_pos alpha N
          ≤ C * Real.log ((N : ℝ) + 2) := by
  classical
  by_cases hd1 : d = 1
  · subst d
    refine ⟨(Real.log (2 : ℝ))⁻¹, inv_pos.mpr (Real.log_pos (by norm_num)), ?_⟩
    intro N
    have hslice := firstCoordinateSliceWeightSum_d1 (N := N) alpha halpha
    have hlog2_pos : 0 < Real.log (2 : ℝ) :=
      Real.log_pos (by norm_num)
    have hlog_mono :
        Real.log (2 : ℝ) ≤ Real.log ((N : ℝ) + 2) := by
      refine Real.log_le_log (by norm_num) ?_
      norm_num
    have hone_le :
        1 ≤ (Real.log (2 : ℝ))⁻¹ * Real.log ((N : ℝ) + 2) := by
      calc
        (1 : ℝ) = (Real.log (2 : ℝ))⁻¹ * Real.log (2 : ℝ) := by
          field_simp [hlog2_pos.ne']
        _ ≤ (Real.log (2 : ℝ))⁻¹ * Real.log ((N : ℝ) + 2) :=
          mul_le_mul_of_nonneg_left hlog_mono (inv_nonneg.mpr hlog2_pos.le)
    exact hslice.trans hone_le
  · have hd_two : 2 ≤ d := by omega
    rcases transverse_shell_sum_critical_bound (d := d) (alpha := alpha) hcase with
      ⟨Csum, hCsum_pos, hCsum⟩
    refine ⟨((d : ℝ) + 1) * Csum, ?_, ?_⟩
    · exact mul_pos (by positivity) hCsum_pos
    · intro N
      have hslice :=
        firstCoordinateSliceWeightSum_le_sharp_transverse_shell_sum
          (d := d) (alpha := alpha) hd_two halpha N
      have hhd :
          (Nat.succ_pos _ |>.trans_le hd_two : 0 < d) = hd_pos := by
        exact Subsingleton.elim _ _
      rw [hhd] at hslice
      calc
        firstCoordinateSliceWeightSum (d := d) hd_pos alpha N
            ≤ ((d : ℝ) + 1) *
                (Finset.Icc 1 N).sum
                  (fun m : ℕ =>
                    Real.rpow (m : ℝ) ((d : ℝ) - 2 - 2 * alpha)) := hslice
        _ ≤ ((d : ℝ) + 1) * (Csum * Real.log ((N : ℝ) + 2)) := by
              exact mul_le_mul_of_nonneg_left (hCsum N) (by positivity)
        _ = (((d : ℝ) + 1) * Csum) * Real.log ((N : ℝ) + 2) := by ring

theorem firstCoordinateSliceWeightSum_supercritical {d : ℕ} (hd_pos : 0 < d)
    (halpha : AlphaLeDimHalf d alpha)
    (hcase : (d : ℝ) - 1 < 2 * alpha) :
    ∃ C : ℝ, 0 < C ∧
      ∀ N : ℕ,
        firstCoordinateSliceWeightSum (d := d) hd_pos alpha N ≤ C := by
  classical
  by_cases hd1 : d = 1
  · subst d
    refine ⟨1, zero_lt_one, ?_⟩
    intro N
    exact firstCoordinateSliceWeightSum_d1 (N := N) alpha halpha
  · have hd_two : 2 ≤ d := by omega
    rcases transverse_shell_sum_supercritical_bound (d := d) (alpha := alpha) hcase with
      ⟨Csum, hCsum_pos, hCsum⟩
    refine ⟨((d : ℝ) + 1) * Csum, ?_, ?_⟩
    · exact mul_pos (by positivity) hCsum_pos
    · intro N
      have hslice :=
        firstCoordinateSliceWeightSum_le_sharp_transverse_shell_sum
          (d := d) (alpha := alpha) hd_two halpha N
      have hhd :
          (Nat.succ_pos _ |>.trans_le hd_two : 0 < d) = hd_pos := by
        exact Subsingleton.elim _ _
      rw [hhd] at hslice
      calc
        firstCoordinateSliceWeightSum (d := d) hd_pos alpha N
            ≤ ((d : ℝ) + 1) *
                (Finset.Icc 1 N).sum
                  (fun m : ℕ =>
                    Real.rpow (m : ℝ) ((d : ℝ) - 2 - 2 * alpha)) := hslice
        _ ≤ ((d : ℝ) + 1) * Csum := by
              exact mul_le_mul_of_nonneg_left (hCsum N) (by positivity)

private lemma exp2piI_add (u v : ℝ) :
    exp2piI (u + v) = exp2piI u * exp2piI v := by
  unfold exp2piI
  rw [← Complex.exp_add]
  congr 1
  norm_num [Complex.ofReal_add, Complex.ofReal_mul]
  ring

private lemma norm_natVec_comp_perm {d : ℕ}
    (σ : Equiv.Perm (Fin d)) (k : Fin d → ℕ) :
    ‖natVec (k ∘ σ)‖ = ‖natVec k‖ := by
  calc
    ‖natVec (k ∘ σ)‖
        = Real.sqrt (∑ i : Fin d, ‖((k (σ i) : ℝ))‖ ^ 2) := by
          simp [natVec, toE, PiLp.norm_eq_of_L2]
    _ = Real.sqrt (∑ i : Fin d, ‖((k i : ℝ))‖ ^ 2) := by
          exact congrArg Real.sqrt
            (Equiv.sum_comp σ (fun i : Fin d => ‖((k i : ℝ))‖ ^ 2))
    _ = ‖natVec k‖ := by
          simp [natVec, toE, PiLp.norm_eq_of_L2]

private lemma a_comp_perm {d : ℕ}
    (σ : Equiv.Perm (Fin d)) (k : Fin d → ℕ) :
    a alpha (k ∘ σ) = a alpha k := by
  unfold a sobolevWeight sobolevPower
  rw [norm_natVec_comp_perm σ k]

private lemma norm_natVec_cons_mono {n : ℕ} (v : Fin n → ℕ)
    {k l : ℕ} (hkl : k ≤ l) :
    ‖natVec (Fin.cons k v)‖ ≤ ‖natVec (Fin.cons l v)‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  have hkl_real : (k : ℝ) ≤ (l : ℝ) := by exact_mod_cast hkl
  have hsq : ((k : ℝ) ^ 2) ≤ ((l : ℝ) ^ 2) := by
    exact (sq_le_sq₀ (Nat.cast_nonneg k) (Nat.cast_nonneg l)).2 hkl_real
  have hnorm_sq : ∀ m : ℕ,
      ‖natVec (Fin.cons m v)‖ ^ 2 =
        (m : ℝ) ^ 2 + ∑ i : Fin n, ‖(v i : ℝ)‖ ^ 2 := by
    intro m
    calc
      ‖natVec (Fin.cons m v)‖ ^ 2
          = ∑ i : Fin (n + 1), ‖coord (natVec (Fin.cons m v)) i‖ ^ 2 := by
            simp [coord, PiLp.norm_sq_eq_of_L2]
      _ = (m : ℝ) ^ 2 + ∑ i : Fin n, ‖(v i : ℝ)‖ ^ 2 := by
            simp [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  rw [hnorm_sq k, hnorm_sq l]
  simpa [add_comm, add_left_comm, add_assoc] using
    add_le_add_right hsq (∑ i : Fin n, ‖(v i : ℝ)‖ ^ 2)

private lemma a_cons_mono {n : ℕ}
    (halpha : AlphaLeDimHalf (n + 1) alpha)
    (v : Fin n → ℕ) {k l : ℕ} (_hk : 1 ≤ k) (hkl : k ≤ l) :
    a alpha (Fin.cons l v) ≤ a alpha (Fin.cons k v) := by
  have hnorm := norm_natVec_cons_mono (v := v) hkl
  have hweight :
      sobolevWeight alpha (natVec (Fin.cons k v)) ≤
        sobolevWeight alpha (natVec (Fin.cons l v)) := by
    unfold sobolevWeight sobolevPower
    by_cases hzero : alpha = 0
    · simp [hzero]
    · simp [hzero]
      exact Real.rpow_le_rpow (norm_nonneg _) hnorm (by linarith [halpha.nonneg])
  have hden :
      0 < sobolevWeight alpha (natVec (Fin.cons k v)) :=
    sobolevWeight_pos alpha (natVec (Fin.cons k v))
  unfold a
  simpa [one_div] using one_div_le_one_div_of_le hden hweight

private lemma inner_natVec_cons {n : ℕ}
    (m : ℕ) (v : Fin n → ℕ) (u : E (n + 1)) :
    inner ℝ (natVec (Fin.cons m v)) u =
      (m : ℝ) * coord u 0 +
        ∑ j : Fin n, (v j : ℝ) * coord u j.succ := by
  simp [natVec, toE, coord, PiLp.inner_apply, Fin.sum_univ_succ,
    Fin.cons_zero, Fin.cons_succ, mul_comm]

private lemma norm_exp2piI_local (u : ℝ) :
    ‖exp2piI u‖ = 1 := by
  simp [exp2piI, Complex.norm_exp]

private lemma firstCoordinateSliceWeightSum_succ_eq {n N : ℕ}
    (alpha : ℝ) (hN : 1 ≤ N) :
    firstCoordinateSliceWeightSum (d := n + 1) (Nat.succ_pos n) alpha N =
      (indexBox n N).sum (fun v => a alpha (Fin.cons 1 v)) := by
  classical
  unfold firstCoordinateSliceWeightSum indexBox a
  change
    ((Fintype.piFinset fun _ : Fin (n + 1) => Finset.Icc 1 N).filter
        (fun k => k (0 : Fin (n + 1)) = 1)
      ).sum (fun k => 1 / sobolevWeight alpha (natVec k)) =
      (Fintype.piFinset fun _ : Fin n => Finset.Icc 1 N).sum
        (fun v => 1 / sobolevWeight alpha (natVec (Fin.cons 1 v)))
  rw [← Fintype.piFinset_update_singleton_eq_filter_piFinset_eq
    (s := fun _ : Fin (n + 1) => Finset.Icc 1 N)
    (i := (0 : Fin (n + 1))) (a := 1)]
  · rw [← Finset.filter_true
        (Fintype.piFinset (Function.update (fun _ : Fin (n + 1) => Finset.Icc 1 N) 0 {1}))]
    rw [Finset.filter_piFinset_eq_map_consEquiv
      (S := Function.update (fun _ : Fin (n + 1) => Finset.Icc 1 N) 0 {1})
      (P := fun _ : Fin n → ℕ => True)]
    rw [Finset.sum_map]
    have htailS :
        Fin.tail (Function.update (fun _ : Fin (n + 1) => Finset.Icc 1 N) 0 {1}) =
          (fun _ : Fin n => Finset.Icc 1 N) := by
      funext i
      simp [Fin.tail, Function.update]
    rw [htailS]
    simp only [Function.update_self, Finset.filter_true]
    rw [Finset.sum_product]
    simp only [Finset.sum_singleton]
    change
      (Fintype.piFinset fun _ : Fin n => Finset.Icc 1 N).sum
          (fun x : Fin n → ℕ =>
            1 / sobolevWeight alpha
              (natVec ((Fin.consEquiv (fun _ : Fin (n + 1) => ℕ)) (1, x)))) =
        (Fintype.piFinset fun _ : Fin n => Finset.Icc 1 N).sum
          (fun x : Fin n → ℕ =>
            1 / sobolevWeight alpha (natVec (Fin.cons 1 x)))
    refine Finset.sum_congr rfl ?_
    intro x hx
    have hxfun :
        (Fin.consEquiv (fun _ : Fin (n + 1) => ℕ)) (1, x) = Fin.cons 1 x := by
      ext i
      cases i using Fin.cases <;> simp [Fin.consEquiv_apply]
    rw [hxfun]
  · simp [hN]

private lemma weighted_sum_bound_first_coordinate_succ
    {n : ℕ} (halpha : AlphaLeDimHalf (n + 1) alpha)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ C : ℝ, 0 < C ∧
      ∀ u : E (n + 1),
      (∀ m : ℤ, delta ≤ |coord u 0 - (m : ℝ)|) →
      ∀ N : ℕ,
        ‖(indexBox (n + 1) N).sum
          (fun k => ((a alpha k : ℝ) : ℂ) *
            exp2piI (inner ℝ (natVec k) u))‖
          ≤ C * firstCoordinateSliceWeightSum (d := n + 1) (Nat.succ_pos n) alpha N := by
  classical
  rcases geometric_partial_sums_bounded_in_coordinate hdelta with
    ⟨Cgeom, hCgeom_pos, hgeom⟩
  refine ⟨2 * Cgeom, mul_pos (by norm_num) hCgeom_pos, ?_⟩
  intro u hu N
  by_cases hN : 1 ≤ N
  · have hbox_split :
        (indexBox (n + 1) N).sum
          (fun k => ((a alpha k : ℝ) : ℂ) *
            exp2piI (inner ℝ (natVec k) u)) =
        (indexBox n N).sum
          (fun v =>
            (Finset.Icc 1 N).sum
              (fun m : ℕ =>
                ((a alpha (Fin.cons m v) : ℝ) : ℂ) *
                  exp2piI (inner ℝ (natVec (Fin.cons m v)) u))) := by
      unfold indexBox
      rw [← Finset.filter_true
        (Fintype.piFinset fun _ : Fin (n + 1) => Finset.Icc 1 N)]
      rw [Finset.filter_piFinset_eq_map_consEquiv
        (S := fun _ : Fin (n + 1) => Finset.Icc 1 N)
        (P := fun _ : Fin n → ℕ => True)]
      rw [Finset.sum_map]
      simp only [Finset.filter_true]
      rw [Finset.sum_product]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro v hv
      refine Finset.sum_congr rfl ?_
      intro m hm
      have hfun :
          (Fin.consEquiv (fun _ : Fin (n + 1) => ℕ)).toEmbedding (m, v) =
            Fin.cons m v := by
        ext j
        cases j using Fin.cases <;> simp [Fin.consEquiv_apply]
      rw [hfun]
    have hinner_bound :
        ∀ v ∈ indexBox n N,
          ‖(Finset.Icc 1 N).sum
              (fun m : ℕ =>
                ((a alpha (Fin.cons m v) : ℝ) : ℂ) *
                  exp2piI (inner ℝ (natVec (Fin.cons m v)) u))‖
            ≤ 2 * Cgeom * a alpha (Fin.cons 1 v) := by
      intro v hv
      let transverse : ℝ := ∑ j : Fin n, (v j : ℝ) * coord u j.succ
      have hsum_factor :
          (Finset.Icc 1 N).sum
              (fun m : ℕ =>
                ((a alpha (Fin.cons m v) : ℝ) : ℂ) *
                  exp2piI (inner ℝ (natVec (Fin.cons m v)) u)) =
            exp2piI transverse *
              (Finset.Icc 1 N).sum
                (fun m : ℕ =>
                  ((a alpha (Fin.cons m v) : ℝ) : ℂ) *
                    exp2piI ((m : ℝ) * coord u 0)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro m hm
        have hinner := inner_natVec_cons (m := m) (v := v) (u := u)
        dsimp [transverse] at hinner ⊢
        rw [hinner, exp2piI_add]
        ring
      have habel :
          ‖(Finset.Icc 1 N).sum
              (fun m : ℕ =>
                ((a alpha (Fin.cons m v) : ℝ) : ℂ) *
                  exp2piI ((m : ℝ) * coord u 0))‖
            ≤ 2 * Cgeom * a alpha (Fin.cons 1 v) := by
        refine abel_summation_one_coordinate
          (N := N) (u := coord u 0)
          (w := fun m => a alpha (Fin.cons m v))
          (Cgeom := Cgeom) hN hCgeom_pos.le ?_ ?_ ?_
        · intro m
          exact hgeom (coord u 0) hu m
        · intro m hm
          exact a_nonneg halpha (Fin.cons m v)
        · intro k l hk hkl hlN
          exact a_cons_mono halpha v hk hkl
      calc
        ‖(Finset.Icc 1 N).sum
            (fun m : ℕ =>
              ((a alpha (Fin.cons m v) : ℝ) : ℂ) *
                exp2piI (inner ℝ (natVec (Fin.cons m v)) u))‖
            = ‖exp2piI transverse‖ *
                ‖(Finset.Icc 1 N).sum
                  (fun m : ℕ =>
                    ((a alpha (Fin.cons m v) : ℝ) : ℂ) *
                      exp2piI ((m : ℝ) * coord u 0))‖ := by
              rw [hsum_factor, norm_mul]
        _ = ‖(Finset.Icc 1 N).sum
                  (fun m : ℕ =>
                    ((a alpha (Fin.cons m v) : ℝ) : ℂ) *
                      exp2piI ((m : ℝ) * coord u 0))‖ := by
              rw [norm_exp2piI_local, one_mul]
        _ ≤ 2 * Cgeom * a alpha (Fin.cons 1 v) := habel
    calc
      ‖(indexBox (n + 1) N).sum
          (fun k => ((a alpha k : ℝ) : ℂ) *
            exp2piI (inner ℝ (natVec k) u))‖
          =
        ‖(indexBox n N).sum
          (fun v =>
            (Finset.Icc 1 N).sum
              (fun m : ℕ =>
                ((a alpha (Fin.cons m v) : ℝ) : ℂ) *
                  exp2piI (inner ℝ (natVec (Fin.cons m v)) u)))‖ := by
            rw [hbox_split]
      _ ≤ (indexBox n N).sum
          (fun v =>
            ‖(Finset.Icc 1 N).sum
              (fun m : ℕ =>
                ((a alpha (Fin.cons m v) : ℝ) : ℂ) *
                  exp2piI (inner ℝ (natVec (Fin.cons m v)) u))‖) :=
            norm_sum_le _ _
      _ ≤ (indexBox n N).sum
          (fun v => 2 * Cgeom * a alpha (Fin.cons 1 v)) :=
            Finset.sum_le_sum hinner_bound
      _ = (2 * Cgeom) *
          firstCoordinateSliceWeightSum (d := n + 1) (Nat.succ_pos n) alpha N := by
            rw [firstCoordinateSliceWeightSum_succ_eq alpha hN]
            rw [Finset.mul_sum]
  · have hN0 : N = 0 := by omega
    subst N
    have hbox_empty : indexBox (n + 1) 0 = ∅ := by
      ext k
      simp [indexBox]
    rw [hbox_empty]
    simp
    have hslice_nonneg :
        0 ≤ firstCoordinateSliceWeightSum (d := n + 1) (Nat.succ_pos n) alpha 0 := by
      unfold firstCoordinateSliceWeightSum
      exact Finset.sum_nonneg fun k hk =>
        one_div_nonneg.mpr (sobolevWeight_nonneg alpha (natVec k))
    exact mul_nonneg (mul_nonneg zero_le_two hCgeom_pos.le)
      hslice_nonneg

theorem weighted_sum_bound_by_slice_after_coordinate_permutation
    {d : ℕ} (hd_pos : 0 < d)
    (halpha : AlphaLeDimHalf d alpha)
    {i : Fin d} {delta : ℝ} (hdelta : 0 < delta) :
    ∃ C : ℝ, 0 < C ∧
      ∀ u : E d,
      (∀ m : ℤ, delta ≤ |coord u i - (m : ℝ)|) →
      ∀ N : ℕ,
        ‖(indexBox d N).sum
          (fun k => ((a alpha k : ℝ) : ℂ) *
            exp2piI (inner ℝ (natVec k) u))‖
          ≤ C * firstCoordinateSliceWeightSum (d := d) hd_pos alpha N := by
  classical
  cases d with
  | zero => omega
  | succ n =>
      let σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap (0 : Fin (n + 1)) i
      rcases weighted_sum_bound_first_coordinate_succ
          (n := n) (alpha := alpha) halpha hdelta with
        ⟨C, hCpos, hC⟩
      refine ⟨C, hCpos, ?_⟩
      intro u hu N
      let u' : E (n + 1) := toE fun j => coord u (σ j)
      have hu' : ∀ m : ℤ, delta ≤ |coord u' 0 - (m : ℝ)| := by
        intro m
        simpa [u', σ] using hu m
      have hsum_eq :
          (indexBox (n + 1) N).sum
            (fun k => ((a alpha k : ℝ) : ℂ) *
              exp2piI (inner ℝ (natVec k) u)) =
          (indexBox (n + 1) N).sum
            (fun k => ((a alpha k : ℝ) : ℂ) *
              exp2piI (inner ℝ (natVec k) u')) := by
        let b : (Fin (n + 1) → ℕ) → ℂ :=
          fun k => ((a alpha k : ℝ) : ℂ)
        have hperm :=
          coeffPolynomial_coordinate_permutation
            (d := n + 1) (N := N) σ b u
        calc
          (indexBox (n + 1) N).sum
              (fun k => ((a alpha k : ℝ) : ℂ) *
                exp2piI (inner ℝ (natVec k) u))
              = coeffPolynomial N b u := by
                rfl
          _ = coeffPolynomial N (fun k => b (k ∘ σ.symm)) u' := by
                simpa [u'] using hperm
          _ =
            (indexBox (n + 1) N).sum
              (fun k => ((a alpha k : ℝ) : ℂ) *
                exp2piI (inner ℝ (natVec k) u')) := by
              unfold coeffPolynomial
              refine Finset.sum_congr rfl ?_
              intro k hk
              dsimp [b]
              rw [a_comp_perm (σ := σ.symm) (k := k)]
      have hslice_eq :
          firstCoordinateSliceWeightSum (d := n + 1) (Nat.succ_pos n) alpha N =
            firstCoordinateSliceWeightSum (d := n + 1) hd_pos alpha N := by
        simp [firstCoordinateSliceWeightSum]
      calc
        ‖(indexBox (n + 1) N).sum
            (fun k => ((a alpha k : ℝ) : ℂ) *
              exp2piI (inner ℝ (natVec k) u))‖
            =
          ‖(indexBox (n + 1) N).sum
            (fun k => ((a alpha k : ℝ) : ℂ) *
              exp2piI (inner ℝ (natVec k) u'))‖ := by
            rw [hsum_eq]
        _ ≤ C *
            firstCoordinateSliceWeightSum (d := n + 1) (Nat.succ_pos n) alpha N :=
            hC u' hu' N
        _ = C * firstCoordinateSliceWeightSum (d := n + 1) hd_pos alpha N := by
            rw [hslice_eq]

private lemma firstCoordinateSliceWeightSum_nonneg {d : ℕ} (hd_pos : 0 < d)
    (alpha : ℝ) (N : ℕ) :
    0 ≤ firstCoordinateSliceWeightSum (d := d) hd_pos alpha N := by
  unfold firstCoordinateSliceWeightSum
  exact Finset.sum_nonneg fun k hk =>
    one_div_nonneg.mpr (sobolevWeight_nonneg alpha (natVec k))

private lemma div_le_div_of_le_of_le_pos
    {s u b l : ℝ}
    (hsu : s ≤ u) (hlb : l ≤ b) (hu : 0 ≤ u) (hl : 0 < l) :
    s / b ≤ u / l := by
  have hb : 0 < b := hl.trans_le hlb
  exact (div_le_div_of_nonneg_right hsu hb.le).trans
    (div_le_div_of_nonneg_left hu hl hlb)

private lemma tendsto_rpow_add_one_div_rpow_add_one
    {q : ℝ} (hq : 0 ≤ q) :
    Tendsto
      (fun N : ℕ =>
        Real.rpow ((N : ℝ) + 1) q / Real.rpow (N : ℝ) (q + 1))
      atTop (nhds 0) := by
  refine squeeze_zero'
    (f := fun N : ℕ =>
      Real.rpow ((N : ℝ) + 1) q / Real.rpow (N : ℝ) (q + 1))
    (g := fun N : ℕ => Real.rpow 2 q / (N : ℝ)) ?_ ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with N hN
    have hN_nonneg : 0 ≤ (N : ℝ) := by positivity
    exact div_nonneg
      (Real.rpow_nonneg (add_nonneg hN_nonneg zero_le_one) q)
      (Real.rpow_nonneg hN_nonneg (q + 1))
  · filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with N hN
    have hN_pos : 0 < (N : ℝ) := by exact_mod_cast hN
    have hN_nonneg : 0 ≤ (N : ℝ) := hN_pos.le
    have hN_ge_one : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hbase_nonneg : 0 ≤ (N : ℝ) + 1 :=
      add_nonneg hN_nonneg zero_le_one
    have hbase_le : (N : ℝ) + 1 ≤ 2 * (N : ℝ) := by
      nlinarith
    have hpow_le :
        Real.rpow ((N : ℝ) + 1) q ≤ Real.rpow (2 * (N : ℝ)) q :=
      Real.rpow_le_rpow hbase_nonneg hbase_le hq
    have hden_nonneg : 0 ≤ Real.rpow (N : ℝ) (q + 1) :=
      Real.rpow_nonneg hN_nonneg _
    calc
      Real.rpow ((N : ℝ) + 1) q / Real.rpow (N : ℝ) (q + 1)
          ≤ Real.rpow (2 * (N : ℝ)) q / Real.rpow (N : ℝ) (q + 1) :=
            div_le_div_of_nonneg_right hpow_le hden_nonneg
      _ = Real.rpow 2 q / (N : ℝ) := by
            have htwo_nonneg : 0 ≤ (2 : ℝ) := by norm_num
            have hNq_pos : 0 < Real.rpow (N : ℝ) q :=
              Real.rpow_pos_of_pos hN_pos q
            rw [show Real.rpow (2 * (N : ℝ)) q =
                Real.rpow 2 q * Real.rpow (N : ℝ) q by
              exact Real.mul_rpow htwo_nonneg hN_nonneg]
            rw [show Real.rpow (N : ℝ) (q + 1) =
                Real.rpow (N : ℝ) q * (N : ℝ) by
              calc
                Real.rpow (N : ℝ) (q + 1)
                    = Real.rpow (N : ℝ) q * Real.rpow (N : ℝ) 1 :=
                      Real.rpow_add hN_pos q 1
                _ = Real.rpow (N : ℝ) q * (N : ℝ) := by
                      have h1 : Real.rpow (N : ℝ) 1 = (N : ℝ) :=
                        Real.rpow_one (N : ℝ)
                      rw [h1]]
            field_simp [hN_pos.ne', hNq_pos.ne']
  · exact (tendsto_const_nhds (x := Real.rpow 2 q)).div_atTop
      (tendsto_natCast_atTop_atTop (R := ℝ))

private lemma tendsto_log_nat_add_two_div_nat :
    Tendsto
      (fun N : ℕ => Real.log ((N : ℝ) + 2) / (N : ℝ))
      atTop (nhds 0) := by
  have hlog_id_real :
      Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) := by
    simpa [Real.rpow_one] using
      (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 by norm_num)).tendsto_div_nhds_zero
  have hlog_id_nat :
      Tendsto (fun N : ℕ => Real.log (N : ℝ) / (N : ℝ))
        atTop (nhds 0) :=
    hlog_id_real.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hconst :
      Tendsto (fun N : ℕ => Real.log 3 / (N : ℝ)) atTop (nhds 0) :=
    (tendsto_const_nhds (x := Real.log 3)).div_atTop
      (tendsto_natCast_atTop_atTop (R := ℝ))
  refine squeeze_zero'
    (f := fun N : ℕ => Real.log ((N : ℝ) + 2) / (N : ℝ))
    (g := fun N : ℕ =>
      Real.log 3 / (N : ℝ) + Real.log (N : ℝ) / (N : ℝ)) ?_ ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with N hN
    have hN_pos : 0 < (N : ℝ) := by exact_mod_cast hN
    have hlog_nonneg : 0 ≤ Real.log ((N : ℝ) + 2) := by
      exact Real.log_nonneg (by nlinarith)
    exact div_nonneg hlog_nonneg hN_pos.le
  · filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with N hN
    have hN_pos : 0 < (N : ℝ) := by exact_mod_cast hN
    have hN_ge_one : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have harg_pos : 0 < (N : ℝ) + 2 := by nlinarith
    have hprod_pos : 0 < 3 * (N : ℝ) := by positivity
    have harg_le : (N : ℝ) + 2 ≤ 3 * (N : ℝ) := by nlinarith
    have hlog_le : Real.log ((N : ℝ) + 2) ≤ Real.log (3 * (N : ℝ)) :=
      Real.log_le_log harg_pos harg_le
    calc
      Real.log ((N : ℝ) + 2) / (N : ℝ)
          ≤ Real.log (3 * (N : ℝ)) / (N : ℝ) :=
            div_le_div_of_nonneg_right hlog_le hN_pos.le
      _ = Real.log 3 / (N : ℝ) + Real.log (N : ℝ) / (N : ℝ) := by
            rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hN_pos.ne']
            ring
  · simpa using hconst.add hlog_id_nat

theorem normalized_sliceWeight_tendsto_zero {d : ℕ} (hd_pos : 0 < d)
    (halpha : AlphaLeDimHalf d alpha) :
    Tendsto
      (fun N : ℕ =>
        firstCoordinateSliceWeightSum (d := d) hd_pos alpha N / B d alpha N)
      atTop (nhds 0) := by
  have hratio_nonneg :
      ∀ᶠ N : ℕ in atTop,
        0 ≤ firstCoordinateSliceWeightSum (d := d) hd_pos alpha N /
          B d alpha N := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with N hN
    exact div_nonneg
      (firstCoordinateSliceWeightSum_nonneg hd_pos alpha N)
      (B_pos halpha hN).le
  rcases lt_trichotomy (2 * alpha) ((d : ℝ) - 1) with htrans | htrans | htrans
  · rcases firstCoordinateSliceWeightSum_subcritical hd_pos halpha htrans with
      ⟨Cs, hCspos, hS⟩
    have hglobal : 2 * alpha < (d : ℝ) := by linarith
    rcases B_lower_bound_subcritical hd_pos halpha hglobal with
      ⟨Cb, hCbpos, hB⟩
    let q : ℝ := (d : ℝ) - 1 - 2 * alpha
    have hq_nonneg : 0 ≤ q := by
      dsimp [q]
      linarith
    refine squeeze_zero'
      (f := fun N : ℕ =>
        firstCoordinateSliceWeightSum (d := d) hd_pos alpha N / B d alpha N)
      (g := fun N : ℕ =>
        (Cs / Cb) *
          (Real.rpow ((N : ℝ) + 1) q / Real.rpow (N : ℝ) (q + 1)))
      hratio_nonneg ?_ ?_
    · filter_upwards [hB, Filter.eventually_ge_atTop (1 : ℕ)] with N hBN hN
      have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
      have hNnonneg : 0 ≤ (N : ℝ) := hNpos.le
      have hbase_nonneg : 0 ≤ (N : ℝ) + 1 :=
        add_nonneg hNnonneg zero_le_one
      have hU_nonneg :
          0 ≤ Cs * Real.rpow ((N : ℝ) + 1) q :=
        mul_nonneg hCspos.le (Real.rpow_nonneg hbase_nonneg q)
      have hL_pos :
          0 < Cb * Real.rpow (N : ℝ) ((d : ℝ) - 2 * alpha) :=
        mul_pos hCbpos (Real.rpow_pos_of_pos hNpos _)
      have hmain :
          firstCoordinateSliceWeightSum (d := d) hd_pos alpha N / B d alpha N
            ≤
          (Cs * Real.rpow ((N : ℝ) + 1) q) /
            (Cb * Real.rpow (N : ℝ) ((d : ℝ) - 2 * alpha)) :=
        div_le_div_of_le_of_le_pos (hS N) hBN hU_nonneg hL_pos
      calc
        firstCoordinateSliceWeightSum (d := d) hd_pos alpha N / B d alpha N
            ≤
          (Cs * Real.rpow ((N : ℝ) + 1) q) /
            (Cb * Real.rpow (N : ℝ) ((d : ℝ) - 2 * alpha)) := hmain
        _ =
          (Cs / Cb) *
            (Real.rpow ((N : ℝ) + 1) q / Real.rpow (N : ℝ) (q + 1)) := by
            have hp_eq : (d : ℝ) - 2 * alpha = q + 1 := by
              dsimp [q]
              ring
            have hpow_pos : 0 < Real.rpow (N : ℝ) (q + 1) :=
              Real.rpow_pos_of_pos hNpos _
            rw [hp_eq]
            field_simp [hCbpos.ne', hpow_pos.ne']
    · simpa using
        (tendsto_rpow_add_one_div_rpow_add_one (q := q) hq_nonneg).const_mul
          (Cs / Cb)
  · rcases firstCoordinateSliceWeightSum_critical hd_pos halpha htrans with
      ⟨Cs, hCspos, hS⟩
    have hglobal : 2 * alpha < (d : ℝ) := by
      have hdim : (d : ℝ) - 1 < (d : ℝ) := by norm_num
      linarith
    rcases B_lower_bound_subcritical hd_pos halpha hglobal with
      ⟨Cb, hCbpos, hB⟩
    refine squeeze_zero'
      (f := fun N : ℕ =>
        firstCoordinateSliceWeightSum (d := d) hd_pos alpha N / B d alpha N)
      (g := fun N : ℕ =>
        (Cs / Cb) * (Real.log ((N : ℝ) + 2) / (N : ℝ)))
      hratio_nonneg ?_ ?_
    · filter_upwards [hB, Filter.eventually_ge_atTop (1 : ℕ)] with N hBN hN
      have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
      have hlog_nonneg : 0 ≤ Real.log ((N : ℝ) + 2) :=
        Real.log_nonneg (by nlinarith)
      have hU_nonneg : 0 ≤ Cs * Real.log ((N : ℝ) + 2) :=
        mul_nonneg hCspos.le hlog_nonneg
      have hL_pos :
          0 < Cb * Real.rpow (N : ℝ) ((d : ℝ) - 2 * alpha) :=
        mul_pos hCbpos (Real.rpow_pos_of_pos hNpos _)
      have hmain :
          firstCoordinateSliceWeightSum (d := d) hd_pos alpha N / B d alpha N
            ≤
          (Cs * Real.log ((N : ℝ) + 2)) /
            (Cb * Real.rpow (N : ℝ) ((d : ℝ) - 2 * alpha)) :=
        div_le_div_of_le_of_le_pos (hS N) hBN hU_nonneg hL_pos
      calc
        firstCoordinateSliceWeightSum (d := d) hd_pos alpha N / B d alpha N
            ≤
          (Cs * Real.log ((N : ℝ) + 2)) /
            (Cb * Real.rpow (N : ℝ) ((d : ℝ) - 2 * alpha)) := hmain
        _ =
          (Cs / Cb) * (Real.log ((N : ℝ) + 2) / (N : ℝ)) := by
            have hp_eq : (d : ℝ) - 2 * alpha = 1 := by
              linarith
            have hpow_one : Real.rpow (N : ℝ) 1 = (N : ℝ) :=
              Real.rpow_one (N : ℝ)
            rw [hp_eq, hpow_one]
            field_simp [hCbpos.ne', hNpos.ne']
    · simpa using tendsto_log_nat_add_two_div_nat.const_mul (Cs / Cb)
  · rcases firstCoordinateSliceWeightSum_supercritical hd_pos halpha htrans with
      ⟨Cs, hCspos, hS⟩
    have h_inv :
        Tendsto (fun N : ℕ => (B d alpha N)⁻¹) atTop (nhds 0) :=
      Filter.Tendsto.inv_tendsto_atTop (B_tendsto_atTop hd_pos halpha)
    refine squeeze_zero'
      (f := fun N : ℕ =>
        firstCoordinateSliceWeightSum (d := d) hd_pos alpha N / B d alpha N)
      (g := fun N : ℕ => Cs * (B d alpha N)⁻¹)
      hratio_nonneg ?_ ?_
    · filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with N hN
      have hBpos : 0 < B d alpha N := B_pos halpha hN
      calc
        firstCoordinateSliceWeightSum (d := d) hd_pos alpha N / B d alpha N
            ≤ Cs / B d alpha N :=
              div_le_div_of_nonneg_right (hS N) hBpos.le
        _ = Cs * (B d alpha N)⁻¹ := by rw [div_eq_mul_inv]
    · simpa using h_inv.const_mul Cs

theorem Q_eventually_small_uniformOn_coordinate_away
    {d : ℕ} (hd_pos : 0 < d)
    (halpha : AlphaLeDimHalf d alpha)
    {i : Fin d} {delta : ℝ} (hdelta : 0 < delta) :
    ∀ eps > 0,
      ∀ᶠ N in atTop,
        ∀ u : E d,
          (∀ m : ℤ, delta ≤ |coord u i - (m : ℝ)|) →
          ‖Q (d := d) alpha N u‖ < eps := by
  rcases weighted_sum_bound_by_slice_after_coordinate_permutation
      hd_pos halpha hdelta with ⟨C, hCpos, hC⟩
  intro eps heps
  have h_ratio :
      Tendsto
        (fun N : ℕ =>
          C * (firstCoordinateSliceWeightSum (d := d) hd_pos alpha N /
            B d alpha N))
        atTop (nhds 0) := by
    simpa using
      (normalized_sliceWeight_tendsto_zero hd_pos halpha).const_mul C
  have h_event :
      ∀ᶠ N : ℕ in atTop,
        C * (firstCoordinateSliceWeightSum (d := d) hd_pos alpha N /
          B d alpha N) < eps :=
    h_ratio (Iio_mem_nhds heps)
  filter_upwards [h_event, Filter.eventually_ge_atTop (1 : ℕ)] with
    N hsmall hN u hu
  have hBpos : 0 < B d alpha N := B_pos halpha hN
  let numerator : ℂ :=
    (indexBox d N).sum
      (fun k => ((a alpha k : ℝ) : ℂ) *
        exp2piI (inner ℝ (natVec k) u))
  have hQ_eq :
      Q (d := d) alpha N u =
        (((B d alpha N : ℝ) : ℂ)⁻¹) * numerator := by
    calc
      Q (d := d) alpha N u
          =
        (indexBox d N).sum
          (fun k =>
            (((B d alpha N : ℝ) : ℂ)⁻¹) *
              (((a alpha k : ℝ) : ℂ) *
                exp2piI (inner ℝ (natVec k) u))) := by
            unfold Q coeffPolynomial
            refine Finset.sum_congr rfl ?_
            intro k hk
            simp [c, hk, div_eq_mul_inv, mul_assoc, mul_comm]
      _ = (((B d alpha N : ℝ) : ℂ)⁻¹) * numerator := by
            rw [Finset.mul_sum]
  have hBnorm : ‖((B d alpha N : ℝ) : ℂ)‖ = B d alpha N := by
    rw [← Real.norm_of_nonneg hBpos.le]
    norm_num
  have hnum :
      ‖numerator‖
        ≤ C * firstCoordinateSliceWeightSum (d := d) hd_pos alpha N := by
    simpa [numerator] using hC u hu N
  calc
    ‖Q (d := d) alpha N u‖
        = (B d alpha N)⁻¹ * ‖numerator‖ := by
          rw [hQ_eq, norm_mul, norm_inv, hBnorm]
    _ ≤ (B d alpha N)⁻¹ *
          (C * firstCoordinateSliceWeightSum (d := d) hd_pos alpha N) :=
          mul_le_mul_of_nonneg_left hnum (inv_nonneg.mpr hBpos.le)
    _ = C * (firstCoordinateSliceWeightSum (d := d) hd_pos alpha N /
          B d alpha N) := by
          rw [div_eq_mul_inv]
          ring
    _ < eps := hsmall

theorem compact_coordinate_away_decomposition {d : ℕ} (hd_pos : 0 < d)
    {K : Set (E d)}
    (hK : IsCompact K)
    (hK_away : ∀ u ∈ K, u ∉ integerLattice d) :
    ∃ I : Finset (Fin d),
    ∃ Kcoord : Fin d → Set (E d),
    ∃ delta : Fin d → ℝ,
      (∀ i ∈ I, 0 < delta i) ∧
      (∀ i ∈ I, IsCompact (Kcoord i)) ∧
      (∀ i ∈ I, Kcoord i ⊆ K) ∧
      K ⊆ {u | ∃ i ∈ I, u ∈ Kcoord i} ∧
      (∀ i ∈ I, ∀ u ∈ Kcoord i,
        ∀ m : ℤ, delta i ≤ |coord u i - (m : ℝ)|) := by
  rcases compact_pos_dist_to_integerLattice hd_pos hK hK_away with
    ⟨rho, hrho_pos, hrho⟩
  let delta0 : ℝ := rho / (2 * Real.sqrt (d : ℝ))
  have hd_real_pos : 0 < (d : ℝ) := by exact_mod_cast hd_pos
  have hsqrtd_pos : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 hd_real_pos
  have hdelta0_pos : 0 < delta0 :=
    div_pos hrho_pos (mul_pos (by norm_num) hsqrtd_pos)
  let Kcoord : Fin d → Set (E d) := fun i =>
    K ∩ {u | ∀ m : ℤ, delta0 ≤ |coord u i - (m : ℝ)|}
  let delta : Fin d → ℝ := fun _ => delta0
  have hclosed_away :
      ∀ i : Fin d,
        IsClosed {u : E d | ∀ m : ℤ, delta0 ≤ |coord u i - (m : ℝ)|} := by
    intro i
    rw [show
        {u : E d | ∀ m : ℤ, delta0 ≤ |coord u i - (m : ℝ)|}
          =
        ⋂ m : ℤ, {u : E d | delta0 ≤ |coord u i - (m : ℝ)|} by
          ext u
          simp]
    refine isClosed_iInter fun m => ?_
    have hcont :
        Continuous (fun u : E d => |coord u i - (m : ℝ)|) :=
      continuous_abs.comp ((continuous_coord i).sub continuous_const)
    exact isClosed_Ici.preimage hcont
  refine ⟨Finset.univ, Kcoord, delta, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact hdelta0_pos
  · intro i hi
    exact hK.inter_right (hclosed_away i)
  · intro i hi u hu
    exact hu.1
  · intro u huK
    rcases exists_coordinate_away_from_int hd_pos hrho_pos (u := u)
        (hrho u huK) with ⟨i, hi⟩
    exact ⟨i, Finset.mem_univ i, huK, hi⟩
  · intro i hi u hu m
    exact hu.2 m

theorem compact_covered_by_coordinate_away_sets {d : ℕ} (hd_pos : 0 < d)
    {K : Set (E d)}
    (hK : IsCompact K)
    (hK_away : ∀ u ∈ K, u ∉ integerLattice d) :
    ∃ I : Finset (Fin d),
    ∃ delta : Fin d → ℝ,
      (∀ i ∈ I, 0 < delta i) ∧
      K ⊆ {u | ∃ i ∈ I, ∀ m : ℤ, delta i ≤ |coord u i - (m : ℝ)|} := by
  rcases compact_coordinate_away_decomposition hd_pos hK hK_away with
    ⟨I, Kcoord, delta, hdelta_pos, hKcoord_compact, hKcoord_sub,
      hcover, haway⟩
  refine ⟨I, delta, hdelta_pos, ?_⟩
  intro u hu
  rcases hcover hu with ⟨i, hi, hui⟩
  exact ⟨i, hi, haway i hi u hui⟩

theorem Q_eventually_small_uniformOn_compact_away_lattice
    {d : ℕ} (hd_pos : 0 < d)
    (halpha : AlphaLeDimHalf d alpha)
    {K : Set (E d)}
    (hK : IsCompact K)
    (hK_away : ∀ u ∈ K, u ∉ integerLattice d) :
    ∀ eps > 0,
      ∀ᶠ N in atTop, ∀ u ∈ K, ‖Q (d := d) alpha N u‖ < eps := by
  rcases compact_covered_by_coordinate_away_sets hd_pos hK hK_away with
    ⟨I, delta, hdelta_pos, hcover⟩
  intro eps heps
  have h_each :
      ∀ i ∈ I,
        ∀ᶠ N in atTop,
          ∀ u : E d,
            (∀ m : ℤ, delta i ≤ |coord u i - (m : ℝ)|) →
            ‖Q (d := d) alpha N u‖ < eps := by
    intro i hi
    exact Q_eventually_small_uniformOn_coordinate_away
      hd_pos halpha (hdelta_pos i hi) eps heps
  have h_all :
      ∀ᶠ N in atTop,
        ∀ i ∈ I, ∀ u : E d,
          (∀ m : ℤ, delta i ≤ |coord u i - (m : ℝ)|) →
          ‖Q (d := d) alpha N u‖ < eps := by
    exact (Filter.eventually_all_finset I).2 h_each
  filter_upwards [h_all] with N hN u hu
  rcases hcover hu with ⟨i, hi, haway⟩
  exact hN i hi u haway

end SpectralGapsPrelim.HigherDim
