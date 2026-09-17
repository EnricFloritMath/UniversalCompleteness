import SpectralGapsPrelim.Theorem112.Setup

noncomputable section

open MeasureTheory Filter
open scoped BigOperators

namespace SpectralGapsPrelim.Theorem112

/-!
Exponential independence for the one-dimensional nonuniqueness proof.
-/

private lemma exists_accumulation_zero_of_ae_zero_on_pos_measure
    {g : ℝ → ℂ} (_hg_cont : Continuous g)
    {B : Set ℝ} (_hB_meas : MeasurableSet B)
    (hB_pos : 0 < volume B)
    (hg_zero : ∀ᵐ t ∂volume.restrict B, g t = 0) :
    ∃ x : ℝ, ∃ᶠ y in nhds x, y ≠ x ∧ g y = 0 := by
  let bad : Set ℝ := {t | g t ≠ 0}
  have hbad_restrict : volume.restrict B bad = 0 := by
    simpa [bad] using (ae_iff.mp hg_zero)
  have hbad_inter : volume (B ∩ bad) = 0 := by
    simpa [Set.inter_comm] using
      (Measure.measure_inter_eq_zero_of_restrict (μ := volume) (s := B) (t := bad)
        hbad_restrict)
  let E : Set ℝ := B \ (B ∩ bad)
  have hE_pos : 0 < volume E := by
    change 0 < volume (B \ (B ∩ bad))
    rw [measure_sdiff_null hbad_inter]
    exact hB_pos
  rcases exists_accPt_of_noAtoms (μ := volume) (E := E) hE_pos with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  rw [accPt_iff_frequently] at hx
  exact hx.mono fun y hy =>
    ⟨hy.1, by
      have hy_not_bad : y ∉ bad := fun hybad => hy.2.2 ⟨hy.2.1, hybad⟩
      simpa [bad] using hy_not_bad⟩

private lemma frequently_complex_ofReal_zero_of_real_accumulation
    {G : ℂ → ℂ} {x : ℝ}
    (hfreq :
      ∃ᶠ y in nhds x, y ≠ x ∧ G (Complex.ofReal y) = 0) :
    ∃ᶠ z in nhds (Complex.ofReal x),
      z ≠ Complex.ofReal x ∧ G z = 0 := by
  exact Tendsto.frequently_map (fun y : ℝ => Complex.ofReal y)
    (Complex.continuous_ofReal.tendsto x)
    (fun y hy => ⟨fun h => hy.1 (Complex.ofReal_injective h), hy.2⟩)
    hfreq

private lemma exponential_coefficients_zero_of_derivative_equations
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {d : ι → ℝ} (hd : Function.Injective d)
    {c : ι → ℂ}
    (hderiv :
      ∀ m : ℕ, m < Fintype.card ι →
        Finset.univ.sum
          (fun j =>
            c j *
              ((((2 * Real.pi * d j : ℝ) : ℂ) * Complex.I) ^ m)) = 0) :
    ∀ j, c j = 0 := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let a : Fin (Fintype.card ι) → ℂ :=
    fun i => (((2 * Real.pi * d (e.symm i) : ℝ) : ℂ) * Complex.I)
  let v : Fin (Fintype.card ι) → ℂ := fun i => c (e.symm i)
  have ha : Function.Injective a := by
    intro i k hik
    have him :
        2 * Real.pi * d (e.symm i) = 2 * Real.pi * d (e.symm k) := by
      have := congrArg Complex.im hik
      simpa [a] using this
    have hd_eq : d (e.symm i) = d (e.symm k) := by
      exact mul_left_cancel₀ (show 2 * Real.pi ≠ 0 by positivity) him
    exact e.symm.injective (hd hd_eq)
  have hv : v = 0 := by
    apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero
      (R := ℂ) (f := a) (v := v) ha
    intro m
    have hm := hderiv (m : ℕ) m.isLt
    have hsum :
        (∑ j : Fin (Fintype.card ι), v j * a j ^ (m : ℕ)) =
          ∑ j : ι,
            c j * ((((2 * Real.pi * d j : ℝ) : ℂ) * Complex.I) ^ (m : ℕ)) := by
      rw [← Equiv.sum_comp e.symm]
    simpa [hsum] using hm
  intro j
  have hvj : v (e j) = 0 := by
    simp [hv]
  simpa [v] using hvj

private lemma real_complex_exponential_sum_eq {ι : Type*} [Fintype ι]
    (d : ι → ℝ) (c : ι → ℂ) (t : ℝ) :
    (∑ j : ι,
        c j *
          Complex.exp (((((2 * Real.pi * d j : ℝ) : ℂ) * Complex.I) *
            (t : ℂ)))) =
      ∑ j : ι, c j * exp2piI (d j * t) := by
  classical
  apply Finset.sum_congr rfl
  intro j _hj
  congr 1
  simp [exp2piI]
  ring_nf

private lemma exp_sum_continuous {ι : Type*} [Fintype ι]
    (d : ι → ℝ) (c : ι → ℂ) :
    Continuous (fun t : ℝ => ∑ j : ι, c j * exp2piI (d j * t)) := by
  unfold exp2piI
  fun_prop

private lemma exp_sum_analytic {ι : Type*} [Fintype ι]
    (d : ι → ℝ) (c : ι → ℂ) :
    AnalyticOnNhd ℂ
      (fun z : ℂ =>
        ∑ j : ι,
          c j *
            Complex.exp (((((2 * Real.pi * d j : ℝ) : ℂ) * Complex.I) * z)))
      Set.univ := by
  classical
  apply Finset.analyticOnNhd_fun_sum
  intro j _hj
  have hlin : AnalyticOnNhd ℂ
      (fun z : ℂ => ((((2 * Real.pi * d j : ℝ) : ℂ) * Complex.I) * z))
      Set.univ := by
    change AnalyticOnNhd ℂ
      (fun z : ℂ =>
        ((ContinuousLinearMap.mul ℂ ℂ)
          (((2 * Real.pi * d j : ℝ) : ℂ) * Complex.I)) z)
      Set.univ
    exact ((((ContinuousLinearMap.mul ℂ ℂ)
      (((2 * Real.pi * d j : ℝ) : ℂ) * Complex.I))).analyticOnNhd Set.univ)
  exact (analyticOnNhd_const (v := c j)).mul hlin.cexp

private lemma exp_sum_iteratedDeriv {ι : Type*} [Fintype ι]
    (d : ι → ℝ) (c : ι → ℂ) (m : ℕ) :
    iteratedDeriv m
      (fun z : ℂ =>
        ∑ j : ι,
          c j *
            Complex.exp (((((2 * Real.pi * d j : ℝ) : ℂ) * Complex.I) * z)))
      0 =
      ∑ j : ι, c j * ((((2 * Real.pi * d j : ℝ) : ℂ) * Complex.I) ^ m) := by
  classical
  rw [iteratedDeriv_fun_sum]
  · apply Finset.sum_congr rfl
    intro j _hj
    let a : ℂ := (((2 * Real.pi * d j : ℝ) : ℂ) * Complex.I)
    have hcont : ContDiffAt ℂ (m : ℕ)
        (fun z : ℂ => Complex.exp (a * z)) 0 := by
      fun_prop
    rw [iteratedDeriv_const_mul (c j) hcont]
    have hcexp := congrFun (iteratedDeriv_cexp_const_mul m a) 0
    simpa [a, mul_assoc] using congrArg (fun x => c j * x) hcexp
  · intro j _hj
    fun_prop

theorem expFamily_linearIndependent_ae
    {ι : Type*} [Fintype ι]
    {d : ι → ℝ} (hd : Function.Injective d)
    {B : Set ℝ} (hB_meas : MeasurableSet B)
    (hB_pos : 0 < volume B)
    {c : ι → ℂ}
    (hzero :
      ∀ᵐ t ∂volume.restrict B,
        (Finset.univ.sum
          (fun j => c j * exp2piI ((d j) * t))) = 0) :
    ∀ j, c j = 0 := by
  classical
  let G : ℂ → ℂ := fun z =>
    ∑ j : ι,
      c j * Complex.exp (((((2 * Real.pi * d j : ℝ) : ℂ) * Complex.I) * z))
  let g : ℝ → ℂ := fun t => ∑ j : ι, c j * exp2piI (d j * t)
  have hg_cont : Continuous g := by
    simpa [g] using exp_sum_continuous d c
  obtain ⟨x, hx⟩ := exists_accumulation_zero_of_ae_zero_on_pos_measure
    hg_cont hB_meas hB_pos hzero
  have hxG : ∃ᶠ y in nhds x, y ≠ x ∧ G (Complex.ofReal y) = 0 := by
    refine hx.mono ?_
    intro y hy
    refine ⟨hy.1, ?_⟩
    have hGy : G (Complex.ofReal y) = g y := by
      simpa [G, g] using (real_complex_exponential_sum_eq d c y)
    simpa [hGy] using hy.2
  have hfreq_complex :=
    frequently_complex_ofReal_zero_of_real_accumulation (G := G) hxG
  have hfreq_punct :
      ∃ᶠ z in nhdsWithin (Complex.ofReal x) {z | z ≠ Complex.ofReal x},
        G z = 0 := by
    rw [nhdsWithin, Filter.frequently_inf_principal]
    exact hfreq_complex
  have hG_an : AnalyticOnNhd ℂ G Set.univ := by
    simpa [G] using exp_sum_analytic d c
  have hG_zero_on : Set.EqOn G 0 Set.univ :=
    hG_an.eqOn_zero_of_preconnected_of_frequently_eq_zero
      isPreconnected_univ (by simp) hfreq_punct
  have hG_zero : G = fun _ => 0 := by
    funext z
    exact hG_zero_on (by simp)
  apply exponential_coefficients_zero_of_derivative_equations hd
  intro m _hm
  have hderiv_zero : iteratedDeriv m G 0 = 0 := by
    rw [hG_zero]
    simp
  have hderiv_calc :
      iteratedDeriv m G 0 =
        ∑ j : ι, c j * ((((2 * Real.pi * d j : ℝ) : ℂ) * Complex.I) ^ m) := by
    simpa [G] using exp_sum_iteratedDeriv d c m
  simpa [hderiv_calc] using hderiv_zero

end SpectralGapsPrelim.Theorem112
