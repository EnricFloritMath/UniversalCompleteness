import Theorem14.Definitions
import Mathlib.Analysis.Fourier.AddCircle

/-! # Theorem 1.4: uniform continuous rotation averages -/

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace Theorem14.Internal

/- Proof idea: irrationality excludes a unit ratio. -/
private lemma fourier_rotation_ratio_ne_one
    (alpha : ℝ) (hAlpha : Irrational alpha) (m : ℤ) (hm : m ≠ 0) :
    (fourier m : C(AddCircle (1 : ℝ), ℂ)) (alpha : AddCircle (1 : ℝ)) ≠ 1 := by
  /- Proof idea: Rewrite the character as `exp(2π i m alpha)`. Equality to one would give `m * alpha ∈ ℤ`,
  hence rationality of `alpha`, contradicting `hAlpha` and `m ≠ 0`. -/
  rw [fourier_coe_apply]
  intro h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  norm_num at hn
  have hirr : Irrational ((m : ℝ) * alpha) := hAlpha.intCast_mul hm
  apply hirr.ne_int n
  have hnonzero : (2 * (Real.pi : ℂ) * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hc : (m : ℂ) * (alpha : ℂ) = (n : ℂ) := by
    apply mul_right_cancel₀ hnonzero
    calc
      (m : ℂ) * (alpha : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
          = 2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (alpha : ℂ) := by ring
      _ = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := hn
  exact_mod_cast hc

/- Proof idea: factor the character, use the exact finite sum, and bound its numerator by two. -/
private lemma norm_rotationAverage_fourier_le
    (alpha : ℝ) (hAlpha : Irrational alpha) (m : ℤ) (hm : m ≠ 0)
    (N : ℕ) (hN : 0 < N) :
    ∀ x : AddCircle (1 : ℝ),
      ‖rotationAverage alpha (fourier m) N x‖ ≤
        2 / ((N : ℝ) *
          ‖1 - fourier m (alpha : AddCircle (1 : ℝ))‖) := by
  /- Proof idea: Factor out `fourier m x`, rewrite the orbit terms as powers of the fixed ratio, apply the
  finite geometric-sum identity, bound `‖1-r^N‖ ≤ 2`, and divide by `N‖1-r‖`. -/
  intro x
  let r : ℂ := fourier m (alpha : AddCircle (1 : ℝ))
  have hr : (fourier m : C(AddCircle (1 : ℝ), ℂ))
      (alpha : AddCircle (1 : ℝ)) ≠ 1 :=
    fourier_rotation_ratio_ne_one alpha hAlpha m hm
  have hr' : 1 - r ≠ 0 := sub_ne_zero.mpr (Ne.symm hr)
  have hrnorm : ‖r‖ = 1 := Circle.norm_coe _
  have hterm (k : ℕ) :
      (fourier m : C(AddCircle (1 : ℝ), ℂ))
          (x + ((((k : ℕ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ))) =
        fourier m x * r ^ k := by
    change _ = fourier m x *
      (fourier m (alpha : AddCircle (1 : ℝ))) ^ k
    rw [fourier_apply, zsmul_add, AddCircle.toCircle_add, Circle.coe_mul]
    congr 1
    rw [← fourier_apply, fourier_coe_apply, fourier_coe_apply, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hsum : ∑ k ∈ Finset.range N, r ^ k = (1 - r ^ N) / (1 - r) := by
    apply (eq_div_iff hr').2
    exact geom_sum_mul_neg r N
  have hnum : ‖1 - r ^ N‖ ≤ 2 := by
    calc
      ‖1 - r ^ N‖ ≤ ‖(1 : ℂ)‖ + ‖r ^ N‖ := norm_sub_le _ _
      _ = 2 := by norm_num [norm_pow, hrnorm]
  rw [rotationAverage]
  simp_rw [hterm]
  rw [← Finset.mul_sum, hsum]
  have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hdenpos : 0 < ‖1 - r‖ := norm_pos_iff.mpr hr'
  have hNnorm : ‖(N : ℂ)‖ = (N : ℝ) := by
    rw [Complex.norm_natCast]
  calc
    ‖(N : ℂ)⁻¹ * ((fourier m) x * ((1 - r ^ N) / (1 - r)))‖ =
        (N : ℝ)⁻¹ * (‖1 - r ^ N‖ / ‖1 - r‖) := by
          rw [norm_mul, norm_inv, hNnorm, norm_mul,
            show ‖(fourier m) x‖ = 1 from Circle.norm_coe _, one_mul, norm_div]
    _ ≤ (N : ℝ)⁻¹ * (2 / ‖1 - r‖) := by gcongr
    _ = 2 / ((N : ℝ) *
        ‖1 - (fourier m) (alpha : AddCircle (1 : ℝ))‖) := by
      dsimp [r]
      field_simp

private lemma integral_fourier_eq_ite (m : ℤ) :
    (∫ y, (fourier m : C(AddCircle (1 : ℝ), ℂ)) y
      ∂AddCircle.haarAddCircle) = if m = 0 then 1 else 0 := by
  have hc := congr_fun (fourierCoeff_fourier (T := (1 : ℝ)) m) 0
  by_cases hm : m = 0
  · subst m
    simp [fourierCoeff] at hc ⊢
  · simpa [fourierCoeff, Pi.single_apply, hm] using hc

private lemma rotationAverage_fourier_zero
    (alpha : ℝ) (N : ℕ) (hN : 0 < N) (x : AddCircle (1 : ℝ)) :
    rotationAverage alpha (fourier 0) N x = 1 := by
  simp [rotationAverage, hN.ne']

private lemma rotationAverage_add
    (alpha : ℝ) (f g : C(AddCircle (1 : ℝ), ℂ))
    (N : ℕ) (x : AddCircle (1 : ℝ)) :
    rotationAverage alpha (⇑(f + g)) N x =
      rotationAverage alpha f N x + rotationAverage alpha g N x := by
  simp [rotationAverage]
  rw [Finset.sum_add_distrib]
  ring

private lemma rotationAverage_smul
    (alpha : ℝ) (a : ℂ) (f : C(AddCircle (1 : ℝ), ℂ))
    (N : ℕ) (x : AddCircle (1 : ℝ)) :
    rotationAverage alpha (⇑(a • f)) N x = a * rotationAverage alpha f N x := by
  simp [rotationAverage]
  rw [← Finset.mul_sum]
  ring

private lemma continuousMap_integrable
    (f : C(AddCircle (1 : ℝ), ℂ)) :
    Integrable f AddCircle.haarAddCircle := by
  simpa [IntegrableOn] using
    f.continuous.continuousOn.integrableOn_compact
      (μ := AddCircle.haarAddCircle) isCompact_univ

/- Proof idea: prove constants exactly, characters quantitatively, and close under finite span. -/
private lemma uniform_rotationAverage_on_fourierSpan
    (alpha : ℝ) (hAlpha : Irrational alpha)
    (phi : C(AddCircle (1 : ℝ), ℂ))
    (hphi : phi ∈ Submodule.span ℂ
      (Set.range (fun m : ℤ => (fourier m : C(AddCircle (1 : ℝ), ℂ))))) :
    ∀ epsilon > 0, ∃ N0 : ℕ, ∀ N ≥ N0, 0 < N →
      ∀ x : AddCircle (1 : ℝ),
        ‖rotationAverage alpha phi N x -
          ∫ y, phi y ∂AddCircle.haarAddCircle‖ < epsilon := by
  /- Proof idea: Use `Submodule.span_induction`; constants are exact, single nonzero characters use
  `norm_rotationAverage_fourier_le`, and addition/scalar multiplication combine finitely many `N0` bounds. -/
  induction hphi using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨m, rfl⟩ := hf
      intro epsilon hepsilon
      by_cases hm : m = 0
      · subst m
        refine ⟨1, ?_⟩
        intro N hN0 hN x
        rw [rotationAverage_fourier_zero alpha N hN x,
          integral_fourier_eq_ite, if_pos rfl]
        simpa using hepsilon
      · let d : ℝ := ‖1 - (fourier m : C(AddCircle (1 : ℝ), ℂ))
            (alpha : AddCircle (1 : ℝ))‖
        have hd : 0 < d := by
          apply norm_pos_iff.mpr
          exact sub_ne_zero.mpr
            (Ne.symm (fourier_rotation_ratio_ne_one alpha hAlpha m hm))
        obtain ⟨N0, hN0⟩ := exists_nat_gt (2 / (epsilon * d))
        refine ⟨N0, ?_⟩
        intro N hNN0 hN x
        rw [integral_fourier_eq_ite, if_neg hm, sub_zero]
        refine (norm_rotationAverage_fourier_le alpha hAlpha m hm N hN x).trans_lt ?_
        have hlarge : 2 / (epsilon * d) < (N : ℝ) :=
          hN0.trans_le (by exact_mod_cast hNN0)
        have hprod : 2 < (N : ℝ) * (epsilon * d) :=
          (div_lt_iff₀ (mul_pos hepsilon hd)).mp hlarge
        change 2 / ((N : ℝ) * d) < epsilon
        have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
        rw [div_lt_iff₀ (mul_pos hNr hd)]
        nlinarith
  | zero =>
      intro epsilon hepsilon
      refine ⟨1, ?_⟩
      intro N hN0 hN x
      simpa [rotationAverage] using hepsilon
  | add f g hf hg ihf ihg =>
      intro epsilon hepsilon
      obtain ⟨Nf, hNf⟩ := ihf (epsilon / 2) (by linarith)
      obtain ⟨Ng, hNg⟩ := ihg (epsilon / 2) (by linarith)
      refine ⟨max Nf Ng, ?_⟩
      intro N hNmax hN x
      have hNNf : Nf ≤ N := (le_max_left Nf Ng).trans hNmax
      have hNNg : Ng ≤ N := (le_max_right Nf Ng).trans hNmax
      have hfx := hNf N hNNf hN x
      have hgx := hNg N hNNg hN x
      rw [rotationAverage_add]
      have hiadd : (∫ y, (f + g) y ∂AddCircle.haarAddCircle) =
          (∫ y, f y ∂AddCircle.haarAddCircle) +
            ∫ y, g y ∂AddCircle.haarAddCircle := by
        change (∫ y, f y + g y ∂AddCircle.haarAddCircle) = _
        exact integral_add (continuousMap_integrable f) (continuousMap_integrable g)
      rw [hiadd]
      calc
        ‖(rotationAverage alpha f N x + rotationAverage alpha g N x) -
            ((∫ y, f y ∂AddCircle.haarAddCircle) +
              ∫ y, g y ∂AddCircle.haarAddCircle)‖ =
            ‖(rotationAverage alpha f N x -
                ∫ y, f y ∂AddCircle.haarAddCircle) +
              (rotationAverage alpha g N x -
                ∫ y, g y ∂AddCircle.haarAddCircle)‖ := by
                  abel_nf
        _ ≤ ‖rotationAverage alpha f N x -
                ∫ y, f y ∂AddCircle.haarAddCircle‖ +
              ‖rotationAverage alpha g N x -
                ∫ y, g y ∂AddCircle.haarAddCircle‖ := norm_add_le _ _
        _ < epsilon := by linarith
  | smul a f hf ih =>
      intro epsilon hepsilon
      by_cases ha : a = 0
      · subst a
        refine ⟨1, ?_⟩
        intro N hN0 hN x
        simpa [rotationAverage] using hepsilon
      · have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha
        obtain ⟨N0, hN0⟩ := ih (epsilon / ‖a‖) (div_pos hepsilon hna)
        refine ⟨N0, ?_⟩
        intro N hNN0 hN x
        have hx := hN0 N hNN0 hN x
        rw [rotationAverage_smul]
        have hismul : (∫ y, (a • f) y ∂AddCircle.haarAddCircle) =
            a * ∫ y, f y ∂AddCircle.haarAddCircle := by
          change (∫ y, a • f y ∂AddCircle.haarAddCircle) = _
          simpa [smul_eq_mul] using
            (integral_smul a (fun y => f y) :
              (∫ y, a • f y ∂AddCircle.haarAddCircle) = _)
        rw [hismul]
        rw [← mul_sub, norm_mul]
        calc
          ‖a‖ * ‖rotationAverage alpha f N x -
              ∫ y, f y ∂AddCircle.haarAddCircle‖ <
          ‖a‖ * (epsilon / ‖a‖) := mul_lt_mul_of_pos_left hx hna
          _ = epsilon := mul_div_cancel₀ epsilon (ne_of_gt hna)

private lemma norm_rotationAverage_sub_le_norm
    (alpha : ℝ) (f g : C(AddCircle (1 : ℝ), ℂ))
    (N : ℕ) (hN : 0 < N) (x : AddCircle (1 : ℝ)) :
    ‖rotationAverage alpha f N x - rotationAverage alpha g N x‖ ≤ ‖f - g‖ := by
  have hNnorm : ‖(N : ℂ)‖ = (N : ℝ) := by rw [Complex.norm_natCast]
  rw [rotationAverage, rotationAverage, ← mul_sub, ← Finset.sum_sub_distrib,
    norm_mul, norm_inv, hNnorm]
  calc
    (N : ℝ)⁻¹ * ‖∑ k ∈ Finset.range N,
        (f (x + ((((k : ℕ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ))) -
          g (x + ((((k : ℕ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ))))‖ ≤
        (N : ℝ)⁻¹ * ∑ k ∈ Finset.range N,
          ‖f (x + ((((k : ℕ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ))) -
            g (x + ((((k : ℕ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ)))‖ := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ (N : ℝ)⁻¹ * ∑ _k ∈ Finset.range N, ‖f - g‖ := by
      gcongr with k hk
      exact (f - g).norm_coe_le_norm _
    _ = ‖f - g‖ := by
      simp [hN.ne']

private lemma norm_integral_sub_le_norm
    (f g : C(AddCircle (1 : ℝ), ℂ)) :
    ‖(∫ y, f y ∂AddCircle.haarAddCircle) -
      ∫ y, g y ∂AddCircle.haarAddCircle‖ ≤ ‖f - g‖ := by
  rw [← integral_sub (continuousMap_integrable f) (continuousMap_integrable g)]
  calc
    ‖∫ y, f y - g y ∂AddCircle.haarAddCircle‖ ≤
        ‖f - g‖ * AddCircle.haarAddCircle.real Set.univ :=
      norm_integral_le_of_norm_le_const (C := ‖f - g‖) <| by
        filter_upwards with x
        exact (f - g).norm_coe_le_norm x
    _ = ‖f - g‖ := by simp [measureReal_def]

/- Proof idea: approximate in sup norm and retain one N0 for every starting point. -/
theorem uniform_rotationAverage_continuous
    (alpha : ℝ) (hAlpha : Irrational alpha)
    (phi : C(AddCircle (1 : ℝ), ℂ)) :
    ∀ epsilon > 0, ∃ N0 : ℕ, ∀ N ≥ N0, 0 < N →
      ∀ x : AddCircle (1 : ℝ),
        ‖rotationAverage alpha phi N x -
          ∫ y, phi y ∂AddCircle.haarAddCircle‖ < epsilon := by
  /- Proof idea: Approximate `phi` uniformly by `psi` in the Fourier span within `epsilon/3`, apply `uniform_rotationAverage_on_fourierSpan`
  to `psi`, and close the two uniform error terms by the probability-measure estimates. -/
  intro epsilon hepsilon
  let V : Submodule ℂ C(AddCircle (1 : ℝ), ℂ) :=
    Submodule.span ℂ
      (Set.range (fun m : ℤ => (fourier m : C(AddCircle (1 : ℝ), ℂ))))
  have hclosure : phi ∈ V.topologicalClosure := by
    dsimp [V]
    rw [span_fourier_closure_eq_top]
    exact Submodule.mem_top
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe,
    Metric.mem_closure_iff] at hclosure
  obtain ⟨psi, hpsiV, hclose⟩ := hclosure (epsilon / 3) (by linarith)
  have hpsi : psi ∈ Submodule.span ℂ
      (Set.range (fun m : ℤ => (fourier m : C(AddCircle (1 : ℝ), ℂ)))) := by
    exact hpsiV
  have hnorm : ‖phi - psi‖ < epsilon / 3 := by
    simpa [dist_eq_norm] using hclose
  obtain ⟨N0, hN0⟩ :=
    uniform_rotationAverage_on_fourierSpan alpha hAlpha psi hpsi
      (epsilon / 3) (by linarith)
  refine ⟨N0, ?_⟩
  intro N hNN0 hN x
  have hmiddle := hN0 N hNN0 hN x
  have havg : ‖rotationAverage alpha phi N x -
      rotationAverage alpha psi N x‖ ≤ ‖phi - psi‖ :=
    norm_rotationAverage_sub_le_norm alpha phi psi N hN x
  have hint : ‖(∫ y, psi y ∂AddCircle.haarAddCircle) -
      ∫ y, phi y ∂AddCircle.haarAddCircle‖ ≤ ‖phi - psi‖ := by
    have h := norm_integral_sub_le_norm psi phi
    simpa [norm_sub_rev] using h
  calc
    ‖rotationAverage alpha phi N x -
        ∫ y, phi y ∂AddCircle.haarAddCircle‖ =
      ‖(rotationAverage alpha phi N x - rotationAverage alpha psi N x) +
        (rotationAverage alpha psi N x -
          ∫ y, psi y ∂AddCircle.haarAddCircle) +
        ((∫ y, psi y ∂AddCircle.haarAddCircle) -
          ∫ y, phi y ∂AddCircle.haarAddCircle)‖ := by
            abel_nf
    _ ≤ ‖rotationAverage alpha phi N x - rotationAverage alpha psi N x‖ +
        ‖rotationAverage alpha psi N x -
          ∫ y, psi y ∂AddCircle.haarAddCircle‖ +
        ‖(∫ y, psi y ∂AddCircle.haarAddCircle) -
          ∫ y, phi y ∂AddCircle.haarAddCircle‖ := by
      exact (norm_add_le _ _).trans <|
        add_le_add (norm_add_le _ _) le_rfl
    _ < epsilon := by linarith

end Theorem14.Internal
