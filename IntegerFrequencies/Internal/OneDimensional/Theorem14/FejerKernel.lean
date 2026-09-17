import Theorem14.Definitions

/-! # Theorem 1.4: quantitative Fejer kernel -/

noncomputable section

open Filter MeasureTheory Metric Set
open scoped BigOperators ENNReal Topology

namespace Theorem14.Internal

/- Proof idea: move the coefficient through the finite sum and collapse the delta sum. -/
theorem fourierCoeff_fejerMean
    (f : AddCircle (1 : ℝ) → ℂ) (N : ℕ) (n : ℤ) :
    fourierCoeff (fejerMean N f) n =
      (fejerMultiplier N n : ℂ) * fourierCoeff f n := by
  /- Proof idea: Move coefficient through the finite sum and use orthogonality of characters. -/
  classical
  rw [fejerMean]
  rw [show
    (⇑(∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      ((fejerMultiplier N m : ℂ) * fourierCoeff f m) •
        (fourier m : C(AddCircle (1 : ℝ), ℂ))) : AddCircle (1 : ℝ) → ℂ) =
      (fun x : AddCircle (1 : ℝ) =>
        ∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          ((fejerMultiplier N m : ℂ) * fourierCoeff f m) • fourier m x) by
    funext x
    simp]
  rw [show
    (fun x : AddCircle (1 : ℝ) =>
      ∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        ((fejerMultiplier N m : ℂ) * fourierCoeff f m) • fourier m x) =
      ∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        (fun x : AddCircle (1 : ℝ) =>
          ((fejerMultiplier N m : ℂ) * fourierCoeff f m) • fourier m x) by
    funext x
    simp]
  have hint : ∀ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      Integrable (fun x : AddCircle (1 : ℝ) =>
        ((fejerMultiplier N m : ℂ) * fourierCoeff f m) • fourier m x)
        AddCircle.haarAddCircle := by
    intro m hm
    have hfour : Integrable (fun x : AddCircle (1 : ℝ) => fourier m x)
        AddCircle.haarAddCircle := by
      simpa using (integrable_const (1 : ℂ)).fourier_smul m
    simpa only [smul_eq_mul] using
      hfour.const_mul ((fejerMultiplier N m : ℂ) * fourierCoeff f m)
  rw [fourierCoeff.sum (T := (1 : ℝ))
    (Finset.Icc (-(N : ℤ)) (N : ℤ))
    (fun m (x : AddCircle (1 : ℝ)) =>
      ((fejerMultiplier N m : ℂ) * fourierCoeff f m) • fourier m x) hint]
  have hterm (m : ℤ) :
      fourierCoeff (fun x : AddCircle (1 : ℝ) =>
        ((fejerMultiplier N m : ℂ) * fourierCoeff f m) • fourier m x) n =
        ((fejerMultiplier N m : ℂ) * fourierCoeff f m) •
          (Pi.single m 1 : ℤ → ℂ) n := by
    calc
      fourierCoeff (fun x : AddCircle (1 : ℝ) =>
          ((fejerMultiplier N m : ℂ) * fourierCoeff f m) • fourier m x) n =
          ((fejerMultiplier N m : ℂ) * fourierCoeff f m) •
            fourierCoeff (fourier m) n :=
        fourierCoeff.const_smul (fourier m)
          ((fejerMultiplier N m : ℂ) * fourierCoeff f m) n
      _ = ((fejerMultiplier N m : ℂ) * fourierCoeff f m) •
          (Pi.single m 1 : ℤ → ℂ) n := by
        exact congrArg
          (fun z : ℂ => ((fejerMultiplier N m : ℂ) * fourierCoeff f m) • z)
          (congrFun (fourierCoeff_fourier m) n)
  rw [Finset.sum_apply]
  change (∑ c ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      fourierCoeff (fun x : AddCircle (1 : ℝ) =>
        ((fejerMultiplier N c : ℂ) * fourierCoeff f c) * fourier c x) n) = _
  calc
    (∑ c ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        fourierCoeff (fun x : AddCircle (1 : ℝ) =>
          ((fejerMultiplier N c : ℂ) * fourierCoeff f c) * fourier c x) n) =
        ∑ c ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          ((fejerMultiplier N c : ℂ) * fourierCoeff f c) *
            (Pi.single c 1 : ℤ → ℂ) n := by
      apply Finset.sum_congr rfl
      intro c hc
      simpa only [smul_eq_mul] using hterm c
    _ = (fejerMultiplier N n : ℂ) * fourierCoeff f n := by
      by_cases hn : n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ)
      · rw [Finset.sum_eq_single n]
        · simp
        · intro b hb hbn
          simp [hbn]
        · exact fun h => (h hn).elim
      · have hmult : fejerMultiplier N n = 0 := by
          have hnot : ¬ |n| ≤ (N : ℤ) := by
            intro h
            apply hn
            simpa [Finset.mem_Icc, abs_le] using h
          rw [fejerMultiplier, if_neg hnot]
        rw [show (fejerMultiplier N n : ℂ) * fourierCoeff f n = 0 by
          simp [hmult]]
        apply Finset.sum_eq_zero
        intro c hc
        have hcn : c ≠ n := by
          intro h
          subst c
          exact hn hc
        simp [hcn]

private lemma sum_Icc_neg_natCast_eq_zero_add_pairs
    (F : ℤ → ℂ) (N : ℕ) :
    (∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), F n) =
      F 0 + ∑ d ∈ Finset.range N,
        (F ((d + 1 : ℕ) : ℤ) + F (-((d + 1 : ℕ) : ℤ))) := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hset :
          Finset.Icc (-((N + 1 : ℕ) : ℤ)) ((N + 1 : ℕ) : ℤ) =
            insert (-((N + 1 : ℕ) : ℤ))
              (insert ((N + 1 : ℕ) : ℤ)
                (Finset.Icc (-(N : ℤ)) (N : ℤ))) := by
        ext n
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [hset]
      have hneg : -((N + 1 : ℕ) : ℤ) ∉
          insert ((N + 1 : ℕ) : ℤ) (Finset.Icc (-(N : ℤ)) (N : ℤ)) := by
        simp only [Finset.mem_insert, Finset.mem_Icc, not_or]
        constructor
        · omega
        · omega
      have hpos : ((N + 1 : ℕ) : ℤ) ∉
          Finset.Icc (-(N : ℤ)) (N : ℤ) := by
        simp [Finset.mem_Icc]
      rw [Finset.sum_insert hneg, Finset.sum_insert hpos, ih,
        Finset.sum_range_succ]
      ring

private lemma sq_norm_characterPartialSum_eq_positive_pairs
    (N : ℕ) (x : AddCircle (1 : ℝ)) :
    ((‖∑ k ∈ Finset.range (N + 1), fourier (k : ℤ) x‖ ^ 2 : ℝ) : ℂ) =
      ((N : ℝ) + 1 : ℂ) +
        ∑ d ∈ Finset.range N,
          (((N : ℝ) - (d : ℝ) : ℝ) : ℂ) *
            (fourier ((d + 1 : ℕ) : ℤ) x +
              fourier (-((d + 1 : ℕ) : ℤ)) x) := by
  induction N with
  | zero => simp
  | succ N ih =>
      let S : ℂ := ∑ k ∈ Finset.range (N + 1), fourier (k : ℤ) x
      let a : ℂ := fourier ((N + 1 : ℕ) : ℤ) x
      let P : ℕ → ℂ := fun d =>
        fourier ((d + 1 : ℕ) : ℤ) x + fourier (-((d + 1 : ℕ) : ℤ)) x
      have hsum :
          (∑ k ∈ Finset.range (N + 1 + 1), fourier (k : ℤ) x) = S + a := by
        rw [Finset.sum_range_succ]
      have hsq (z : ℂ) :
          ((‖z‖ ^ 2 : ℝ) : ℂ) = starRingEnd ℂ z * z := by
        rw [Complex.sq_norm]
        exact Complex.normSq_eq_conj_mul_self
      have hconjS : starRingEnd ℂ S =
          ∑ k ∈ Finset.range (N + 1), fourier (-(k : ℤ)) x := by
        dsimp [S]
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro k hk
        exact (fourier_neg (n := (k : ℤ)) (x := x)).symm
      have hcrossPos : starRingEnd ℂ S * a = ∑ d ∈ Finset.range (N + 1),
          fourier ((d + 1 : ℕ) : ℤ) x := by
        rw [hconjS, Finset.sum_mul]
        have hraw :
            (∑ k ∈ Finset.range (N + 1),
              fourier (-(k : ℤ)) x * a) =
            ∑ k ∈ Finset.range (N + 1),
              fourier (((N + 1 : ℕ) : ℤ) - (k : ℤ)) x := by
          apply Finset.sum_congr rfl
          intro k hk
          dsimp [a]
          change fourier (-(k : ℤ)) x *
              fourier (((N + 1 : ℕ) : ℤ)) x =
            fourier (((N + 1 : ℕ) : ℤ) - (k : ℤ)) x
          rw [← fourier_add]
          congr 1
          ring
        rw [hraw, ← Finset.sum_range_reflect
          (fun d => fourier ((d + 1 : ℕ) : ℤ) x) (N + 1)]
        apply Finset.sum_congr rfl
        intro k hk
        congr 2
        have hk' := Finset.mem_range.mp hk
        push_cast
        omega
      have hcrossNeg : starRingEnd ℂ a * S = ∑ d ∈ Finset.range (N + 1),
          fourier (-((d + 1 : ℕ) : ℤ)) x := by
        rw [hconjS] at hcrossPos
        dsimp [a, S]
        rw [Finset.mul_sum]
        calc
          (∑ k ∈ Finset.range (N + 1),
              starRingEnd ℂ (fourier ((N + 1 : ℕ) : ℤ) x) * fourier (k : ℤ) x) =
              ∑ k ∈ Finset.range (N + 1),
                fourier ((k : ℤ) - ((N + 1 : ℕ) : ℤ)) x := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [← fourier_neg]
            rw [← fourier_add]
            congr 2
          _ = ∑ d ∈ Finset.range (N + 1),
                fourier (-((d + 1 : ℕ) : ℤ)) x := by
            rw [← Finset.sum_range_reflect
              (fun d => fourier (-((d + 1 : ℕ) : ℤ)) x) (N + 1)]
            apply Finset.sum_congr rfl
            intro k hk
            congr 2
            have hk' := Finset.mem_range.mp hk
            push_cast
            omega
      have haa : starRingEnd ℂ a * a = 1 := by
        rw [← Complex.normSq_eq_conj_mul_self]
        simp [a, fourier_apply]
      have hpairSum :
          (∑ d ∈ Finset.range (N + 1), fourier ((d + 1 : ℕ) : ℤ) x) +
            (∑ d ∈ Finset.range (N + 1), fourier (-((d + 1 : ℕ) : ℤ)) x) =
          ∑ d ∈ Finset.range (N + 1), P d := by
        simp [P, Finset.sum_add_distrib]
      have hcoeff :
          (∑ d ∈ Finset.range (N + 1),
              ((((N + 1 : ℕ) : ℝ) - (d : ℝ) : ℝ) : ℂ) * P d) =
            (∑ d ∈ Finset.range N,
              (((N : ℝ) - (d : ℝ) : ℝ) : ℂ) * P d) +
              ∑ d ∈ Finset.range (N + 1), P d := by
        calc
          (∑ d ∈ Finset.range (N + 1),
              ((((N + 1 : ℕ) : ℝ) - (d : ℝ) : ℝ) : ℂ) * P d) =
              ∑ d ∈ Finset.range (N + 1),
                ((((N : ℝ) - (d : ℝ) : ℝ) : ℂ) * P d + P d) := by
            apply Finset.sum_congr rfl
            intro d hd
            simp only [Nat.cast_add, Nat.cast_one]
            push_cast
            ring
          _ = (∑ d ∈ Finset.range (N + 1),
                (((N : ℝ) - (d : ℝ) : ℝ) : ℂ) * P d) +
              ∑ d ∈ Finset.range (N + 1), P d := Finset.sum_add_distrib
          _ = (∑ d ∈ Finset.range N,
                (((N : ℝ) - (d : ℝ) : ℝ) : ℂ) * P d) +
              ∑ d ∈ Finset.range (N + 1), P d := by
            rw [Finset.sum_range_succ]
            norm_num
      rw [hsum, hsq]
      simp only [map_add]
      calc
        (starRingEnd ℂ S + starRingEnd ℂ a) * (S + a) =
            starRingEnd ℂ S * S + starRingEnd ℂ S * a +
              starRingEnd ℂ a * S + starRingEnd ℂ a * a := by ring
        _ = starRingEnd ℂ S * S + 1 +
              ∑ d ∈ Finset.range (N + 1), P d := by
          rw [hcrossPos, hcrossNeg, haa, ← hpairSum]
          ring
        _ = ((N : ℝ) + 1 : ℂ) +
              (∑ d ∈ Finset.range N,
                (((N : ℝ) - (d : ℝ) : ℝ) : ℂ) * P d) +
              1 + ∑ d ∈ Finset.range (N + 1), P d := by
          rw [← ih, hsq S]
        _ = (((N + 1 : ℕ) : ℝ) + 1 : ℂ) +
              ∑ d ∈ Finset.range (N + 1),
                ((((N + 1 : ℕ) : ℝ) - (d : ℝ) : ℝ) : ℂ) * P d := by
          rw [hcoeff]
          push_cast
          ring

/- Proof idea: expand the norm square, group by differences, and integrate characters. -/
lemma fejerKernel_expansion_nonneg_integral (N : ℕ) :
    (∀ x : AddCircle (1 : ℝ),
      ((fejerKernel N x : ℝ) : ℂ) =
        ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          (fejerMultiplier N n : ℂ) * fourier n x) ∧
    (∀ x : AddCircle (1 : ℝ), 0 ≤ fejerKernel N x) ∧
    (∫ x, fejerKernel N x ∂AddCircle.haarAddCircle) = 1 := by
  /- Proof idea: Expand the norm square, group pairs by their difference, count multiplicities, and integrate
  the finite character expansion. -/
  have hdenR : (N : ℝ) + 1 ≠ 0 := by positivity
  have hmult0 : fejerMultiplier N 0 = 1 := by
    simp [fejerMultiplier]
  have hmultPair (d : ℕ) (hd : d ∈ Finset.range N) :
      fejerMultiplier N ((d + 1 : ℕ) : ℤ) =
          ((N : ℝ) - (d : ℝ)) / ((N : ℝ) + 1) ∧
        fejerMultiplier N (-((d + 1 : ℕ) : ℤ)) =
          ((N : ℝ) - (d : ℝ)) / ((N : ℝ) + 1) := by
    have hdlt : d < N := Finset.mem_range.mp hd
    have hdle : ((d + 1 : ℕ) : ℤ) ≤ (N : ℤ) := by omega
    have habs : |((d + 1 : ℕ) : ℤ)| = ((d + 1 : ℕ) : ℤ) := abs_of_nonneg (by omega)
    have hcond : |((d + 1 : ℕ) : ℤ)| ≤ (N : ℤ) := habs.le.trans hdle
    have hcastNonneg : 0 ≤ ((((d + 1 : ℕ) : ℤ) : ℝ)) := by positivity
    have hcastNonneg' : 0 ≤ (d : ℝ) + 1 := by positivity
    constructor
    · rw [fejerMultiplier, if_pos hcond]
      push_cast
      rw [abs_of_nonneg hcastNonneg']
      field_simp [hdenR]
      ring
    · rw [fejerMultiplier, abs_neg, if_pos hcond]
      push_cast
      rw [abs_neg]
      rw [abs_of_nonneg hcastNonneg']
      field_simp [hdenR]
      ring
  have hexp : ∀ x : AddCircle (1 : ℝ),
      ((fejerKernel N x : ℝ) : ℂ) =
        ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          (fejerMultiplier N n : ℂ) * fourier n x := by
    intro x
    rw [sum_Icc_neg_natCast_eq_zero_add_pairs]
    simp only [hmult0, Complex.ofReal_one, one_mul]
    have hpairs :
        (∑ d ∈ Finset.range N,
          ((fejerMultiplier N ((d + 1 : ℕ) : ℤ) : ℂ) *
              fourier ((d + 1 : ℕ) : ℤ) x +
            (fejerMultiplier N (-((d + 1 : ℕ) : ℤ)) : ℂ) *
              fourier (-((d + 1 : ℕ) : ℤ)) x)) =
        ∑ d ∈ Finset.range N,
          (((((N : ℝ) - (d : ℝ)) / ((N : ℝ) + 1) : ℝ) : ℂ) *
            (fourier ((d + 1 : ℕ) : ℤ) x +
              fourier (-((d + 1 : ℕ) : ℤ)) x)) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [(hmultPair d hd).1, (hmultPair d hd).2]
      ring
    rw [hpairs]
    rw [fejerKernel]
    rw [Complex.ofReal_div]
    rw [sq_norm_characterPartialSum_eq_positive_pairs]
    push_cast
    rw [add_div, div_self (by exact_mod_cast hdenR)]
    simp only [fourier_zero]
    congr 1
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  have hnonneg : ∀ x : AddCircle (1 : ℝ), 0 ≤ fejerKernel N x := by
    intro x
    exact div_nonneg (sq_nonneg _) (by positivity)
  have hfourIntegrable (n : ℤ) :
      Integrable (fun x : AddCircle (1 : ℝ) => fourier n x)
        AddCircle.haarAddCircle := by
    simpa using (integrable_const (1 : ℂ)).fourier_smul n
  have hfourIntegral (n : ℤ) :
      (∫ x : AddCircle (1 : ℝ), fourier n x ∂AddCircle.haarAddCircle) =
        (Pi.single n 1 : ℤ → ℂ) 0 := by
    have h := congrFun (fourierCoeff_fourier (T := (1 : ℝ)) n) 0
    simpa [fourierCoeff, fourier_zero] using h
  have hintegral :
      (∫ x, fejerKernel N x ∂AddCircle.haarAddCircle) = 1 := by
    apply Complex.ofReal_injective
    rw [← integral_complex_ofReal]
    calc
      (∫ x, ((fejerKernel N x : ℝ) : ℂ) ∂AddCircle.haarAddCircle) =
          ∫ x, ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
            (fejerMultiplier N n : ℂ) * fourier n x
              ∂AddCircle.haarAddCircle := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hexp
      _ = ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          ∫ x, (fejerMultiplier N n : ℂ) * fourier n x
            ∂AddCircle.haarAddCircle := by
        rw [integral_finsetSum]
        intro n hn
        exact (hfourIntegrable n).const_mul _
      _ = 1 := by
        simp_rw [integral_const_mul, hfourIntegral]
        rw [Finset.sum_eq_single 0]
        · simp [hmult0]
        · intro b hb hb0
          simp [hb0]
        · simp
  exact ⟨hexp, hnonneg, hintegral⟩

/- Proof idea: substitute the finite kernel expansion and identify every coefficient. -/
lemma fejerMean_eq_fejerConvolution
    {f : AddCircle (1 : ℝ) → ℂ}
    (hf : Integrable f AddCircle.haarAddCircle) (N : ℕ)
    (x : AddCircle (1 : ℝ)) :
    fejerMean N f x = fejerConvolution N f x := by
  /- Proof idea: Substitute the finite kernel expansion, interchange the finite sum and integral, change
  variables, and identify each Fourier coefficient. -/
  classical
  have hexp := (fejerKernel_expansion_nonneg_integral N).1
  have hcharSub (n : ℤ) (z : AddCircle (1 : ℝ)) :
      fourier n (x - z) = fourier n x * fourier (-n) z := by
    simp only [sub_eq_add_neg, fourier_apply, zsmul_add, AddCircle.toCircle_add,
      Circle.coe_mul]
    rw [show n • (-z) = (-n) • z by simp]
  have hbase (n : ℤ) :
      (∫ y, fourier n y * f (x - y) ∂AddCircle.haarAddCircle) =
        fourier n x * fourierCoeff f n := by
    let g : AddCircle (1 : ℝ) → ℂ := fun z => fourier n (x - z) * f z
    calc
      (∫ y, fourier n y * f (x - y) ∂AddCircle.haarAddCircle) =
          ∫ y, g (x - y) ∂AddCircle.haarAddCircle := by
        apply integral_congr_ae
        filter_upwards [] with y
        simp [g]
      _ = ∫ z, g z ∂AddCircle.haarAddCircle := by
        exact integral_sub_left_eq_self g AddCircle.haarAddCircle x
      _ = ∫ z, fourier n x * (fourier (-n) z * f z)
            ∂AddCircle.haarAddCircle := by
        apply integral_congr_ae
        filter_upwards [] with z
        change fourier n (x - z) * f z = _
        rw [hcharSub]
        ring
      _ = fourier n x * fourierCoeff f n := by
        rw [integral_const_mul]
        rfl
  have hfx : Integrable (fun y : AddCircle (1 : ℝ) => f (x - y))
      AddCircle.haarAddCircle := by
    change Integrable (f ∘ fun y : AddCircle (1 : ℝ) => x - y)
      AddCircle.haarAddCircle
    exact (AddCircle.haarAddCircle.measurePreserving_sub_left x).integrable_comp_of_integrable hf
  rw [fejerMean, fejerConvolution]
  change (∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      ((fejerMultiplier N n : ℂ) * fourierCoeff f n) • fourier n) x = _
  simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
  calc
    (∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        (fejerMultiplier N n : ℂ) * fourierCoeff f n * fourier n x) =
      ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        (fejerMultiplier N n : ℂ) *
          (fourier n x * fourierCoeff f n) := by
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ = ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        ∫ y, ((fejerMultiplier N n : ℂ) * fourier n y) * f (x - y)
          ∂AddCircle.haarAddCircle := by
      apply Finset.sum_congr rfl
      intro n hn
      let c : ℂ := fejerMultiplier N n
      calc
        (fejerMultiplier N n : ℂ) * (fourier n x * fourierCoeff f n) =
            c * ∫ y, fourier n y * f (x - y) ∂AddCircle.haarAddCircle := by
          change c * (fourier n x * fourierCoeff f n) =
            c * ∫ y, fourier n y * f (x - y) ∂AddCircle.haarAddCircle
          exact congrArg (fun z : ℂ => c * z) (hbase n).symm
        _ = ∫ y, c * (fourier n y * f (x - y))
              ∂AddCircle.haarAddCircle :=
          (integral_const_mul c (fun y => fourier n y * f (x - y))).symm
        _ = ∫ y, ((fejerMultiplier N n : ℂ) * fourier n y) * f (x - y)
              ∂AddCircle.haarAddCircle := by
          apply integral_congr_ae
          filter_upwards [] with y
          dsimp [c]
          ring
    _ = ∫ y, ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        ((fejerMultiplier N n : ℂ) * fourier n y) * f (x - y)
          ∂AddCircle.haarAddCircle := by
      symm
      rw [integral_finsetSum]
      intro n hn
      have hi := (hfx.fourier_smul n).const_mul (fejerMultiplier N n : ℂ)
      simpa only [smul_eq_mul, mul_assoc] using hi
    _ = ∫ y, (fejerKernel N y : ℂ) * f (x - y)
          ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [hexp y]
      rw [Finset.sum_mul]

/- Proof idea: bound the convolution by K_N * norm f and use unit mass. -/
theorem integral_norm_fejerMean_le
    {f : AddCircle (1 : ℝ) → ℂ}
    (hf : Integrable f AddCircle.haarAddCircle) (N : ℕ) :
    (∫ x, ‖fejerMean N f x‖ ∂AddCircle.haarAddCircle) ≤
      ∫ x, ‖f x‖ ∂AddCircle.haarAddCircle := by
  /- Proof idea: Rewrite the finite Fejer mean by `fejerMean_eq_fejerConvolution`, bound its norm by the convolution of `K_N` with
  `norm f`, integrate, swap nonnegative integrals, and use kernel unit mass. -/
  classical
  let K : AddCircle (1 : ℝ) → ℂ := fun y => (fejerKernel N y : ℂ)
  have hkernel := fejerKernel_expansion_nonneg_integral N
  have hKnonneg : ∀ y : AddCircle (1 : ℝ), 0 ≤ fejerKernel N y := hkernel.2.1
  have hfourIntegrable (n : ℤ) :
      Integrable (fun x : AddCircle (1 : ℝ) => fourier n x)
        AddCircle.haarAddCircle := by
    simpa using (integrable_const (1 : ℂ)).fourier_smul n
  have hK : Integrable K AddCircle.haarAddCircle := by
    rw [show K = fun y : AddCircle (1 : ℝ) =>
        ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          (fejerMultiplier N n : ℂ) * fourier n y by
      funext y
      exact hkernel.1 y]
    apply integrable_finsetSum
    intro n hn
    exact (hfourIntegrable n).const_mul _
  have hprod : Integrable
      (fun p : AddCircle (1 : ℝ) × AddCircle (1 : ℝ) =>
        K p.2 * f (p.1 - p.2))
      (AddCircle.haarAddCircle.prod AddCircle.haarAddCircle) := by
    simpa only [ContinuousLinearMap.mul_apply'] using
      hK.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ) hf
  have hconv : Integrable
      (fun x : AddCircle (1 : ℝ) =>
        ∫ y, K y * f (x - y) ∂AddCircle.haarAddCircle)
      AddCircle.haarAddCircle := by
    exact hprod.integral_prod_left
  have hpoint (x : AddCircle (1 : ℝ)) :
      ‖∫ y, K y * f (x - y) ∂AddCircle.haarAddCircle‖ ≤
        ∫ y, fejerKernel N y * ‖f (x - y)‖
          ∂AddCircle.haarAddCircle := by
    calc
      ‖∫ y, K y * f (x - y) ∂AddCircle.haarAddCircle‖ ≤
          ∫ y, ‖K y * f (x - y)‖ ∂AddCircle.haarAddCircle :=
        norm_integral_le_integral_norm _
      _ = ∫ y, fejerKernel N y * ‖f (x - y)‖
            ∂AddCircle.haarAddCircle := by
        apply integral_congr_ae
        filter_upwards [] with y
        simp [K, Real.norm_eq_abs, abs_of_nonneg (hKnonneg y)]
  rw [show (fun x => ‖fejerMean N f x‖) =
      (fun x => ‖∫ y, K y * f (x - y) ∂AddCircle.haarAddCircle‖) by
    funext x
    rw [fejerMean_eq_fejerConvolution hf N x]
    rfl]
  calc
    (∫ x, ‖∫ y, K y * f (x - y) ∂AddCircle.haarAddCircle‖
        ∂AddCircle.haarAddCircle) ≤
        ∫ x, ∫ y, ‖K y * f (x - y)‖
          ∂AddCircle.haarAddCircle ∂AddCircle.haarAddCircle := by
      apply integral_mono hconv.norm hprod.norm.integral_prod_left
      intro x
      exact norm_integral_le_integral_norm _
    _ = ∫ y, ∫ x, ‖K y * f (x - y)‖
          ∂AddCircle.haarAddCircle ∂AddCircle.haarAddCircle := by
      exact integral_integral_swap hprod.norm
    _ = ∫ y, ∫ x, fejerKernel N y * ‖f (x - y)‖
          ∂AddCircle.haarAddCircle ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      filter_upwards [] with y
      apply integral_congr_ae
      filter_upwards [] with x
      simp [K, Real.norm_eq_abs, abs_of_nonneg (hKnonneg y)]
    _ = ∫ y, fejerKernel N y *
          (∫ x, ‖f x‖ ∂AddCircle.haarAddCircle)
          ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [integral_const_mul,
        integral_sub_right_eq_self (μ := AddCircle.haarAddCircle)
          (fun x : AddCircle (1 : ℝ) => ‖f x‖) y]
    _ = ∫ x, ‖f x‖ ∂AddCircle.haarAddCircle := by
      rw [integral_mul_const, hkernel.2.2, one_mul]

/- Proof idea: character one iff the circle point is the origin. -/
private lemma fourier_one_eq_one_iff (x : AddCircle (1 : ℝ)) :
    fourier (1 : ℤ) x = 1 ↔ x = 0 := by
  /- Proof idea: Rewrite the character through the period-one quotient formula. A value of one forces the
  representative to be an integer; `0<=unitRep<1` forces zero and hence the circle origin. The
  reverse direction is simplification. -/
  constructor
  · intro hx
    have hcircle : (AddCircle.toCircle x : ℂ) =
        (AddCircle.toCircle (0 : AddCircle (1 : ℝ)) : ℂ) := by
      simpa using hx
    exact AddCircle.injective_toCircle (by norm_num : (1 : ℝ) ≠ 0)
      (Circle.coe_injective hcircle)
  · rintro rfl
    simp

/- Proof idea: prove the exact quotient identity, then bound the numerator by two. -/
private lemma norm_character_partialSum_le
    (x : AddCircle (1 : ℝ)) (hx : x ≠ 0) (N : ℕ) :
    ‖∑ k ∈ Finset.range (N + 1), fourier (k : ℤ) x‖ ≤
      2 / ‖1 - fourier (1 : ℤ) x‖ := by
  /- Proof idea: First prove the literal identity `∑ k in range (N+1), fourier (k:Int) x = (1-(fourier 1
  x)^(N+1))/(1-fourier 1 x)`. Bound the numerator norm by two using character norm one and
  divide by the positive denominator norm. -/
  let z : ℂ := fourier (1 : ℤ) x
  have hz : z ≠ 1 := by
    intro h
    exact hx ((fourier_one_eq_one_iff x).mp h)
  have hpow : ∀ k : ℕ, fourier (k : ℤ) x = z ^ k := by
    intro k
    induction k with
    | zero => simp [z]
    | succ k ih =>
        rw [Nat.cast_succ, fourier_add, ih]
        simp [z, pow_succ]
  simp_rw [hpow]
  rw [geom_sum_eq hz, norm_div]
  have hzNorm : ‖z‖ = 1 := by
    simp [z, fourier_apply]
  have hnum : ‖z ^ (N + 1) - 1‖ ≤ 2 := by
    calc
      ‖z ^ (N + 1) - 1‖ ≤ ‖z ^ (N + 1)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hzNorm]; norm_num
  have hden : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  calc
    ‖z ^ (N + 1) - 1‖ / ‖z - 1‖ ≤ 2 / ‖z - 1‖ :=
      (div_le_div_iff_of_pos_right hden).2 hnum
    _ = 2 / ‖1 - fourier (1 : ℤ) x‖ := by
      rw [norm_sub_rev]

/- Proof idea: minimize the positive denominator on the closed ball complement. -/
private lemma exists_offZeroCharacterGap
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1 / 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : AddCircle (1 : ℝ),
      delta ≤ dist x 0 → c ≤ ‖1 - fourier (1 : ℤ) x‖ := by
  /- Proof idea: On the nonempty compact closed set `{x | delta <= dist x 0}`, `fourier_one_eq_one_iff` and `delta>0` exclude
  zeros. Take the attained positive minimum as `c`. -/
  have _hdelta1 : delta ≤ 1 / 2 := hdelta1
  let s : Set (AddCircle (1 : ℝ)) := (Metric.ball 0 delta)ᶜ
  have hs : IsCompact s := Metric.isOpen_ball.isClosed_compl.isCompact
  have hcont : Continuous (fun x : AddCircle (1 : ℝ) =>
      ‖1 - fourier (1 : ℤ) x‖) :=
    (continuous_const.sub (map_continuous (fourier (1 : ℤ)))).norm
  have hpos : ∀ x ∈ s, (0 : ℝ) < ‖1 - fourier (1 : ℤ) x‖ := by
    intro x hxs
    rw [norm_pos_iff]
    intro hzero
    have hchar : fourier (1 : ℤ) x = 1 := (sub_eq_zero.mp hzero).symm
    have hx0 : x = 0 := (fourier_one_eq_one_iff x).mp hchar
    subst x
    have : delta ≤ 0 := by
      simpa [s, Metric.mem_ball, not_lt] using hxs
    linarith
  obtain ⟨c, hc0, hc⟩ := hs.exists_forall_le' hcont.continuousOn hpos
  refine ⟨c, hc0, ?_⟩
  intro x hx
  apply hc x
  simpa [s, Metric.mem_ball, not_lt] using hx

/- Proof idea: square the 2/c bound and integrate over the literal ball complement. -/
private lemma integral_fejerKernel_compl_ball_le
    {delta c : ℝ} (hdelta : 0 < delta) (hc0 : 0 < c)
    (hc : ∀ x : AddCircle (1 : ℝ),
      delta ≤ dist x 0 → c ≤ ‖1 - fourier (1 : ℤ) x‖)
    (N : ℕ) :
    (∫ x in (Metric.ball (0 : AddCircle (1 : ℝ)) delta)ᶜ,
      fejerKernel N x ∂AddCircle.haarAddCircle) ≤
      4 / (((N : ℝ) + 1) * c ^ 2) := by
  /- Proof idea: For `x` in the complement, `delta>0` gives `x!=0`; `norm_character_partialSum_le` and `hc` bound the partial-sum
  norm by `2/c`. Square and divide by the literal `(N+1)` in `fejerKernel`, then integrate the
  pointwise `4/(((N:Real)+1)*c^2)` bound and use set mass at most one. -/
  classical
  let s : Set (AddCircle (1 : ℝ)) := (Metric.ball 0 delta)ᶜ
  let C : ℝ := 4 / (((N : ℝ) + 1) * c ^ 2)
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity
  have hpoint : ∀ x ∈ s, fejerKernel N x ≤ C := by
    intro x hxs
    have hdist : delta ≤ dist x 0 := by
      simpa [s, Metric.mem_ball, not_lt] using hxs
    have hx0 : x ≠ 0 := by
      intro hx
      subst x
      simp only [dist_self] at hdist
      linarith
    let A : ℝ := ‖∑ k ∈ Finset.range (N + 1), fourier (k : ℤ) x‖
    let D : ℝ := ‖1 - fourier (1 : ℤ) x‖
    have hDc : c ≤ D := hc x hdist
    have hD0 : 0 < D := lt_of_lt_of_le hc0 hDc
    have hA : A ≤ 2 / c := by
      calc
        A ≤ 2 / D := norm_character_partialSum_le x hx0 N
        _ ≤ 2 / c := by
          exact div_le_div_of_nonneg_left (by norm_num) hc0 hDc
    have hAc : A * c ≤ 2 := (le_div_iff₀ hc0).mp hA
    have hAsq : A ^ 2 * c ^ 2 ≤ 4 := by
      have hA0 : 0 ≤ A := norm_nonneg _
      calc
        A ^ 2 * c ^ 2 = (A * c) ^ 2 := by ring
        _ ≤ 2 ^ 2 := (sq_le_sq₀ (mul_nonneg hA0 hc0.le) (by norm_num)).2 hAc
        _ = 4 := by norm_num
    rw [fejerKernel]
    change A ^ 2 / ((N : ℝ) + 1) ≤ C
    dsimp [C]
    rw [div_le_div_iff₀ (by positivity : 0 < (N : ℝ) + 1)
      (mul_pos (by positivity : 0 < (N : ℝ) + 1) (sq_pos_of_pos hc0))]
    nlinarith
  have hkernel := fejerKernel_expansion_nonneg_integral N
  have hfourIntegrable (n : ℤ) :
      Integrable (fun x : AddCircle (1 : ℝ) => fourier n x)
        AddCircle.haarAddCircle := by
    simpa using (integrable_const (1 : ℂ)).fourier_smul n
  have hKc : Integrable (fun x : AddCircle (1 : ℝ) => (fejerKernel N x : ℂ))
      AddCircle.haarAddCircle := by
    rw [show (fun x : AddCircle (1 : ℝ) => (fejerKernel N x : ℂ)) =
        fun x => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          (fejerMultiplier N n : ℂ) * fourier n x by
      funext x
      exact hkernel.1 x]
    apply integrable_finsetSum
    intro n hn
    exact (hfourIntegrable n).const_mul _
  have hK : Integrable (fejerKernel N) AddCircle.haarAddCircle := by
    simpa using hKc.re
  change (∫ x in s, fejerKernel N x ∂AddCircle.haarAddCircle) ≤ C
  calc
    (∫ x in s, fejerKernel N x ∂AddCircle.haarAddCircle) ≤
        ∫ _x in s, C ∂AddCircle.haarAddCircle := by
      apply integral_mono_ae hK.integrableOn (integrable_const C)
      exact ae_restrict_of_forall_mem Metric.isOpen_ball.measurableSet.compl
        fun x hx => hpoint x hx
    _ = AddCircle.haarAddCircle.real s * C := by
      rw [setIntegral_const, smul_eq_mul]
    _ ≤ C := by
      exact mul_le_of_le_one_left hC0 measureReal_le_one

/- Proof idea: split the kernel integral over a small ball and its complement, using the explicit rate. -/
theorem fejerMean_tendsto_uniform_continuous
    (phi : C(AddCircle (1 : ℝ), ℂ)) :
    Tendsto (fun N : ℕ => ‖fejerMean N phi - phi‖) atTop (𝓝 0) := by
  /- Proof idea: Given a target error, use uniform continuity to choose `0<delta<=1/2` so `‖phi (x-y)-phi x‖`
  is small when `dist y 0<delta`. Choose `c` from `exists_offZeroCharacterGap`. Split the convolution integral
  over `Metric.ball 0 delta` and its literal complement. Kernel unit mass controls the inner
  part; on the complement use the global oscillation bound `2*‖phi‖` and `integral_fejerKernel_compl_ball_le`, choosing an
  explicit `N0` from the displayed `4/(((N:Real)+1)*c^2)` rate. Apply `fejerMean_eq_fejerConvolution` to return to
  `fejerMean`. -/
  classical
  have hphi : Integrable (phi : AddCircle (1 : ℝ) → ℂ)
      AddCircle.haarAddCircle := by
    exact phi.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  obtain ⟨delta0, hdelta0, hmod⟩ :=
    phi.uniform_continuity (epsilon / 2) (by positivity)
  let delta : ℝ := min delta0 (1 / 2)
  have hdelta : 0 < delta := by
    exact lt_min hdelta0 (by norm_num)
  have hdeltaHalf : delta ≤ 1 / 2 := min_le_right _ _
  have hmodDelta {u v : AddCircle (1 : ℝ)} (huv : dist u v < delta) :
      ‖phi u - phi v‖ < epsilon / 2 := by
    rw [← dist_eq_norm]
    exact hmod (huv.trans_le (min_le_left _ _))
  obtain ⟨c, hc0, hc⟩ := exists_offZeroCharacterGap hdelta hdeltaHalf
  let B : ℝ := 2 * ‖phi‖
  have hB0 : 0 ≤ B := by positivity
  obtain ⟨N0, hN0⟩ := exists_nat_gt (8 * B / (epsilon * c ^ 2))
  refine ⟨N0, ?_⟩
  intro N hN
  have hthreshold :
      8 * B / (epsilon * c ^ 2) < (N : ℝ) + 1 := by
    have hcast : (N0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    exact hN0.trans_le (hcast.trans (le_add_of_nonneg_right zero_le_one))
  have hrate :
      B * (4 / (((N : ℝ) + 1) * c ^ 2)) < epsilon / 2 := by
    have hec : 0 < epsilon * c ^ 2 := mul_pos hepsilon (sq_pos_of_pos hc0)
    have hbase : 8 * B < ((N : ℝ) + 1) * (epsilon * c ^ 2) :=
      (div_lt_iff₀ hec).mp hthreshold
    have hden : 0 < ((N : ℝ) + 1) * c ^ 2 :=
      mul_pos (by positivity) (sq_pos_of_pos hc0)
    rw [show B * (4 / (((N : ℝ) + 1) * c ^ 2)) =
      (4 * B) / (((N : ℝ) + 1) * c ^ 2) by ring]
    rw [div_lt_iff₀ hden]
    nlinarith [hbase]
  have hkernel := fejerKernel_expansion_nonneg_integral N
  have hKnonneg : ∀ y : AddCircle (1 : ℝ), 0 ≤ fejerKernel N y := hkernel.2.1
  have hKcCont : Continuous (fun y : AddCircle (1 : ℝ) =>
      (fejerKernel N y : ℂ)) := by
    rw [show (fun y : AddCircle (1 : ℝ) => (fejerKernel N y : ℂ)) =
        fun y => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          (fejerMultiplier N n : ℂ) * fourier n y by
      funext y
      exact hkernel.1 y]
    fun_prop
  have hKCont : Continuous (fejerKernel N) := by
    exact Complex.continuous_re.comp hKcCont
  have hK : Integrable (fejerKernel N) AddCircle.haarAddCircle := by
    exact hKCont.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hKc : Integrable (fun y : AddCircle (1 : ℝ) => (fejerKernel N y : ℂ))
      AddCircle.haarAddCircle := by
    exact hK.ofReal
  have herror (x : AddCircle (1 : ℝ)) :
      ‖fejerMean N phi x - phi x‖ ≤
        ∫ y, fejerKernel N y * ‖phi (x - y) - phi x‖
          ∂AddCircle.haarAddCircle := by
    have hleft : Integrable (fun y : AddCircle (1 : ℝ) =>
        (fejerKernel N y : ℂ) * phi (x - y)) AddCircle.haarAddCircle := by
      let F : C(AddCircle (1 : ℝ), ℂ) :=
        ⟨fun y => (fejerKernel N y : ℂ) * phi (x - y),
          hKcCont.mul (phi.continuous.comp (continuous_const.sub continuous_id))⟩
      exact F.continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hright : Integrable (fun y : AddCircle (1 : ℝ) =>
        (fejerKernel N y : ℂ) * phi x) AddCircle.haarAddCircle :=
      hKc.mul_const _
    have hmass :
        (∫ y, (fejerKernel N y : ℂ) * phi x ∂AddCircle.haarAddCircle) = phi x := by
      rw [integral_mul_const, integral_complex_ofReal, hkernel.2.2]
      norm_num
    rw [fejerMean_eq_fejerConvolution hphi N x]
    change ‖(∫ y, (fejerKernel N y : ℂ) * phi (x - y)
        ∂AddCircle.haarAddCircle) - phi x‖ ≤ _
    calc
      ‖(∫ y, (fejerKernel N y : ℂ) * phi (x - y)
          ∂AddCircle.haarAddCircle) - phi x‖ =
          ‖(∫ y, (fejerKernel N y : ℂ) * phi (x - y)
            ∂AddCircle.haarAddCircle) -
            ∫ y, (fejerKernel N y : ℂ) * phi x
              ∂AddCircle.haarAddCircle‖ := by rw [hmass]
      _ = ‖∫ y, (fejerKernel N y : ℂ) * phi (x - y) -
            (fejerKernel N y : ℂ) * phi x
          ∂AddCircle.haarAddCircle‖ := by rw [integral_sub hleft hright]
      _ ≤
          ∫ y, ‖(fejerKernel N y : ℂ) * phi (x - y) -
            (fejerKernel N y : ℂ) * phi x‖
              ∂AddCircle.haarAddCircle := norm_integral_le_integral_norm _
      _ = ∫ y, fejerKernel N y * ‖phi (x - y) - phi x‖
            ∂AddCircle.haarAddCircle := by
        apply integral_congr_ae
        filter_upwards [] with y
        rw [← mul_sub, norm_mul]
        simp [Real.norm_eq_abs, abs_of_nonneg (hKnonneg y)]
  have hpointwise (x : AddCircle (1 : ℝ)) :
      ‖fejerMean N phi x - phi x‖ < epsilon := by
    let e : AddCircle (1 : ℝ) → ℝ := fun y =>
      fejerKernel N y * ‖phi (x - y) - phi x‖
    have heCont : Continuous e := by
      dsimp [e]
      exact hKCont.mul
        ((phi.continuous.comp (continuous_const.sub continuous_id)).sub
          continuous_const).norm
    have heInt : Integrable e AddCircle.haarAddCircle := by
      let E : C(AddCircle (1 : ℝ), ℝ) := ⟨e, heCont⟩
      exact E.continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hnear :
        (∫ y in Metric.ball (0 : AddCircle (1 : ℝ)) delta, e y
            ∂AddCircle.haarAddCircle) ≤ epsilon / 2 := by
      calc
        (∫ y in Metric.ball (0 : AddCircle (1 : ℝ)) delta, e y
            ∂AddCircle.haarAddCircle) ≤
            ∫ y in Metric.ball (0 : AddCircle (1 : ℝ)) delta,
              fejerKernel N y * (epsilon / 2)
                ∂AddCircle.haarAddCircle := by
          apply integral_mono_ae heInt.integrableOn (hK.mul_const _).integrableOn
          exact ae_restrict_of_forall_mem Metric.isOpen_ball.measurableSet fun y hy => by
            change fejerKernel N y * ‖phi (x - y) - phi x‖ ≤
              fejerKernel N y * (epsilon / 2)
            apply mul_le_mul_of_nonneg_left _ (hKnonneg y)
            exact (hmodDelta (by
              have : dist (x - y) x = dist y 0 := by simp [dist_eq_norm]
              rw [this]
              exact hy)).le
        _ = (∫ y in Metric.ball (0 : AddCircle (1 : ℝ)) delta,
              fejerKernel N y ∂AddCircle.haarAddCircle) * (epsilon / 2) := by
          rw [integral_mul_const]
        _ ≤ 1 * (epsilon / 2) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          calc
            (∫ y in Metric.ball (0 : AddCircle (1 : ℝ)) delta,
                fejerKernel N y ∂AddCircle.haarAddCircle) ≤
                ∫ y, fejerKernel N y ∂AddCircle.haarAddCircle := by
              apply integral_mono_measure Measure.restrict_le_self
                (Filter.Eventually.of_forall hKnonneg) hK
            _ = 1 := hkernel.2.2
        _ = epsilon / 2 := one_mul _
    have hfar :
        (∫ y in (Metric.ball (0 : AddCircle (1 : ℝ)) delta)ᶜ, e y
            ∂AddCircle.haarAddCircle) < epsilon / 2 := by
      calc
        (∫ y in (Metric.ball (0 : AddCircle (1 : ℝ)) delta)ᶜ, e y
            ∂AddCircle.haarAddCircle) ≤
            ∫ y in (Metric.ball (0 : AddCircle (1 : ℝ)) delta)ᶜ,
              fejerKernel N y * B ∂AddCircle.haarAddCircle := by
          apply integral_mono_ae heInt.integrableOn (hK.mul_const _).integrableOn
          exact ae_restrict_of_forall_mem Metric.isOpen_ball.measurableSet.compl
            fun y hy => by
            change fejerKernel N y * ‖phi (x - y) - phi x‖ ≤
              fejerKernel N y * B
            apply mul_le_mul_of_nonneg_left _ (hKnonneg y)
            calc
              ‖phi (x - y) - phi x‖ ≤ ‖phi (x - y)‖ + ‖phi x‖ := norm_sub_le _ _
              _ ≤ ‖phi‖ + ‖phi‖ :=
                add_le_add (phi.norm_coe_le_norm _) (phi.norm_coe_le_norm _)
              _ = B := by dsimp [B]; ring
        _ = (∫ y in (Metric.ball (0 : AddCircle (1 : ℝ)) delta)ᶜ,
              fejerKernel N y ∂AddCircle.haarAddCircle) * B := by
          rw [integral_mul_const]
        _ ≤ (4 / (((N : ℝ) + 1) * c ^ 2)) * B := by
          apply mul_le_mul_of_nonneg_right
            (integral_fejerKernel_compl_ball_le hdelta hc0 hc N) hB0
        _ < epsilon / 2 := by
          simpa [mul_comm] using hrate
    calc
      ‖fejerMean N phi x - phi x‖ ≤ ∫ y, e y ∂AddCircle.haarAddCircle := herror x
      _ = (∫ y in Metric.ball (0 : AddCircle (1 : ℝ)) delta, e y
              ∂AddCircle.haarAddCircle) +
            ∫ y in (Metric.ball (0 : AddCircle (1 : ℝ)) delta)ᶜ, e y
              ∂AddCircle.haarAddCircle :=
        (integral_add_compl Metric.isOpen_ball.measurableSet heInt).symm
      _ < epsilon := by linarith
  have hsup : ‖fejerMean N phi - phi‖ < epsilon :=
    (ContinuousMap.norm_lt_iff _ hepsilon).2 fun x => by
      simpa only [ContinuousMap.sub_apply] using hpointwise x
  simpa only [dist_zero_right, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg (fejerMean N phi - phi))] using hsup

end Theorem14.Internal
