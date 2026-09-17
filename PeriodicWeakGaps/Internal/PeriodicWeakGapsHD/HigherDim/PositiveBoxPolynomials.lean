import PeriodicWeakGapsHD.HigherDim.Setup

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Topology ENNReal FourierTransform

namespace SpectralGapsPrelim.HigherDim

/-!
Finite positive-box combinatorics and elementary coefficient polynomials.
-/

private lemma norm_exp2piI (u : ℝ) :
    ‖exp2piI u‖ = 1 := by
  simp [exp2piI, Complex.norm_exp]

theorem indexBox_nonempty {d N : ℕ} (hN : 1 ≤ N) :
    (indexBox d N).Nonempty := by
  classical
  exact Fintype.piFinset_nonempty.2 fun _ => ⟨1, by simp [hN]⟩

theorem indexBox_mem_iff {d N : ℕ} (k : Fin d → ℕ) :
    k ∈ indexBox d N ↔ ∀ i : Fin d, 1 ≤ k i ∧ k i ≤ N := by
  classical
  simp [indexBox, Fintype.mem_piFinset]

theorem card_indexBox (d N : ℕ) :
    (indexBox d N).card = N ^ d := by
  classical
  simp [indexBox]

theorem natVec_eq_intVec_natCast {d : ℕ} (k : Fin d → ℕ) :
    natVec k = intVec (fun i => (k i : ℤ)) := by
  simp [natVec, intVec, toE]

theorem norm_natVec_le_sqrt_d_mul_N {d N : ℕ} {k : Fin d → ℕ}
    (hk : k ∈ indexBox d N) :
    ‖natVec k‖ ≤ Real.sqrt (d : ℝ) * (N : ℝ) := by
  have hk_coord := (indexBox_mem_iff (d := d) (N := N) k).1 hk
  have hsum_le :
      (∑ i : Fin d, ‖(k i : ℝ)‖ ^ 2) ≤
        ∑ _i : Fin d, (N : ℝ) ^ 2 := by
    refine Finset.sum_le_sum ?_
    intro i hi
    have hki_le : ‖(k i : ℝ)‖ ≤ (N : ℝ) := by
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · exact_mod_cast (hk_coord i).2
      · exact_mod_cast Nat.zero_le (k i)
    exact pow_le_pow_left₀ (norm_nonneg _) hki_le 2
  calc
    ‖natVec k‖
        = Real.sqrt (∑ i : Fin d, ‖(k i : ℝ)‖ ^ 2) := by
          simp [natVec, toE, PiLp.norm_eq_of_L2]
    _ ≤ Real.sqrt (∑ _i : Fin d, (N : ℝ) ^ 2) :=
          Real.sqrt_le_sqrt hsum_le
    _ = Real.sqrt (d : ℝ) * (N : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          rw [Real.sqrt_mul (Nat.cast_nonneg d)]
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (Nat.cast_nonneg N)]

theorem coeffPolynomial_zero {d N : ℕ} {b : (Fin d → ℕ) → ℂ}
    (hsum : (indexBox d N).sum b = 1) :
    coeffPolynomial N b 0 = 1 := by
  simp [coeffPolynomial, exp2piI, hsum]

theorem coeffPolynomial_norm_le_sum_norm {d N : ℕ}
    (b : (Fin d → ℕ) → ℂ) (u : E d) :
    ‖coeffPolynomial N b u‖ ≤
      (indexBox d N).sum (fun k => ‖b k‖) := by
  calc
    ‖coeffPolynomial N b u‖
        ≤ (indexBox d N).sum
            (fun k => ‖b k * exp2piI (inner ℝ (natVec k) u)‖) := by
          simpa [coeffPolynomial] using
            norm_sum_le (indexBox d N)
              (fun k => b k * exp2piI (inner ℝ (natVec k) u))
    _ = (indexBox d N).sum (fun k => ‖b k‖) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          simp [norm_exp2piI]

theorem coeffPolynomial_coordinate_permutation {d N : ℕ}
    (σ : Equiv.Perm (Fin d))
    (b : (Fin d → ℕ) → ℂ) (u : E d) :
    coeffPolynomial N b u =
      coeffPolynomial N (fun k => b (k ∘ σ.symm))
        (toE fun i => coord u (σ i)) := by
  classical
  let e : (Fin d → ℕ) ≃ (Fin d → ℕ) := {
    toFun k := k ∘ σ
    invFun k := k ∘ σ.symm
    left_inv k := by
      funext i
      simp [Function.comp_def]
    right_inv k := by
      funext i
      simp [Function.comp_def] }
  refine Finset.sum_equiv e ?_ ?_
  · intro k
    simp only [indexBox, Fintype.mem_piFinset, Finset.mem_Icc, e]
    constructor
    · intro hk i
      exact hk (σ i)
    · intro hk i
      simpa using hk (σ.symm i)
  · intro k hk
    have hinner :
        inner ℝ (natVec k) u =
          inner ℝ (natVec (e k)) (toE fun i => coord u (σ i)) := by
      simp only [natVec, toE, coord, PiLp.inner_apply, e]
      exact (Equiv.sum_comp σ (fun i : Fin d => u.ofLp i * (k i : ℝ))).symm
    rw [hinner]
    simp [e, Function.comp_def]

end SpectralGapsPrelim.HigherDim
