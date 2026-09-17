import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Quantitative forward-recursion energy lemma

These quantitative energy statements use dimension-free inequalities
from the one-dimensional argument.
-/

noncomputable section

open scoped BigOperators

namespace AsymptoticallyIntegerHD
namespace Internal

/-- Absorb a half-square-root term. -/
theorem absorb_partial_energy {A D : Real} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (h : Real.sqrt A ≤ Real.sqrt D + (1 / 2 : Real) * Real.sqrt A) :
    A ≤ 4 * D := by
  have hsqrtA : 0 ≤ Real.sqrt A := Real.sqrt_nonneg A
  have hsqrtD : 0 ≤ Real.sqrt D := Real.sqrt_nonneg D
  have hsqA : (Real.sqrt A) ^ 2 = A := Real.sq_sqrt hA
  have hsqD : (Real.sqrt D) ^ 2 = D := Real.sq_sqrt hD
  nlinarith

/-- Bounded nonnegative partial sums are summable. -/
theorem summable_of_bounded_nonnegative_partialSums (a : Nat → Real) (C : Real)
    (ha : ∀ n, 0 ≤ a n)
    (hbound : ∀ N, (∑ n ∈ Finset.range N, a n) ≤ C) :
    Summable a ∧ ∑' n, a n ≤ C := by
  exact ⟨summable_of_sum_range_le ha hbound,
    Real.tsum_le_of_sum_range_le ha hbound⟩

end Internal

/-- Abstract triangular residual-energy estimate. -/
theorem triangular_residual_energy (a d k : Nat → Real) (Dsq : Real)
    (ha : ∀ n, 0 ≤ a n) (hd : ∀ n, 0 ≤ d n) (hk : ∀ n, 0 ≤ k n)
    (hdSummable : Summable d) (hdTsum : ∑' n, d n ≤ Dsq)
    (hDsq : 0 ≤ Dsq)
    (hkSummable : Summable (fun j => (k j) ^ 2))
    (hkTsum : ∑' j, (k j) ^ 2 ≤ 1 / 4)
    (htri : ∀ N,
      Real.sqrt (∑ j ∈ Finset.range N, a j) ≤
        Real.sqrt (∑ j ∈ Finset.range N, d j) +
          ∑ i ∈ Finset.range N, k i * Real.sqrt (a i)) :
    Summable a ∧ ∑' n, a n ≤ 4 * Dsq := by
  apply Internal.summable_of_bounded_nonnegative_partialSums a (4 * Dsq) ha
  intro N
  have haPartial : 0 ≤ ∑ i ∈ Finset.range N, a i :=
    Finset.sum_nonneg fun i _ => ha i
  have hkSq (i : Nat) : 0 ≤ (k i) ^ 2 := pow_nonneg (hk i) 2
  have hdPartial_le : (∑ i ∈ Finset.range N, d i) ≤ Dsq :=
    (hdSummable.sum_le_tsum (Finset.range N) (fun i _ => hd i)).trans hdTsum
  have hkPartial_le : (∑ i ∈ Finset.range N, (k i) ^ 2) ≤ 1 / 4 :=
    (hkSummable.sum_le_tsum (Finset.range N) (fun i _ => hkSq i)).trans hkTsum
  have hsqrtK : Real.sqrt (∑ i ∈ Finset.range N, (k i) ^ 2) ≤ (1 / 2 : Real) := by
    rw [Real.sqrt_le_iff]
    constructor
    · norm_num
    · norm_num at hkPartial_le ⊢
      exact hkPartial_le
  have hCS :
      (∑ i ∈ Finset.range N, k i * Real.sqrt (a i)) ≤
        Real.sqrt (∑ i ∈ Finset.range N, (k i) ^ 2) *
          Real.sqrt (∑ i ∈ Finset.range N, a i) := by
    simpa only [Real.sq_sqrt (ha _)] using
      (Real.sum_mul_le_sqrt_mul_sqrt (Finset.range N) k
        (fun i => Real.sqrt (a i)))
  have hweighted :
      (∑ i ∈ Finset.range N, k i * Real.sqrt (a i)) ≤
        (1 / 2 : Real) * Real.sqrt (∑ i ∈ Finset.range N, a i) :=
    hCS.trans (mul_le_mul_of_nonneg_right hsqrtK (Real.sqrt_nonneg _))
  have hrootD :
      Real.sqrt (∑ i ∈ Finset.range N, d i) ≤ Real.sqrt Dsq :=
    Real.sqrt_le_sqrt hdPartial_le
  apply Internal.absorb_partial_energy haPartial hDsq
  exact (htri N).trans (add_le_add hrootD hweighted)

end AsymptoticallyIntegerHD
