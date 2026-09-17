import Theorem14.FejerKernel
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-! # Theorem 1.4: representative L1 Fejer approximation -/

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Topology

namespace Theorem14.Internal

/- Proof idea: approximate by a bounded continuous map and use direct contraction. -/
private theorem fejerMean_tendsto_L1
    {f : AddCircle (1 : ℝ) → ℂ}
    (hf : Integrable f AddCircle.haarAddCircle) :
    Tendsto (fun N : ℕ =>
      ∫ x, ‖fejerMean N f x - f x‖ ∂AddCircle.haarAddCircle)
      atTop (𝓝 0) := by
  /- Proof idea: Given a target error, apply the exact theorem with a smaller tolerance to obtain a
  `BoundedContinuousFunction` `phi`, its non-strict integral error bound, and integrability. Use
  `phi.toContinuousMap` for `fejerMean_tendsto_uniform_continuous`; control `fejerMean(f-phi)` by the direct contraction
  `integral_norm_fejerMean_le`, control `fejerMean phi-phi` by uniform convergence and probability mass, and close
  the three-term estimate. This is the sole route. -/
  classical
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  obtain ⟨phi, happrox, hphi⟩ :=
    hf.exists_boundedContinuous_integral_sub_le (by positivity : 0 < epsilon / 4)
  let phiC : C(AddCircle (1 : ℝ), ℂ) := phi.toContinuousMap
  have hdiff : Integrable (fun x : AddCircle (1 : ℝ) => f x - phi x)
      AddCircle.haarAddCircle := hf.sub hphi
  have hcoeffSub (n : ℤ) :
      fourierCoeff (fun x : AddCircle (1 : ℝ) => f x - phi x) n =
        fourierCoeff f n - fourierCoeff phi n := by
    unfold fourierCoeff
    rw [show (fun t : AddCircle (1 : ℝ) =>
        fourier (-n) t • (fun x => f x - phi x) t) =
        (fun t => fourier (-n) t • f t - fourier (-n) t • phi t) by
      funext t
      rw [smul_sub]]
    exact integral_sub (hf.fourier_smul _) (hphi.fourier_smul _)
  have hmeanSub (N : ℕ) :
      fejerMean N (fun x : AddCircle (1 : ℝ) => f x - phi x) =
        fejerMean N f - fejerMean N phi := by
    ext x
    simp only [fejerMean, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
      ContinuousMap.sub_apply, smul_eq_mul, hcoeffSub, mul_sub]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  have hcontinuousIntegrable (g : C(AddCircle (1 : ℝ), ℂ)) :
      Integrable g AddCircle.haarAddCircle := by
    simpa [IntegrableOn] using
      g.continuous.continuousOn.integrableOn_compact
        (μ := AddCircle.haarAddCircle) isCompact_univ
  have huniform := fejerMean_tendsto_uniform_continuous phiC
  rw [Metric.tendsto_atTop] at huniform
  obtain ⟨N0, hN0⟩ := huniform (epsilon / 2) (by positivity)
  refine ⟨N0, ?_⟩
  intro N hN
  have hcenterNorm : ‖fejerMean N phi - phiC‖ < epsilon / 2 := by
    have h := hN0 N hN
    change ‖fejerMean N phiC - phiC‖ < epsilon / 2
    simpa only [dist_zero_right, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg (fejerMean N phiC - phiC))] using h
  let A : C(AddCircle (1 : ℝ), ℂ) := fejerMean N f
  let P : C(AddCircle (1 : ℝ), ℂ) := fejerMean N phi
  have hA : Integrable A AddCircle.haarAddCircle := hcontinuousIntegrable A
  have hP : Integrable P AddCircle.haarAddCircle := hcontinuousIntegrable P
  have ht1 : Integrable (fun x : AddCircle (1 : ℝ) => ‖A x - P x‖)
      AddCircle.haarAddCircle := (hA.sub hP).norm
  have ht2 : Integrable (fun x : AddCircle (1 : ℝ) => ‖P x - phi x‖)
      AddCircle.haarAddCircle := (hP.sub hphi).norm
  have ht3 : Integrable (fun x : AddCircle (1 : ℝ) => ‖phi x - f x‖)
      AddCircle.haarAddCircle := (hphi.sub hf).norm
  have hlhs : Integrable (fun x : AddCircle (1 : ℝ) => ‖A x - f x‖)
      AddCircle.haarAddCircle := (hA.sub hf).norm
  have htriangle :
      (∫ x, ‖A x - f x‖ ∂AddCircle.haarAddCircle) ≤
        (∫ x, ‖A x - P x‖ ∂AddCircle.haarAddCircle) +
          (∫ x, ‖P x - phi x‖ ∂AddCircle.haarAddCircle) +
            ∫ x, ‖phi x - f x‖ ∂AddCircle.haarAddCircle := by
    calc
      (∫ x, ‖A x - f x‖ ∂AddCircle.haarAddCircle) ≤
          ∫ x, ‖A x - P x‖ +
            (‖P x - phi x‖ + ‖phi x - f x‖)
              ∂AddCircle.haarAddCircle := by
        apply integral_mono hlhs (ht1.add (ht2.add ht3))
        intro x
        calc
          ‖A x - f x‖ =
              ‖(A x - P x) + (P x - phi x) + (phi x - f x)‖ := by
            congr 1
            ring
          _ ≤ ‖A x - P x‖ + ‖P x - phi x‖ + ‖phi x - f x‖ :=
            norm_add₃_le
          _ = ‖A x - P x‖ + (‖P x - phi x‖ + ‖phi x - f x‖) := by
            ring
      _ = (∫ x, ‖A x - P x‖ ∂AddCircle.haarAddCircle) +
          (∫ x, ‖P x - phi x‖ ∂AddCircle.haarAddCircle) +
            ∫ x, ‖phi x - f x‖ ∂AddCircle.haarAddCircle := by
        calc
          (∫ x, ‖A x - P x‖ + (‖P x - phi x‖ + ‖phi x - f x‖)
              ∂AddCircle.haarAddCircle) =
              (∫ x, ‖A x - P x‖ ∂AddCircle.haarAddCircle) +
                ∫ x, ‖P x - phi x‖ + ‖phi x - f x‖
                  ∂AddCircle.haarAddCircle :=
            integral_add ht1 (ht2.add ht3)
          _ = _ := by
            rw [integral_add ht2 ht3]
            ring
  have hfirst :
      (∫ x, ‖A x - P x‖ ∂AddCircle.haarAddCircle) ≤ epsilon / 4 := by
    calc
      (∫ x, ‖A x - P x‖ ∂AddCircle.haarAddCircle) =
          ∫ x, ‖fejerMean N (fun x : AddCircle (1 : ℝ) => f x - phi x) x‖
            ∂AddCircle.haarAddCircle := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [hmeanSub N]
        rfl
      _ ≤ ∫ x, ‖f x - phi x‖ ∂AddCircle.haarAddCircle :=
        integral_norm_fejerMean_le hdiff N
      _ ≤ epsilon / 4 := happrox
  have hcenter :
      (∫ x, ‖P x - phi x‖ ∂AddCircle.haarAddCircle) < epsilon / 2 := by
    calc
      (∫ x, ‖P x - phi x‖ ∂AddCircle.haarAddCircle) ≤
          ∫ _x : AddCircle (1 : ℝ), ‖P - phiC‖
            ∂AddCircle.haarAddCircle := by
        apply integral_mono ht2 (integrable_const ‖P - phiC‖)
        intro x
        exact (P - phiC).norm_coe_le_norm x
      _ = ‖P - phiC‖ := by simp
      _ < epsilon / 2 := hcenterNorm
  have hlast :
      (∫ x, ‖phi x - f x‖ ∂AddCircle.haarAddCircle) ≤ epsilon / 4 := by
    calc
      (∫ x, ‖phi x - f x‖ ∂AddCircle.haarAddCircle) =
          ∫ x, ‖f x - phi x‖ ∂AddCircle.haarAddCircle := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [norm_sub_rev]
      _ ≤ epsilon / 4 := happrox
  have hfinal :
      (∫ x, ‖fejerMean N f x - f x‖ ∂AddCircle.haarAddCircle) < epsilon := by
    change (∫ x, ‖A x - f x‖ ∂AddCircle.haarAddCircle) < epsilon
    exact lt_of_le_of_lt htriangle (by linarith)
  have herrNonneg : 0 ≤
      ∫ x, ‖fejerMean N f x - f x‖ ∂AddCircle.haarAddCircle :=
    integral_nonneg fun _ => norm_nonneg _
  rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg herrNonneg]
  exact hfinal

/- Proof idea: choose an index with error at most 2^(-(j+1)) for every j. -/
theorem exists_fejerApproximation
    {f : AddCircle (1 : ℝ) → ℂ}
    (hf : Integrable f AddCircle.haarAddCircle) :
    Nonempty (FejerApproximation f) := by
  /- Proof idea: For each `j`, use convergence to choose an index whose integral error is at most
  `2^(-(j+1):Real)`; compare the resulting nonnegative series with the convergent geometric
  series. -/
  let err : ℕ → ℝ := fun N =>
    ∫ x, ‖fejerMean N f x - f x‖ ∂AddCircle.haarAddCircle
  have herr0 (N : ℕ) : 0 ≤ err N := by
    dsimp [err]
    exact integral_nonneg fun _ => norm_nonneg _
  have hconv := fejerMean_tendsto_L1 hf
  rw [Metric.tendsto_atTop] at hconv
  have hchoose (j : ℕ) :
      ∃ N : ℕ, err N ≤ ((1 : ℝ) / 2) ^ (j + 1) := by
    have hr : 0 < ((1 : ℝ) / 2) ^ (j + 1) := by positivity
    obtain ⟨N, hN⟩ := hconv (((1 : ℝ) / 2) ^ (j + 1)) hr
    refine ⟨N, le_of_lt ?_⟩
    have h := hN N le_rfl
    simpa [err, dist_zero_right, Real.norm_eq_abs,
      abs_of_nonneg (herr0 N)] using h
  let index : ℕ → ℕ := fun j => Classical.choose (hchoose j)
  have hindex (j : ℕ) : err (index j) ≤ ((1 : ℝ) / 2) ^ (j + 1) :=
    Classical.choose_spec (hchoose j)
  have hgeom : Summable (fun j : ℕ => ((1 : ℝ) / 2) ^ (j + 1)) := by
    simpa [pow_succ', mul_comm] using
      summable_geometric_two.mul_left ((1 : ℝ) / 2)
  refine ⟨{ index := index, summable_error := ?_ }⟩
  change Summable (fun j => err (index j))
  exact Summable.of_nonneg_of_le (fun j => herr0 (index j)) hindex hgeom

end Theorem14.Internal
