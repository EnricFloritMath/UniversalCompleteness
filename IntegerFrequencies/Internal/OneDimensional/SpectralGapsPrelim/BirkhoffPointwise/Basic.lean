import SpectralGapsPrelim.BirkhoffPointwise.DenseCore
import SpectralGapsPrelim.BirkhoffPointwise.Coboundary
import SpectralGapsPrelim.BirkhoffPointwise.MaximalTransfer

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Topology ENNReal

namespace SpectralGapsPrelim.BirkhoffPointwise

variable {X : Type*} [MeasurableSpace X]
variable {μ : Measure X} [IsProbabilityMeasure μ] {τ : X → X}

/-- Fast dense-core approximation sequence used in the final assembly. -/
private lemma exists_fast_core_approx
    (hτ : Ergodic τ μ)
    {F : X → ℝ} (hF : Integrable F μ) :
    ∃ C : ℕ → L2CoboundaryCore (X := X) τ μ,
      ∀ j : ℕ,
        ∫ x, |F x - (C j).toFun (τ := τ) x| ∂μ
          ≤ (1 / 2 : ℝ) ^ (j + 1) := by
  -- Proof idea: apply `exists_core_approx_integral_lt` with
  -- `eps = (1 / 2 : ℝ) ^ (j + 1)` and choose witnesses.
  classical
  have h_exists :
      ∀ j : ℕ,
        ∃ C : L2CoboundaryCore (X := X) τ μ,
          ∫ x, |F x - C.toFun (τ := τ) x| ∂μ
            < (1 / 2 : ℝ) ^ (j + 1) := by
    intro j
    exact exists_core_approx_integral_lt (τ := τ) hτ hF (by positivity)
  choose C hC using h_exists
  exact ⟨C, fun j => le_of_lt (hC j)⟩

omit [IsProbabilityMeasure μ] in
/-- The fast geometric approximation errors are summable. -/
private lemma summable_fast_core_errors
    {F : X → ℝ} {C : ℕ → L2CoboundaryCore (X := X) τ μ}
    (hC :
      ∀ j : ℕ,
        ∫ x, |F x - (C j).toFun (τ := τ) x| ∂μ
          ≤ (1 / 2 : ℝ) ^ (j + 1)) :
    Summable
      (fun j : ℕ =>
        ∫ x, |F x - (C j).toFun (τ := τ) x| ∂μ) := by
  -- Proof idea: compare nonnegative error integrals with the summable
  -- geometric series `(1 / 2 : ℝ) ^ (j + 1)`.
  have hgeom : Summable (fun j : ℕ => (1 / 2 : ℝ) ^ (j + 1)) := by
    have hbase : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    simpa [Nat.succ_eq_add_one, Function.comp_def] using
      hbase.comp_injective Nat.succ_injective
  exact hgeom.of_nonneg_of_le
    (fun j => integral_nonneg fun x => abs_nonneg _)
    hC

/-- Every member of the chosen dense-core sequence is integrable. -/
private lemma core_sequence_integrable
    (hτ : Ergodic τ μ)
    (C : ℕ → L2CoboundaryCore (X := X) τ μ) :
    ∀ j, Integrable ((C j).toFun (τ := τ)) μ := by
  -- Proof idea: wrapper around `L2CoboundaryCore.integrable_toFun`.
  intro j
  exact L2CoboundaryCore.integrable_toFun (τ := τ) hτ.toMeasurePreserving (C j)

/-- Birkhoff averages converge a.e. on every member of the dense-core sequence. -/
private lemma core_sequence_tendsto_integral
    (hτ : Ergodic τ μ)
    (C : ℕ → L2CoboundaryCore (X := X) τ μ) :
    ∀ j,
      ∀ᵐ x ∂μ,
        Tendsto
          (fun N : ℕ =>
            birkhoffAverage ℝ τ ((C j).toFun (τ := τ)) N x)
          atTop
          (nhds (∫ y, (C j).toFun (τ := τ) y ∂μ)) := by
  -- Proof idea: wrapper around `ae_tendsto_core_birkhoffAverage_integral`.
  intro j
  exact ae_tendsto_core_birkhoffAverage_integral
    (τ := τ) hτ.toMeasurePreserving (C j)

omit [IsProbabilityMeasure μ] in
/-- Convert the internal Mathlib average statement to explicit finite sums. -/
private lemma birkhoffAverage_to_sum_div_ae
    {F : X → ℝ} {c : ℝ}
    (h :
      ∀ᵐ x ∂μ,
        Tendsto
          (fun N : ℕ => birkhoffAverage ℝ τ F N x)
          atTop (nhds c)) :
    ∀ᵐ x ∂μ,
      Tendsto
        (fun N : ℕ =>
          (Finset.sum (Finset.range N) (fun q => F (τ^[q] x))) / (N : ℝ))
        atTop (nhds c) := by
  -- Proof idea: use `ae_tendsto_sum_div_iff_birkhoffAverage`.
  exact ae_tendsto_sum_div_iff_birkhoffAverage.mp h

/--
Statement of the real-valued `L1` pointwise Birkhoff theorem
for an ergodic probability-preserving system.

This theorem supplies the pointwise ergodic input used by the
higher-dimensional integer-frequency proof.
-/
theorem ae_tendsto_birkhoff_average_of_ergodic
    (hτ : Ergodic τ μ)
    {F : X → ℝ} (hF : Integrable F μ) :
    ∀ᵐ x ∂μ,
      Tendsto
        (fun N : ℕ =>
          (Finset.sum (Finset.range N) (fun q => F (τ^[q] x))) / (N : ℝ))
        atTop
        (nhds (∫ y, F y ∂μ)) := by
  -- Proof idea:
  -- 1. approximate `F` in raw `L1` by summably close `L2` coboundary cores;
  -- 2. use coboundary convergence on each core;
  -- 3. transfer convergence to `F` via the weak-type maximal inequality;
  -- 4. convert `birkhoffAverage` back to explicit finite sums.
  -- Private assembly targets above isolate those four proof obligations.
  rcases exists_fast_core_approx (τ := τ) hτ hF with ⟨C, hC⟩
  have hD_int :
      ∀ j, Integrable ((C j).toFun (τ := τ)) μ :=
    core_sequence_integrable (τ := τ) hτ C
  have hD_tendsto :
      ∀ j,
        ∀ᵐ x ∂μ,
          Tendsto
            (fun N : ℕ =>
              birkhoffAverage ℝ τ ((C j).toFun (τ := τ)) N x)
            atTop
            (nhds (∫ y, (C j).toFun (τ := τ) y ∂μ)) :=
    core_sequence_tendsto_integral (τ := τ) hτ C
  have hD_summable :
      Summable
        (fun j : ℕ =>
          ∫ x, |F x - (C j).toFun (τ := τ) x| ∂μ) :=
    summable_fast_core_errors (τ := τ) hC
  have havg :
      ∀ᵐ x ∂μ,
        Tendsto
          (fun N : ℕ => birkhoffAverage ℝ τ F N x)
          atTop
          (nhds (∫ y, F y ∂μ)) :=
    ae_tendsto_of_summable_L1_approx
      (τ := τ) hτ.toMeasurePreserving hF hD_int hD_tendsto hD_summable
  exact birkhoffAverage_to_sum_div_ae (τ := τ) havg

end SpectralGapsPrelim.BirkhoffPointwise
