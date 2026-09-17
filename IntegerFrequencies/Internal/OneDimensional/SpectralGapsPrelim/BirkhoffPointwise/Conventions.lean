import SpectralGapsPrelim.BirkhoffPointwise.Definitions

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Topology ENNReal

namespace SpectralGapsPrelim.BirkhoffPointwise

variable {X : Type*} [MeasurableSpace X]
variable {μ : Measure X} {τ : X → X}

set_option linter.unusedSectionVars false in
/-- Mathlib's `birkhoffAverage` is the finite sum divided by the length. -/
lemma birkhoffAverage_eq_sum_div
    (F : X → ℝ) (N : ℕ) (x : X) :
    birkhoffAverage ℝ τ F N x =
      (Finset.sum (Finset.range N) (fun q => F (τ^[q] x))) / (N : ℝ) := by
  simp [birkhoffAverage, birkhoffSum, div_eq_inv_mul]

/-- Integrability is preserved by composition with a measure-preserving map. -/
lemma integrable_comp_measurePreserving
    (hτ_mp : MeasurePreserving τ μ μ)
    {G : X → ℝ} (hG : Integrable G μ) :
    Integrable (fun x => G (τ x)) μ := by
  change Integrable (G ∘ τ) μ
  exact hτ_mp.integrable_comp_of_integrable hG

/-- Integral invariance under a non-invertible measure-preserving map. -/
lemma integral_comp_measurePreserving
    (hτ_mp : MeasurePreserving τ μ μ)
    {G : X → ℝ} (hG : Integrable G μ) :
    ∫ x, G (τ x) ∂μ = ∫ x, G x ∂μ := by
  have hG_map : AEStronglyMeasurable G (Measure.map τ μ) := by
    rw [hτ_mp.map_eq]
    exact hG.aestronglyMeasurable
  have hmap := MeasureTheory.integral_map hτ_mp.aemeasurable hG_map
  rw [hτ_mp.map_eq] at hmap
  exact hmap.symm

/-- Integrability of every forward iterate. -/
lemma integrable_comp_iterate_measurePreserving
    (hτ_mp : MeasurePreserving τ μ μ)
    {G : X → ℝ} (hG : Integrable G μ) (n : ℕ) :
    Integrable (fun x => G (τ^[n] x)) μ := by
  change Integrable (G ∘ τ^[n]) μ
  exact (hτ_mp.iterate n).integrable_comp_of_integrable hG

/-- Integral invariance under every forward iterate. -/
lemma integral_comp_iterate_measurePreserving
    (hτ_mp : MeasurePreserving τ μ μ)
    {G : X → ℝ} (hG : Integrable G μ) (n : ℕ) :
    ∫ x, G (τ^[n] x) ∂μ = ∫ x, G x ∂μ := by
  exact integral_comp_measurePreserving (τ := τ^[n]) (hτ_mp.iterate n) hG

/-- The representative chosen by `strongRep` is strongly measurable. -/
lemma strongRep_stronglyMeasurable
    {F : X → ℝ} (hF : Integrable F μ) :
    StronglyMeasurable (strongRep (μ := μ) hF) := by
  simpa [strongRep] using hF.aestronglyMeasurable.stronglyMeasurable_mk

/-- Raw function equals its strong representative a.e. -/
lemma strongRep_ae_eq
    {F : X → ℝ} (hF : Integrable F μ) :
    F =ᵐ[μ] strongRep (μ := μ) hF := by
  simpa [strongRep] using hF.aestronglyMeasurable.ae_eq_mk

/-- Symmetric orientation of `strongRep_ae_eq`. -/
lemma strongRep_ae_eq_symm
    {F : X → ℝ} (hF : Integrable F μ) :
    strongRep (μ := μ) hF =ᵐ[μ] F := by
  exact (strongRep_ae_eq (μ := μ) hF).symm

/-- The strong representative of an integrable function is integrable. -/
lemma strongRep_integrable
    {F : X → ℝ} (hF : Integrable F μ) :
    Integrable (strongRep (μ := μ) hF) μ := by
  exact hF.congr (strongRep_ae_eq (μ := μ) hF)

/-- A.e. equality propagates to all forward iterates simultaneously. -/
lemma ae_forall_iterate_eq_of_ae_eq
    (hτ_mp : MeasurePreserving τ μ μ)
    {F G : X → ℝ} (hFG : F =ᵐ[μ] G) :
    ∀ᵐ x ∂μ, ∀ n : ℕ, F (τ^[n] x) = G (τ^[n] x) := by
  exact ae_all_iff.mpr fun n =>
    (hτ_mp.iterate n).quasiMeasurePreserving.ae (hFG.mono fun _ h => h)

/-- Birkhoff averages respect a.e. equality of observables. -/
lemma birkhoffAverage_ae_eq_of_ae_eq
    (hτ_mp : MeasurePreserving τ μ μ)
    {F G : X → ℝ} (hFG : F =ᵐ[μ] G) (N : ℕ) :
    (fun x => birkhoffAverage ℝ τ F N x)
      =ᵐ[μ]
    (fun x => birkhoffAverage ℝ τ G N x) := by
  simpa using
    MeasureTheory.Measure.QuasiMeasurePreserving.birkhoffAverage_ae_eq_of_ae_eq
      (R := ℝ) hτ_mp.quasiMeasurePreserving hFG N

/-- A.e. congruence for Birkhoff-average tendsto statements. -/
lemma tendsto_birkhoffAverage_congr_ae
    (hτ_mp : MeasurePreserving τ μ μ)
    {F G : X → ℝ} (hFG : F =ᵐ[μ] G) {c : ℝ} :
    (∀ᵐ x ∂μ,
      Tendsto (fun N : ℕ => birkhoffAverage ℝ τ F N x)
        atTop (nhds c))
    ↔
    (∀ᵐ x ∂μ,
      Tendsto (fun N : ℕ => birkhoffAverage ℝ τ G N x)
        atTop (nhds c)) := by
  have hAll :
      ∀ᵐ x ∂μ, ∀ N : ℕ,
        birkhoffAverage ℝ τ F N x = birkhoffAverage ℝ τ G N x := by
    exact ae_all_iff.mpr fun N =>
      birkhoffAverage_ae_eq_of_ae_eq (τ := τ) hτ_mp hFG N
  constructor
  · intro hF_tendsto
    filter_upwards [hAll, hF_tendsto] with x hx htx
    exact Tendsto.congr' (Filter.Eventually.of_forall hx) htx
  · intro hG_tendsto
    filter_upwards [hAll, hG_tendsto] with x hx htx
    exact Tendsto.congr' (Filter.Eventually.of_forall fun N => (hx N).symm) htx

/-- Birkhoff averages of an integrable observable are integrable. -/
lemma integrable_birkhoffAverage
    (hτ_mp : MeasurePreserving τ μ μ)
    {F : X → ℝ} (hF : Integrable F μ) (N : ℕ) :
    Integrable (fun x => birkhoffAverage ℝ τ F N x) μ := by
  have hsum :
      Integrable (fun x => Finset.sum (Finset.range N) (fun q => F (τ^[q] x))) μ := by
    exact integrable_finsetSum (Finset.range N) fun q _hq =>
      integrable_comp_iterate_measurePreserving (τ := τ) hτ_mp hF q
  change Integrable (fun x => (N : ℝ)⁻¹ • birkhoffSum τ F N x) μ
  change Integrable ((N : ℝ)⁻¹ •
    (fun x => Finset.sum (Finset.range N) (fun q => F (τ^[q] x)))) μ
  exact hsum.smul ((N : ℝ)⁻¹)

/-- Positive-length Birkhoff averages preserve the integral. -/
lemma integral_birkhoffAverage
    (hτ_mp : MeasurePreserving τ μ μ)
    {F : X → ℝ} (hF : Integrable F μ) {N : ℕ} (hN : 0 < N) :
    ∫ x, birkhoffAverage ℝ τ F N x ∂μ = ∫ x, F x ∂μ := by
  have hsum_int :
      ∀ q ∈ Finset.range N, Integrable (fun x => F (τ^[q] x)) μ := by
    intro q _hq
    exact integrable_comp_iterate_measurePreserving (τ := τ) hτ_mp hF q
  calc
    ∫ x, birkhoffAverage ℝ τ F N x ∂μ
        = ∫ x, (N : ℝ)⁻¹ •
            (Finset.sum (Finset.range N) (fun q => F (τ^[q] x))) ∂μ := by
          simp [birkhoffAverage, birkhoffSum]
    _ = (N : ℝ)⁻¹ •
          (∫ x, Finset.sum (Finset.range N) (fun q => F (τ^[q] x)) ∂μ) := by
          rw [integral_smul]
    _ = (N : ℝ)⁻¹ •
          (Finset.sum (Finset.range N) (fun q => ∫ x, F (τ^[q] x) ∂μ)) := by
          rw [integral_finsetSum]
          exact hsum_int
    _ = (N : ℝ)⁻¹ •
          (Finset.sum (Finset.range N) (fun _q => ∫ x, F x ∂μ)) := by
          congr 2 with q
          exact integral_comp_iterate_measurePreserving (τ := τ) hτ_mp hF q
    _ = ∫ x, F x ∂μ := by
          have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
          simp [Finset.sum_const, hN']

/-- Final conversion between Mathlib averages and explicit sum/div notation. -/
lemma ae_tendsto_sum_div_iff_birkhoffAverage
    {F : X → ℝ} {c : ℝ} :
    (∀ᵐ x ∂μ,
      Tendsto
        (fun N : ℕ => birkhoffAverage ℝ τ F N x)
        atTop (nhds c))
    ↔
    (∀ᵐ x ∂μ,
      Tendsto
        (fun N : ℕ =>
          (Finset.sum (Finset.range N) (fun q => F (τ^[q] x))) / (N : ℝ))
        atTop (nhds c)) := by
  constructor
  · intro h
    filter_upwards [h] with x hx
    exact Tendsto.congr'
      (Filter.Eventually.of_forall fun N => birkhoffAverage_eq_sum_div (τ := τ) F N x) hx
  · intro h
    filter_upwards [h] with x hx
    exact Tendsto.congr'
      (Filter.Eventually.of_forall fun N =>
        (birkhoffAverage_eq_sum_div (τ := τ) F N x).symm) hx

end SpectralGapsPrelim.BirkhoffPointwise
