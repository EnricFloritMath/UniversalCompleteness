import Theorem14.Definitions

/-! # Theorem 1.4: canonical absolutely summable Fourier synthesis -/

noncomputable section

open MeasureTheory
open scoped BigOperators Topology

namespace Theorem14.Internal

/- Proof idea: apply norm summability in the CMap Banach space. -/
private lemma summable_fourierSeries_of_summable_norm
    {c : ℤ → ℂ} (hc : Summable (fun k : ℤ => ‖c k‖)) :
    Summable (fun k : ℤ => c k •
      (fourier k : C(AddCircle (1 : ℝ), ℂ))) := by
  /- Proof idea: Rewrite each continuous-map norm as `norm(c k)` and apply the norm-summability criterion. -/
  apply Summable.of_norm
  simpa only [norm_smul, fourier_norm, mul_one] using hc

/- Proof idea: norm of a convergent Banach-space sum. -/
private lemma norm_fourierSynthesis_le
    {c : ℤ → ℂ} (hc : Summable (fun k : ℤ => ‖c k‖)) :
    ‖fourierSynthesis c‖ ≤ ∑' k : ℤ, ‖c k‖ := by
  /- Proof idea: Apply the standard norm-of-sum bound to the Banach-valued series. -/
  rw [fourierSynthesis]
  have hnorm : Summable (fun k : ℤ =>
      ‖c k • (fourier k : C(AddCircle (1 : ℝ), ℂ))‖) := by
    simpa only [norm_smul, fourier_norm, mul_one] using hc
  simpa only [norm_smul, fourier_norm, mul_one] using
    norm_tsum_le_tsum_norm hnorm

/- Proof idea: move the continuous coefficient functional through the summable series. -/
theorem fourierCoeff_fourierSynthesis
    {c : ℤ → ℂ} (hc : Summable (fun k : ℤ => ‖c k‖)) (n : ℤ) :
    fourierCoeff (fourierSynthesis c) n = c n := by
  /- Proof idea: Move the continuous linear coefficient functional through the summable Banach series and
  reduce by character orthogonality. -/
  classical
  have hint (f : C(AddCircle (1 : ℝ), ℂ)) :
      Integrable (f : AddCircle (1 : ℝ) → ℂ) AddCircle.haarAddCircle :=
    f.continuous.integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset isClosed_closure (Set.subset_univ _))
  let coeffLM : C(AddCircle (1 : ℝ), ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun f => fourierCoeff f n
      map_add' := fun f g => by
        simpa only [ContinuousMap.coe_add, Pi.add_apply] using
          congrFun (fourierCoeff.add (hint f) (hint g)) n
      map_smul' := fun a f => by
        change fourierCoeff (a • (f : AddCircle (1 : ℝ) → ℂ)) n =
          a • fourierCoeff (f : AddCircle (1 : ℝ) → ℂ) n
        exact fourierCoeff.const_smul (f : AddCircle (1 : ℝ) → ℂ) a n }
  let coeffCLM : C(AddCircle (1 : ℝ), ℂ) →L[ℂ] ℂ :=
    coeffLM.mkContinuous 1 (fun f => by
      change ‖fourierCoeff f n‖ ≤ 1 * ‖f‖
      rw [one_mul, fourierCoeff]
      have hpoint : ∀ᵐ x : AddCircle (1 : ℝ) ∂AddCircle.haarAddCircle,
          ‖fourier (-n) x • f x‖ ≤ ‖f‖ := by
        exact ae_of_all _ fun x => by
          calc
            ‖fourier (-n) x • f x‖ = ‖f x‖ := by
              simp [fourier_apply]
            _ ≤ ‖f‖ := f.norm_coe_le_norm x
      simpa using norm_integral_le_of_norm_le_const hpoint)
  have hs := summable_fourierSeries_of_summable_norm hc
  change coeffCLM (fourierSynthesis c) = c n
  rw [fourierSynthesis, ContinuousLinearMap.map_tsum coeffCLM hs]
  change (∑' k : ℤ, fourierCoeff
    (c k • (fourier k : C(AddCircle (1 : ℝ), ℂ))) n) = c n
  have hcoeff (k : ℤ) : fourierCoeff
      (c k • (fourier k : C(AddCircle (1 : ℝ), ℂ))) n =
        c k • fourierCoeff (T := (1 : ℝ)) (fourier k) n := by
    simpa only [ContinuousMap.coe_smul, Pi.smul_apply] using
      fourierCoeff.const_smul
        (fourier k : AddCircle (1 : ℝ) → ℂ) (c k) n
  simp_rw [hcoeff]
  simp_rw [fourierCoeff_fourier]
  rw [tsum_eq_single n]
  · simp
  · intro k hk
    simp [Ne.symm hk]

/- Proof idea: identify the difference with synthesis of c-d and apply the norm bound. -/
theorem norm_fourierSynthesis_sub_le
    {c d : ℤ → ℂ}
    (hc : Summable (fun k : ℤ => ‖c k‖))
    (hd : Summable (fun k : ℤ => ‖d k‖))
    (hcd : Summable (fun k : ℤ => ‖c k - d k‖)) :
    ‖fourierSynthesis c - fourierSynthesis d‖ ≤
      ∑' k : ℤ, ‖c k - d k‖ := by
  /- Proof idea: Identify the difference with synthesis of `c-d` using summability, then apply `norm_fourierSynthesis_le`. -/
  have hsc := summable_fourierSeries_of_summable_norm hc
  have hsd := summable_fourierSeries_of_summable_norm hd
  have heq : fourierSynthesis c - fourierSynthesis d =
      fourierSynthesis (fun k => c k - d k) := by
    rw [fourierSynthesis, fourierSynthesis, fourierSynthesis,
      ← hsc.tsum_sub hsd]
    apply tsum_congr
    intro k
    exact (sub_smul (c k) (d k) (fourier k : C(AddCircle (1 : ℝ), ℂ))).symm
  rw [heq]
  exact norm_fourierSynthesis_le hcd

end Theorem14.Internal
