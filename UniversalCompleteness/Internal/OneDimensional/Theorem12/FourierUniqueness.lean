import Mathlib.Analysis.Fourier.AddCircle

noncomputable section

open scoped ComplexConjugate ENNReal
open MeasureTheory

namespace Theorem12.Generic



-- Proof idea: package the Bochner integral as a bounded complex-linear functional.

def continuousTestFunctional (g : AddCircle (1 : ℝ) → ℂ)
    (hg : Integrable g AddCircle.haarAddCircle) :
    ContinuousMap (AddCircle (1 : ℝ)) ℂ →L[ℂ] ℂ := by
  let integralMul : ContinuousMap (AddCircle (1 : ℝ)) ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun phi => ∫ x, phi x * g x ∂AddCircle.haarAddCircle
      map_add' := by
        intro phi psi
        have hphi : Integrable (fun x => phi x * g x) AddCircle.haarAddCircle :=
          hg.bdd_mul phi.continuous.aestronglyMeasurable
            (Filter.Eventually.of_forall fun x => ContinuousMap.norm_coe_le_norm phi x)
        have hpsi : Integrable (fun x => psi x * g x) AddCircle.haarAddCircle :=
          hg.bdd_mul psi.continuous.aestronglyMeasurable
            (Filter.Eventually.of_forall fun x => ContinuousMap.norm_coe_le_norm psi x)
        simpa only [ContinuousMap.add_apply, add_mul] using integral_add hphi hpsi
      map_smul' := by
        intro c phi
        simpa only [ContinuousMap.smul_apply, RingHom.id_apply, smul_eq_mul, mul_assoc] using
          (integral_smul c (fun x => phi x * g x) (μ := AddCircle.haarAddCircle)) }
  refine integralMul.mkContinuous (∫ x, ‖g x‖ ∂AddCircle.haarAddCircle) ?_
  intro phi
  calc
    ‖integralMul phi‖ ≤ ∫ x, ‖phi‖ * ‖g x‖ ∂AddCircle.haarAddCircle :=
      norm_integral_le_of_norm_le (hg.norm.const_mul ‖phi‖)
        (Filter.Eventually.of_forall fun x => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (ContinuousMap.norm_coe_le_norm phi x)
            (norm_nonneg _))
    _ = ‖phi‖ * ∫ x, ‖g x‖ ∂AddCircle.haarAddCircle :=
      integral_const_mul ‖phi‖ (fun x => ‖g x‖)
    _ = (∫ x, ‖g x‖ ∂AddCircle.haarAddCircle) * ‖phi‖ := mul_comm _ _


-- Proof idea: unfold the functional and normalize the Fourier sign.

theorem continuousTestFunctional_character_eq_zero (g : AddCircle (1 : ℝ) → ℂ)
    (hg : Integrable g AddCircle.haarAddCircle)
    (hcoeff : ∀ n : ℤ, fourierCoeff g n = 0) (n : ℤ) :
    continuousTestFunctional g hg (fourier n) = 0 := by
  simpa [continuousTestFunctional, fourierCoeff, smul_eq_mul] using hcoeff (-n)


-- Proof idea: specialize the AddCircle density theorem.

theorem dense_span_addCircle_characters :
    (Submodule.span ℂ (Set.range (@fourier (1 : ℝ)))).topologicalClosure = ⊤ :=
  span_fourier_closure_eq_top


-- Proof idea: approximate the phase, obtain integral norm zero, conclude AE zero.

theorem ae_eq_zero_of_integral_mul_continuous_eq_zero
    (g : AddCircle (1 : ℝ) → ℂ)
    (hg : Integrable g AddCircle.haarAddCircle)
    (htest : ∀ phi : ContinuousMap (AddCircle (1 : ℝ)) ℂ,
      (∫ x, phi x * g x ∂AddCircle.haarAddCircle) = 0) :
    g =ᵐ[AddCircle.haarAddCircle] 0 := by
  let mu : Measure (AddCircle (1 : ℝ)) := AddCircle.haarAddCircle
  let phase : AddCircle (1 : ℝ) → ℂ := fun x => conj (g x) / (‖g x‖ : ℂ)
  let nu : Measure (AddCircle (1 : ℝ)) :=
    mu.withDensity (fun x => ENNReal.ofReal ‖g x‖)
  letI : IsFiniteMeasure nu := by
    dsimp [nu]
    exact isFiniteMeasure_withDensity_ofReal hg.norm.hasFiniteIntegral
  have hphase_meas_mu : AEStronglyMeasurable phase mu := by
    dsimp [phase, mu]
    have hg_meas : AEMeasurable g AddCircle.haarAddCircle :=
      hg.aestronglyMeasurable.aemeasurable
    exact ((Complex.continuous_conj.measurable.comp_aemeasurable hg_meas).div
      (Complex.continuous_ofReal.measurable.comp_aemeasurable hg_meas.norm)).aestronglyMeasurable
  have hphase_meas_nu : AEStronglyMeasurable phase nu :=
    AEStronglyMeasurable.mono_ac
      (withDensity_absolutelyContinuous mu (fun x => ENNReal.ofReal ‖g x‖))
      hphase_meas_mu
  have hphase_norm (x : AddCircle (1 : ℝ)) : ‖phase x‖ ≤ 1 := by
    by_cases hx : g x = 0
    · simp [phase, hx]
    · simp [phase, hx]
  have hphase_int_nu : Integrable phase nu := by
    exact (MemLp.of_bound hphase_meas_nu 1
      (Filter.Eventually.of_forall hphase_norm)).integrable le_rfl
  have hphase_mul (x : AddCircle (1 : ℝ)) : phase x * g x = (‖g x‖ : ℂ) := by
    by_cases hx : g x = 0
    · simp [phase, hx]
    · dsimp [phase]
      rw [div_mul_eq_mul_div, ← Complex.normSq_eq_conj_mul_self,
        Complex.normSq_eq_norm_sq]
      norm_num
      field_simp
  have hphase_int_mu : Integrable (fun x => phase x * g x) mu := by
    apply hg.bdd_mul hphase_meas_mu
    exact Filter.Eventually.of_forall hphase_norm
  have hnorm_int_nonneg : 0 ≤ ∫ x, ‖g x‖ ∂mu :=
    integral_nonneg fun _ => norm_nonneg _
  have hsmall : ∀ ε : ℝ, 0 < ε → (∫ x, ‖g x‖ ∂mu) ≤ ε := by
    intro ε hε
    obtain ⟨psi, hpsi_close, _hpsi_int⟩ :=
      hphase_int_nu.exists_boundedContinuous_integral_sub_le hε
    have hpsi_mul_int : Integrable (fun x => psi x * g x) mu := by
      apply hg.bdd_mul psi.continuous.aestronglyMeasurable
      exact Filter.Eventually.of_forall fun x =>
        BoundedContinuousFunction.norm_coe_le_norm psi x
    have hdiff_int : Integrable (fun x => (phase x - psi x) * g x) mu := by
      refine (hphase_int_mu.sub hpsi_mul_int).congr ?_
      exact Filter.Eventually.of_forall fun x => by simp [sub_mul]
    have hpsi_zero : (∫ x, psi x * g x ∂mu) = 0 := by
      simpa [mu] using htest psi.toContinuousMap
    have hphase_eq_diff :
        (∫ x, phase x * g x ∂mu) = ∫ x, (phase x - psi x) * g x ∂mu := by
      simp_rw [sub_mul]
      rw [integral_sub hphase_int_mu hpsi_mul_int, hpsi_zero, sub_zero]
    have hweighted :
        (∫ x, ‖phase x - psi x‖ ∂nu) =
          ∫ x, ‖phase x - psi x‖ * ‖g x‖ ∂mu := by
      rw [integral_withDensity_eq_integral_toReal_smul₀]
      · simp [mu, mul_comm]
      · fun_prop
      · exact Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top
    calc
      (∫ x, ‖g x‖ ∂mu) = ‖((∫ x, ‖g x‖ ∂mu : ℝ) : ℂ)‖ := by
        simp [Real.norm_eq_abs, abs_of_nonneg hnorm_int_nonneg]
      _ = ‖∫ x, phase x * g x ∂mu‖ := by
        congr 1
        rw [← integral_complex_ofReal]
        exact integral_congr_ae
          (Filter.Eventually.of_forall fun x => (hphase_mul x).symm)
      _ = ‖∫ x, (phase x - psi x) * g x ∂mu‖ := by rw [hphase_eq_diff]
      _ ≤ ∫ x, ‖(phase x - psi x) * g x‖ ∂mu :=
        norm_integral_le_of_norm_le hdiff_int.norm
          (Filter.Eventually.of_forall fun _ => le_rfl)
      _ = ∫ x, ‖phase x - psi x‖ * ‖g x‖ ∂mu := by simp only [norm_mul]
      _ = ∫ x, ‖phase x - psi x‖ ∂nu := hweighted.symm
      _ ≤ ε := hpsi_close
  have hnorm_int_zero : (∫ x, ‖g x‖ ∂mu) = 0 := by
    apply le_antisymm
    · by_contra hnot
      have hpos : 0 < ∫ x, ‖g x‖ ∂mu := lt_of_not_ge hnot
      linarith [hsmall ((∫ x, ‖g x‖ ∂mu) / 2) (half_pos hpos)]
    · exact hnorm_int_nonneg
  have hnorm_ae : (fun x => ‖g x‖) =ᵐ[mu] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall fun _ => norm_nonneg _) hg.norm).1 hnorm_int_zero
  rw [show mu = AddCircle.haarAddCircle from rfl] at hnorm_ae
  filter_upwards [hnorm_ae] with x hx
  simpa using norm_eq_zero.mp hx


-- Proof idea: extend character annihilation by density, then use `ae_eq_zero_of_integral_mul_continuous_eq_zero`.

theorem ae_eq_zero_of_all_fourierCoeff_eq_zero (g : AddCircle (1 : ℝ) → ℂ)
    (hg : Integrable g AddCircle.haarAddCircle)
    (hcoeff : ∀ n : ℤ, fourierCoeff g n = 0) :
    g =ᵐ[AddCircle.haarAddCircle] 0 := by
  let F := continuousTestFunctional g hg
  have hspan : Submodule.span ℂ (Set.range (@fourier (1 : ℝ))) ≤ F.ker := by
    refine Submodule.span_le.2 ?_
    rintro phi ⟨n, rfl⟩
    exact continuousTestFunctional_character_eq_zero g hg hcoeff n
  have hclosure :
      (Submodule.span ℂ (Set.range (@fourier (1 : ℝ)))).topologicalClosure ≤ F.ker :=
    F.isClosed_ker.closure_subset_iff.2 hspan
  have hF : F = 0 := by
    ext phi
    have hphi : phi ∈ F.ker := by
      apply hclosure
      rw [dense_span_addCircle_characters]
      trivial
    exact hphi
  apply ae_eq_zero_of_integral_mul_continuous_eq_zero g hg
  intro phi
  change F phi = 0
  rw [hF]
  rfl

end Theorem12.Generic
