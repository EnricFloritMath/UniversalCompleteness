import PeriodicWeakGapsHD.HigherDim.WeightedDirichletAverages
import PeriodicWeakGapsHD.HigherDim.PeakCandidates

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Topology ENNReal FourierTransform

namespace SpectralGapsPrelim.HigherDim

/-!
Small weighted Sobolev peaks from the weighted Dirichlet coefficients.
-/

private lemma weightedEnergy_eq_lintegral_norm_sq_toReal {d : ℕ}
    {A : Set (E d)} {alpha : ℝ} {P : E d → ℂ}
    (hP : WeightedEnergyIntegrable alpha A P) :
    weightedEnergy alpha A P =
      (∫⁻ xi,
        ENNReal.ofReal (‖P xi‖ ^ 2)
        ∂(weightedMeasure alpha A)).toReal := by
  let μ := weightedMeasure alpha A
  have hP' : MemLp P 2 μ := hP
  have hnorm : weightedEnergy alpha A P = ‖hP'.toLp P‖ ^ 2 := by
    unfold weightedEnergy
    rw [Lp.norm_toLp P hP']
  rw [hnorm]
  rw [show ‖hP'.toLp P‖ ^ 2 =
      Complex.re (inner ℂ (hP'.toLp P) (hP'.toLp P)) from
    norm_sq_eq_re_inner (𝕜 := ℂ) (hP'.toLp P)]
  rw [L2.inner_def]
  rw [L2.integral_inner_eq_sq_eLpNorm (𝕜 := ℂ) (hP'.toLp P)]
  apply congrArg ENNReal.toReal
  refine lintegral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp hP'] with xi hxi
  rw [hxi]
  simp [enorm_eq_nnnorm]

private lemma continuous_sobolevWeight_of_nonneg {d : ℕ}
    {alpha : ℝ} (halpha_nonneg : 0 ≤ alpha) :
    Continuous (sobolevWeight (d := d) alpha) := by
  by_cases hzero : alpha = 0
  · rw [hzero]
    unfold sobolevWeight sobolevPower
    simpa using
      (continuous_const : Continuous (fun _ : E d => (1 + 1 : ℝ)))
  · have hpow :
        Continuous fun xi : E d => ‖xi‖ ^ (2 * alpha) :=
      continuous_norm.rpow_const fun _ =>
        Or.inr (mul_nonneg (by norm_num) halpha_nonneg)
    unfold sobolevWeight sobolevPower
    simp only [hzero, ↓reduceIte]
    exact ((continuous_const : Continuous (fun _ : E d => (1 : ℝ))).add hpow)

private lemma aestronglyMeasurable_sobolevWeight_add_natVec {d : ℕ}
    {alpha : ℝ} (halpha_nonneg : 0 ≤ alpha)
    (k : Fin d → ℕ) (μ : Measure (E d)) :
    AEStronglyMeasurable
      (fun t : E d => sobolevWeight alpha (t + natVec k)) μ := by
  exact
    ((continuous_sobolevWeight_of_nonneg (d := d) halpha_nonneg).comp
      (continuous_id.add continuous_const)).aestronglyMeasurable

private lemma norm_exp2piI (u : ℝ) :
    ‖exp2piI u‖ = 1 := by
  simp [exp2piI, Complex.norm_exp]

private lemma isCompact_unitCube_hd (d : ℕ) :
    IsCompact (unitCube d) := by
  let e : E d ≃ₜ (Fin d → ℝ) :=
    PiLp.homeomorph (p := (2 : ℝ≥0∞)) (β := fun _ : Fin d => ℝ)
  let rawCube : Set (Fin d → ℝ) :=
    Set.univ.pi fun _ : Fin d => Set.Icc (0 : ℝ) 1
  have hraw_compact : IsCompact rawCube := by
    simpa [rawCube] using
      (isCompact_univ_pi fun _ : Fin d =>
        (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)))
  have hcube : unitCube d = e ⁻¹' rawCube := by
    ext x
    change (∀ i : Fin d, 0 ≤ coord x i ∧ coord x i ≤ 1) ↔ e x ∈ rawCube
    simp only [rawCube, Set.mem_pi, Set.mem_univ, Set.mem_Icc]
    constructor
    · intro hx i _
      exact hx i
    · intro hx i
      exact hx i trivial
  rw [hcube]
  exact e.isCompact_preimage.mpr hraw_compact

private lemma integrable_sobolevWeight_add_natVec_mul_norm_sq {d : ℕ}
    {A : Set (E d)} {alpha : ℝ} {Phi : E d → ℂ}
    (hA : AContextHD d A) (halpha_nonneg : 0 ≤ alpha)
    (hPhi_L2 : MemLp Phi 2 (volume.restrict A))
    (k : Fin d → ℕ) :
    Integrable
      (fun t : E d => sobolevWeight alpha (t + natVec k) * ‖Phi t‖ ^ 2)
      (volume.restrict A) := by
  have hsq_int :
      Integrable (fun t : E d => ‖Phi t‖ ^ 2) (volume.restrict A) :=
    hPhi_L2.integrable_norm_pow (by norm_num)
  have hcont :
      Continuous fun t : E d => sobolevWeight alpha (t + natVec k) :=
    (continuous_sobolevWeight_of_nonneg (d := d) halpha_nonneg).comp
      (continuous_id.add continuous_const)
  rcases (isCompact_unitCube_hd d).exists_bound_of_continuousOn
      hcont.continuousOn with
    ⟨M, hM⟩
  let C : ℝ := max M 0
  refine (hsq_int.const_mul C).mono_nonneg ?_ ?_ ?_
  · exact
      (aestronglyMeasurable_sobolevWeight_add_natVec
        (d := d) halpha_nonneg k (volume.restrict A)).mul
        (hPhi_L2.aestronglyMeasurable.norm.pow 2)
  · exact Filter.Eventually.of_forall fun t =>
      mul_nonneg (sobolevWeight_nonneg alpha (t + natVec k)) (sq_nonneg _)
  · filter_upwards [ae_restrict_mem hA.measurable] with t htA
    have hle_norm :
        ‖sobolevWeight alpha (t + natVec k)‖ ≤ M :=
      hM t (hA.subset_unitCube htA)
    have hle : sobolevWeight alpha (t + natVec k) ≤ C := by
      calc
        sobolevWeight alpha (t + natVec k)
            ≤ ‖sobolevWeight alpha (t + natVec k)‖ := by
              exact le_abs_self _
        _ ≤ M := hle_norm
        _ ≤ C := le_max_left _ _
    exact mul_le_mul_of_nonneg_right hle (sq_nonneg _)

private theorem shifted_phase_PhiZeroExt_lintegral
    {d : ℕ} {A : Set (E d)} {alpha : ℝ} {y : E d}
    {Phi : E d → ℂ}
    (hA : AContextHD d A) (halpha : AlphaLeDimHalf d alpha)
    (hPhi_L2 : MemLp Phi 2 (volume.restrict A))
    (k : Fin d → ℕ) (b : ℂ) :
    ∫⁻ xi,
        ENNReal.ofReal
          (‖exp2piI (-(inner ℝ y xi)) *
            (b * PhiZeroExt A Phi (xi - natVec k))‖ ^ 2)
        ∂(weightedMeasure alpha A)
      =
      ∫⁻ t,
        ENNReal.ofReal
          (sobolevWeight alpha (t + natVec k) *
            ‖Phi t‖ ^ 2 * ‖b‖ ^ 2)
        ∂(volume.restrict A) := by
  classical
  let S : Set (E d) := latticeTranslate A (fun i : Fin d => (k i : ℤ))
  let ψ : E d → ℂ := fun xi =>
    exp2piI (-(inner ℝ y xi)) *
      (b * PhiZeroExt A Phi (xi - natVec k))
  let G : E d → ℝ≥0∞ := fun xi =>
    ENNReal.ofReal
      (sobolevWeight alpha xi *
        (‖PhiZeroExt A Phi (xi - natVec k)‖ ^ 2 * ‖b‖ ^ 2))
  let R : E d → ℝ≥0∞ := fun t =>
    ENNReal.ofReal
      (sobolevWeight alpha (t + natVec k) * ‖Phi t‖ ^ 2 * ‖b‖ ^ 2)
  have hS_meas : MeasurableSet S :=
    measurableSet_latticeTranslate hA.measurable _
  have hS_subset_spectrum : S ⊆ spectrum A := by
    intro xi hxi
    exact ⟨fun i : Fin d => (k i : ℤ), hxi⟩
  have hPhi0_meas :
      AEStronglyMeasurable
        (fun xi : E d => PhiZeroExt A Phi (xi - natVec k)) volume := by
    have hPhi0 : AEStronglyMeasurable (PhiZeroExt A Phi) volume :=
      PhiZeroExt_aestronglyMeasurable hA.measurable
        hPhi_L2.aestronglyMeasurable
    simpa [Function.comp_def, sub_eq_add_neg] using
      hPhi0.comp_measurePreserving
        (measurePreserving_add_right (μ := volume) (-(natVec k)))
  have hpsi_meas_volume : AEStronglyMeasurable ψ volume := by
    have hphase :
        AEStronglyMeasurable
          (fun xi : E d => exp2piI (-(inner ℝ y xi))) volume := by
      have hcont :
          Continuous fun xi : E d => exp2piI (-(inner ℝ y xi)) := by
        unfold exp2piI
        fun_prop
      exact hcont.aestronglyMeasurable
    exact hphase.mul (hPhi0_meas.const_mul b)
  have hdens_ae :
      AEMeasurable
        (fun xi : E d => ENNReal.ofReal (sobolevWeight alpha xi))
        (volume.restrict (spectrum A)) := by
    exact
      ENNReal.measurable_ofReal.comp_aemeasurable
        ((continuous_sobolevWeight_of_nonneg
          (d := d) halpha.nonneg).aestronglyMeasurable.aemeasurable)
  have hnorm_ae :
      AEMeasurable
        (fun xi : E d => ENNReal.ofReal (‖ψ xi‖ ^ 2))
        (volume.restrict (spectrum A)) := by
    exact
      ENNReal.measurable_ofReal.comp_aemeasurable
        ((hpsi_meas_volume.restrict.norm.pow 2).aemeasurable)
  have hweighted :
      (∫⁻ xi, ENNReal.ofReal (‖ψ xi‖ ^ 2)
          ∂(weightedMeasure alpha A))
        =
        ∫⁻ xi, (fun xi : E d => ENNReal.ofReal (sobolevWeight alpha xi)) xi *
          (fun xi : E d => ENNReal.ofReal (‖ψ xi‖ ^ 2)) xi
          ∂(volume.restrict (spectrum A)) := by
    unfold weightedMeasure
    exact lintegral_withDensity_eq_lintegral_mul₀ hdens_ae hnorm_ae
  have hweighted_to_spectrum :
      (∫⁻ xi, (fun xi : E d => ENNReal.ofReal (sobolevWeight alpha xi)) xi *
          (fun xi : E d => ENNReal.ofReal (‖ψ xi‖ ^ 2)) xi
          ∂(volume.restrict (spectrum A)))
        =
        ∫⁻ xi in spectrum A, G xi ∂volume := by
    apply lintegral_congr
    intro xi
    rw [← ENNReal.ofReal_mul (sobolevWeight_nonneg alpha xi)]
    congr 1
    dsimp [ψ]
    rw [norm_mul, norm_exp2piI, one_mul, norm_mul]
    ring_nf
  have hspectrum_indicator :
      (spectrum A).indicator G = S.indicator G := by
    funext xi
    by_cases hxiS : xi ∈ S
    · have hxis : xi ∈ spectrum A := hS_subset_spectrum hxiS
      simp [hxiS, hxis]
    · have hPhi_zero : PhiZeroExt A Phi (xi - natVec k) = 0 := by
        have hnot : xi - natVec k ∉ A := by
          intro hmem
          apply hxiS
          change xi - intVec (fun i : Fin d => (k i : ℤ)) ∈ A
          rwa [← natVec_eq_intVec_natCast k]
        simp [PhiZeroExt, hnot]
      by_cases hxis : xi ∈ spectrum A
      · simp [G, hxiS, hxis, hPhi_zero]
      · simp [hxiS, hxis]
  have hspectrum_to_S :
      (∫⁻ xi in spectrum A, G xi ∂volume) =
        ∫⁻ xi in S, G xi ∂volume := by
    rw [← lintegral_indicator hA.measurableSet_spectrum,
      ← lintegral_indicator hS_meas]
    rw [hspectrum_indicator]
  have htranslate :
      (∫⁻ xi in S, G xi ∂volume) =
        ∫⁻ t in A, R t ∂volume := by
    have hshift :
        (∫⁻ x, (S.indicator G) (x + natVec k) ∂volume)
          = ∫⁻ x, S.indicator G x ∂volume := by
      exact lintegral_add_right_eq_self
        (μ := volume) (fun x => S.indicator G x) (natVec k)
    have hleft :
        (∫⁻ x, (S.indicator G) (x + natVec k) ∂volume)
          = ∫⁻ x, A.indicator R x ∂volume := by
      apply lintegral_congr
      intro x
      have hxS : x + natVec k ∈ S ↔ x ∈ A := by
        change
          (x + natVec k) - intVec (fun i : Fin d => (k i : ℤ)) ∈ A ↔
            x ∈ A
        rw [← natVec_eq_intVec_natCast k]
        simp
      by_cases hx : x ∈ A
      · have hxs : x + natVec k ∈ S := hxS.mpr hx
        simp [S, G, R, hxs, hx, PhiZeroExt, mul_assoc]
      · have hxs : x + natVec k ∉ S := fun h => hx (hxS.mp h)
        simp [S, G, R, hxs, hx]
    rw [← lintegral_indicator hS_meas, ← lintegral_indicator hA.measurable]
    rw [← hshift, hleft]
  calc
    ∫⁻ xi, ENNReal.ofReal
        (‖exp2piI (-(inner ℝ y xi)) *
          (b * PhiZeroExt A Phi (xi - natVec k))‖ ^ 2)
        ∂(weightedMeasure alpha A)
        = ∫⁻ xi, ENNReal.ofReal (‖ψ xi‖ ^ 2)
            ∂(weightedMeasure alpha A) := by
          rfl
    _ = ∫⁻ xi in spectrum A, G xi ∂volume := by
          rw [hweighted, hweighted_to_spectrum]
    _ = ∫⁻ xi in S, G xi ∂volume := hspectrum_to_S
    _ = ∫⁻ t in A, R t ∂volume := htranslate
    _ = ∫⁻ t, ENNReal.ofReal
          (sobolevWeight alpha (t + natVec k) *
            ‖Phi t‖ ^ 2 * ‖b‖ ^ 2)
        ∂(volume.restrict A) := by
          rfl

private theorem shifted_phase_PhiZeroExt_weightedMemLp_and_lintegral
    {d : ℕ} {A : Set (E d)} {alpha : ℝ} {y : E d}
    {Phi : E d → ℂ}
    (hA : AContextHD d A) (halpha : AlphaLeDimHalf d alpha)
    (hPhi_L2 : MemLp Phi 2 (volume.restrict A))
    (k : Fin d → ℕ) (b : ℂ) :
    MemLp
      (fun xi : E d =>
        exp2piI (-(inner ℝ y xi)) *
          (b * PhiZeroExt A Phi (xi - natVec k)))
      2 (weightedMeasure alpha A) ∧
    ∫⁻ xi,
        ENNReal.ofReal
          (‖exp2piI (-(inner ℝ y xi)) *
            (b * PhiZeroExt A Phi (xi - natVec k))‖ ^ 2)
        ∂(weightedMeasure alpha A)
      =
      ∫⁻ t,
        ENNReal.ofReal
          (sobolevWeight alpha (t + natVec k) *
            ‖Phi t‖ ^ 2 * ‖b‖ ^ 2)
        ∂(volume.restrict A) := by
  let μ : Measure (E d) := weightedMeasure alpha A
  let ψ : E d → ℂ := fun xi =>
    exp2piI (-(inner ℝ y xi)) *
      (b * PhiZeroExt A Phi (xi - natVec k))
  have hlintegral :
      ∫⁻ xi, ENNReal.ofReal (‖ψ xi‖ ^ 2) ∂μ
        =
        ∫⁻ t,
          ENNReal.ofReal
            (sobolevWeight alpha (t + natVec k) *
              ‖Phi t‖ ^ 2 * ‖b‖ ^ 2)
          ∂(volume.restrict A) := by
    simpa [ψ, μ] using
      shifted_phase_PhiZeroExt_lintegral
        (d := d) (A := A) (alpha := alpha) (y := y)
        hA halpha hPhi_L2 k b
  have hPhi0_meas :
      AEStronglyMeasurable
        (fun xi : E d => PhiZeroExt A Phi (xi - natVec k)) volume := by
    have hPhi0 : AEStronglyMeasurable (PhiZeroExt A Phi) volume :=
      PhiZeroExt_aestronglyMeasurable hA.measurable
        hPhi_L2.aestronglyMeasurable
    simpa [Function.comp_def, sub_eq_add_neg] using
      hPhi0.comp_measurePreserving
        (measurePreserving_add_right (μ := volume) (-(natVec k)))
  have hpsi_meas_volume : AEStronglyMeasurable ψ volume := by
    have hphase :
        AEStronglyMeasurable
          (fun xi : E d => exp2piI (-(inner ℝ y xi))) volume := by
      have hcont :
          Continuous fun xi : E d => exp2piI (-(inner ℝ y xi)) := by
        unfold exp2piI
        fun_prop
      exact hcont.aestronglyMeasurable
    exact hphase.mul (hPhi0_meas.const_mul b)
  have hμ_ac : μ ≪ volume := by
    dsimp [μ]
    unfold weightedMeasure
    exact (withDensity_absolutelyContinuous _ _).trans
      Measure.absolutelyContinuous_restrict
  have hpsi_meas : AEStronglyMeasurable ψ μ :=
    AEStronglyMeasurable.mono_ac hμ_ac hpsi_meas_volume
  have hright_ne_top :
      (∫⁻ t,
          ENNReal.ofReal
            (sobolevWeight alpha (t + natVec k) *
              ‖Phi t‖ ^ 2 * ‖b‖ ^ 2)
          ∂(volume.restrict A)) ≠ ∞ := by
    let f : E d → ℝ :=
      fun t => sobolevWeight alpha (t + natVec k) * ‖Phi t‖ ^ 2
    let c : ℝ := ‖b‖ ^ 2
    have hf_int :
        Integrable f (volume.restrict A) :=
      integrable_sobolevWeight_add_natVec_mul_norm_sq
        hA halpha.nonneg hPhi_L2 k
    have hg_int :
        Integrable (fun t => f t * c) (volume.restrict A) :=
      hf_int.mul_const c
    have hg_nonneg : 0 ≤ᵐ[volume.restrict A] fun t => f t * c :=
      Filter.Eventually.of_forall fun t =>
        mul_nonneg
          (mul_nonneg (sobolevWeight_nonneg alpha (t + natVec k))
            (sq_nonneg _))
          (sq_nonneg _)
    have hg_meas :
        AEStronglyMeasurable (fun t => f t * c) (volume.restrict A) :=
      hg_int.aestronglyMeasurable
    simpa [f, c, mul_assoc] using
      (lintegral_ofReal_ne_top_iff_integrable hg_meas hg_nonneg).2 hg_int
  have hleft_ne_top :
      (∫⁻ xi, ENNReal.ofReal (‖ψ xi‖ ^ 2) ∂μ) ≠ ∞ := by
    rw [hlintegral]
    exact hright_ne_top
  have hsq_int :
      Integrable (fun xi => ‖ψ xi‖ ^ 2) μ := by
    have hsq_meas :
        AEStronglyMeasurable (fun xi => ‖ψ xi‖ ^ 2) μ :=
      hpsi_meas.norm.pow 2
    have hsq_nonneg : 0 ≤ᵐ[μ] fun xi => ‖ψ xi‖ ^ 2 :=
      Filter.Eventually.of_forall fun xi => sq_nonneg _
    exact
      (lintegral_ofReal_ne_top_iff_integrable hsq_meas hsq_nonneg).1
        hleft_ne_top
  have hmem : MemLp ψ 2 μ :=
    (memLp_two_iff_integrable_sq_norm hpsi_meas).2 hsq_int
  exact ⟨by simpa [ψ, μ] using hmem, by simpa [ψ, μ] using hlintegral⟩

theorem peak_weightedMemLp_and_lintegral_formula {d : ℕ} (_hd_pos : 0 < d)
    {A K : Set (E d)} {alpha : ℝ} {y : E d} {E0 : Finset (E d)}
    (hA : AContextHD d A) (halpha : AlphaLeDimHalf d alpha)
    (seed : PeakSeed A K y E0)
    (N : PosNat)
    (_C : PeakCandidate A K y E0 seed N.1
      (fun k => (c alpha N.1 k : ℂ))) :
    WeightedEnergyIntegrable alpha A
      (candidateP A seed N.1 (fun k => (c alpha N.1 k : ℂ))) ∧
    ∫⁻ xi,
        ENNReal.ofReal
          (‖candidateP A seed N.1
            (fun k => (c alpha N.1 k : ℂ)) xi‖ ^ 2)
        ∂(weightedMeasure alpha A)
      =
      (indexBox d N.1).sum
        (fun k =>
          ∫⁻ t,
            ENNReal.ofReal
              (sobolevWeight alpha (t + natVec k) *
                ‖seed.Phi t‖ ^ 2 *
                ‖(c alpha N.1 k : ℂ)‖ ^ 2)
            ∂(volume.restrict A)) := by
  classical
  let s : Finset (Fin d → ℕ) := indexBox d N.1
  let b : (Fin d → ℕ) → ℂ := fun k => (c alpha N.1 k : ℂ)
  let μ : Measure (E d) := weightedMeasure alpha A
  let F : (Fin d → ℕ) → E d → ℂ :=
    fun k xi =>
      exp2piI (-(inner ℝ y xi)) *
        (b k * PhiZeroExt A seed.Phi (xi - natVec k))
  let S : (Fin d → ℕ) → Set (E d) :=
    fun k => latticeTranslate A (fun i : Fin d => (k i : ℤ))
  have hbridge :
      ∀ k ∈ s,
        MemLp (F k) 2 μ ∧
        ∫⁻ xi, ENNReal.ofReal (‖F k xi‖ ^ 2) ∂μ =
          ∫⁻ t,
            ENNReal.ofReal
              (sobolevWeight alpha (t + natVec k) *
                ‖seed.Phi t‖ ^ 2 * ‖b k‖ ^ 2)
            ∂(volume.restrict A) := by
    intro k _hk
    simpa [F, b, μ] using
      shifted_phase_PhiZeroExt_weightedMemLp_and_lintegral
        (d := d) (A := A) (alpha := alpha) (y := y)
        hA halpha seed.Phi_memL2 k (b k)
  have hcandidate_eq :
      candidateP A seed N.1 b = fun xi => s.sum (fun k => F k xi) := by
    funext xi
    simp [candidateP, s, F, b, Finset.mul_sum, mul_assoc, mul_comm]
  have hweighted :
      WeightedEnergyIntegrable alpha A (candidateP A seed N.1 b) := by
    rw [hcandidate_eq]
    exact
      memLp_finsetSum (μ := μ) (p := (2 : ℝ≥0∞)) s
        (f := fun k xi => F k xi)
        (by
          intro k hk
          exact (hbridge k hk).1)
  have hF_meas : ∀ k ∈ s, AEStronglyMeasurable (F k) μ := by
    intro k hk
    exact (hbridge k hk).1.aestronglyMeasurable
  have hS_meas : ∀ k ∈ s, MeasurableSet (S k) := by
    intro k _hk
    exact measurableSet_latticeTranslate hA.measurable (fun i : Fin d => (k i : ℤ))
  have h_supp : ∀ k ∈ s, ∀ᵐ xi ∂μ, F k xi ≠ 0 → xi ∈ S k := by
    intro k _hk
    exact Filter.Eventually.of_forall fun xi hnonzero => by
      change xi - intVec (fun i : Fin d => (k i : ℤ)) ∈ A
      rw [← natVec_eq_intVec_natCast k]
      by_contra hnot
      have hzero : PhiZeroExt A seed.Phi (xi - natVec k) = 0 := by
        simp [PhiZeroExt, hnot]
      exact hnonzero (by simp [F, hzero])
  have hμ_ac : μ ≪ volume := by
    dsimp [μ]
    unfold weightedMeasure
    exact (withDensity_absolutelyContinuous _ _).trans Measure.absolutelyContinuous_restrict
  have h_disj :
      ∀ k ∈ s, ∀ l ∈ s, k ≠ l →
        μ (S k ∩ S l) = 0 := by
    intro k _hk l _hl hkl
    have hkl_int :
        (fun i : Fin d => (k i : ℤ)) ≠
          (fun i : Fin d => (l i : ℤ)) := by
      intro hcast
      apply hkl
      funext i
      exact Int.ofNat.inj (congrFun hcast i)
    exact hμ_ac
      (ae_disjoint_lattice_translates
        (A := A) hA.subset_unitCube hkl_int)
  refine ⟨hweighted, ?_⟩
  rw [hcandidate_eq]
  calc
    ∫⁻ xi,
        ENNReal.ofReal (‖s.sum (fun k => F k xi)‖ ^ 2) ∂μ
        =
        s.sum (fun k =>
          ∫⁻ xi, ENNReal.ofReal (‖F k xi‖ ^ 2) ∂μ) := by
          exact
            lintegral_norm_sq_finset_sum_of_ae_disjoint_support
              (μ := μ) (s := s) (S := S) (F := F)
              hF_meas hS_meas h_supp h_disj
    _ =
        s.sum
          (fun k =>
            ∫⁻ t,
              ENNReal.ofReal
                (sobolevWeight alpha (t + natVec k) *
                  ‖seed.Phi t‖ ^ 2 * ‖b k‖ ^ 2)
              ∂(volume.restrict A)) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          exact (hbridge k hk).2
    _ =
        (indexBox d N.1).sum
          (fun k =>
            ∫⁻ t,
              ENNReal.ofReal
                (sobolevWeight alpha (t + natVec k) *
                  ‖seed.Phi t‖ ^ 2 * ‖(c alpha N.1 k : ℂ)‖ ^ 2)
              ∂(volume.restrict A)) := by
          rfl

theorem peak_weightedEnergy_integrable_and_formula {d : ℕ} (hd_pos : 0 < d)
    {A K : Set (E d)} {alpha : ℝ} {y : E d} {E0 : Finset (E d)}
    (hA : AContextHD d A) (halpha : AlphaLeDimHalf d alpha)
    (seed : PeakSeed A K y E0)
    (N : PosNat)
    (C : PeakCandidate A K y E0 seed N.1
      (fun k => (c alpha N.1 k : ℂ))) :
    (∀ k ∈ indexBox d N.1,
      Integrable
        (fun t => sobolevWeight alpha (t + natVec k) * ‖seed.Phi t‖ ^ 2)
        (volume.restrict A)) ∧
    WeightedEnergyIntegrable alpha A
      (candidateP A seed N.1 (fun k => (c alpha N.1 k : ℂ))) ∧
    weightedEnergy alpha A
      (candidateP A seed N.1 (fun k => (c alpha N.1 k : ℂ))) =
      (indexBox d N.1).sum
        (fun k =>
          ‖(c alpha N.1 k : ℂ)‖ ^ 2 *
          ∫ t,
              sobolevWeight alpha (t + natVec k) *
                ‖seed.Phi t‖ ^ 2
            ∂(volume.restrict A)) := by
  classical
  rcases peak_weightedMemLp_and_lintegral_formula
      (d := d) hd_pos hA halpha seed N C with
    ⟨hweighted, hlintegral_formula⟩
  rcases exists_translateWeightConstant
      (d := d) hd_pos halpha with
    ⟨Cdim, hCdim_pos, hCdim⟩
  have hsq_int :
      Integrable (fun t => ‖seed.Phi t‖ ^ 2) (volume.restrict A) :=
    seed.Phi_memL2.integrable_norm_pow (by norm_num)
  have hterm_int :
      ∀ k ∈ indexBox d N.1,
        Integrable
          (fun t => sobolevWeight alpha (t + natVec k) * ‖seed.Phi t‖ ^ 2)
          (volume.restrict A) := by
    intro k hk
    have hk_one : ∀ i : Fin d, 1 ≤ k i := by
      intro i
      exact ((indexBox_mem_iff (d := d) (N := N.1) k).1 hk i).1
    let M : ℝ := Cdim * sobolevWeight alpha (natVec k)
    refine (hsq_int.const_mul M).mono_nonneg ?_ ?_ ?_
    · exact
        (aestronglyMeasurable_sobolevWeight_add_natVec
          (d := d) halpha.nonneg k (volume.restrict A)).mul
          (seed.Phi_memL2.aestronglyMeasurable.norm.pow 2)
    · exact Filter.Eventually.of_forall fun t =>
        mul_nonneg (sobolevWeight_nonneg alpha (t + natVec k)) (sq_nonneg _)
    · filter_upwards [ae_restrict_mem hA.measurable] with t htA
      have hw :
          sobolevWeight alpha (t + natVec k)
            ≤ Cdim * sobolevWeight alpha (natVec k) :=
        hCdim t (hA.subset_unitCube htA) k hk_one
      exact mul_le_mul_of_nonneg_right hw (sq_nonneg _)
  refine ⟨hterm_int, hweighted, ?_⟩
  rw [weightedEnergy_eq_lintegral_norm_sq_toReal hweighted]
  rw [hlintegral_formula]
  have hterm_ne_top :
      ∀ k ∈ indexBox d N.1,
        (∫⁻ t,
            ENNReal.ofReal
              (sobolevWeight alpha (t + natVec k) *
                ‖seed.Phi t‖ ^ 2 *
                ‖(c alpha N.1 k : ℂ)‖ ^ 2)
            ∂(volume.restrict A)) ≠ ∞ := by
    intro k hk
    let f : E d → ℝ :=
      fun t => sobolevWeight alpha (t + natVec k) * ‖seed.Phi t‖ ^ 2
    let b : ℝ := ‖(c alpha N.1 k : ℂ)‖ ^ 2
    have hf_int : Integrable f (volume.restrict A) := hterm_int k hk
    have hg_int :
        Integrable (fun t => f t * b) (volume.restrict A) :=
      hf_int.mul_const b
    have hg_nonneg : 0 ≤ᵐ[volume.restrict A] fun t => f t * b :=
      Filter.Eventually.of_forall fun t =>
        mul_nonneg
          (mul_nonneg (sobolevWeight_nonneg alpha (t + natVec k)) (sq_nonneg _))
          (sq_nonneg _)
    have hg_meas : AEStronglyMeasurable (fun t => f t * b) (volume.restrict A) :=
      hg_int.aestronglyMeasurable
    simpa [f, b, mul_assoc] using
      (lintegral_ofReal_ne_top_iff_integrable hg_meas hg_nonneg).2 hg_int
  rw [ENNReal.toReal_sum hterm_ne_top]
  refine Finset.sum_congr rfl ?_
  intro k hk
  let f : E d → ℝ :=
    fun t => sobolevWeight alpha (t + natVec k) * ‖seed.Phi t‖ ^ 2
  let b : ℝ := ‖(c alpha N.1 k : ℂ)‖ ^ 2
  have hf_int : Integrable f (volume.restrict A) := hterm_int k hk
  have hg_int :
      Integrable (fun t => f t * b) (volume.restrict A) :=
    hf_int.mul_const b
  have hg_nonneg : 0 ≤ᵐ[volume.restrict A] fun t => f t * b :=
    Filter.Eventually.of_forall fun t =>
      mul_nonneg
        (mul_nonneg (sobolevWeight_nonneg alpha (t + natVec k)) (sq_nonneg _))
        (sq_nonneg _)
  have hg_integral_nonneg : 0 ≤ ∫ t, f t * b ∂(volume.restrict A) :=
    integral_nonneg fun t =>
      mul_nonneg
        (mul_nonneg (sobolevWeight_nonneg alpha (t + natVec k)) (sq_nonneg _))
        (sq_nonneg _)
  calc
    (∫⁻ t,
        ENNReal.ofReal
          (sobolevWeight alpha (t + natVec k) *
            ‖seed.Phi t‖ ^ 2 *
            ‖(c alpha N.1 k : ℂ)‖ ^ 2)
        ∂(volume.restrict A)).toReal
        =
        (ENNReal.ofReal (∫ t, f t * b ∂(volume.restrict A))).toReal := by
          rw [ofReal_integral_eq_lintegral_ofReal hg_int hg_nonneg]
    _ = ∫ t, f t * b ∂(volume.restrict A) := by
          exact ENNReal.toReal_ofReal hg_integral_nonneg
    _ = (∫ t, f t ∂(volume.restrict A)) * b := by
          rw [integral_mul_const]
    _ =
        ‖(c alpha N.1 k : ℂ)‖ ^ 2 *
          ∫ t,
              sobolevWeight alpha (t + natVec k) *
                ‖seed.Phi t‖ ^ 2
            ∂(volume.restrict A) := by
          simp [f, b, mul_comm]

theorem exists_peak_weightedEnergy_constant {d : ℕ} (hd_pos : 0 < d)
    {A K : Set (E d)} {alpha : ℝ} {y : E d} {E0 : Finset (E d)}
    (hA : AContextHD d A) (halpha : AlphaLeDimHalf d alpha)
    (seed : PeakSeed A K y E0) :
    ∃ Cdim : ℝ,
      0 < Cdim ∧
      ∀ N : PosNat,
      ∀ _C : PeakCandidate A K y E0 seed N.1
        (fun k => (c alpha N.1 k : ℂ)),
      weightedEnergy alpha A
        (candidateP A seed N.1 (fun k => (c alpha N.1 k : ℂ)))
        ≤
        Cdim *
        (∫ t, ‖seed.Phi t‖ ^ 2 ∂(volume.restrict A)) *
        (indexBox d N.1).sum
          (fun k =>
            sobolevWeight alpha (natVec k) * (c alpha N.1 k)^2) := by
  classical
  rcases exists_translateWeightConstant
      (d := d) hd_pos halpha with
    ⟨Cdim, hCdim_pos, hCdim⟩
  refine ⟨Cdim, hCdim_pos, ?_⟩
  intro N C
  rcases peak_weightedEnergy_integrable_and_formula
      (d := d) hd_pos hA halpha seed N C with
    ⟨hterm_int, _hweighted_int, hformula⟩
  let I : ℝ := ∫ t, ‖seed.Phi t‖ ^ 2 ∂(volume.restrict A)
  have hsq_int :
      Integrable (fun t => ‖seed.Phi t‖ ^ 2) (volume.restrict A) :=
    seed.Phi_memL2.integrable_norm_pow (by norm_num)
  rw [hformula]
  calc
    (indexBox d N.1).sum
        (fun k =>
          ‖(c alpha N.1 k : ℂ)‖ ^ 2 *
          ∫ t,
              sobolevWeight alpha (t + natVec k) *
                ‖seed.Phi t‖ ^ 2
            ∂(volume.restrict A))
        ≤
        (indexBox d N.1).sum
          (fun k =>
            Cdim * I *
              (sobolevWeight alpha (natVec k) *
                (c alpha N.1 k)^2)) := by
          refine Finset.sum_le_sum ?_
          intro k hk
          have hk_one : ∀ i : Fin d, 1 ≤ k i := by
            intro i
            exact ((indexBox_mem_iff (d := d) (N := N.1) k).1 hk i).1
          have hintegral_le :
              (∫ t,
                  sobolevWeight alpha (t + natVec k) *
                    ‖seed.Phi t‖ ^ 2
                  ∂(volume.restrict A))
                ≤
                Cdim * sobolevWeight alpha (natVec k) * I := by
            have hright_int :
                Integrable
                  (fun t =>
                    (Cdim * sobolevWeight alpha (natVec k)) *
                      ‖seed.Phi t‖ ^ 2)
                  (volume.restrict A) :=
              hsq_int.const_mul _
            calc
              (∫ t,
                  sobolevWeight alpha (t + natVec k) *
                    ‖seed.Phi t‖ ^ 2
                  ∂(volume.restrict A))
                  ≤
                  ∫ t,
                    (Cdim * sobolevWeight alpha (natVec k)) *
                      ‖seed.Phi t‖ ^ 2
                    ∂(volume.restrict A) := by
                    refine integral_mono_ae (hterm_int k hk) hright_int ?_
                    filter_upwards [ae_restrict_mem hA.measurable] with t htA
                    have hw :
                        sobolevWeight alpha (t + natVec k)
                          ≤ Cdim * sobolevWeight alpha (natVec k) :=
                      hCdim t (hA.subset_unitCube htA) k hk_one
                    exact mul_le_mul_of_nonneg_right hw (sq_nonneg _)
              _ =
                  Cdim * sobolevWeight alpha (natVec k) * I := by
                    rw [integral_const_mul]
          have hcoef_nonneg : 0 ≤ ‖(c alpha N.1 k : ℂ)‖ ^ 2 := sq_nonneg _
          have hnorm_c :
              ‖(c alpha N.1 k : ℂ)‖ = c alpha N.1 k := by
            rw [← Real.norm_of_nonneg (c_nonneg halpha k)]
            norm_num
          calc
            ‖(c alpha N.1 k : ℂ)‖ ^ 2 *
                (∫ t,
                  sobolevWeight alpha (t + natVec k) *
                    ‖seed.Phi t‖ ^ 2
                  ∂(volume.restrict A))
                ≤
                ‖(c alpha N.1 k : ℂ)‖ ^ 2 *
                  (Cdim * sobolevWeight alpha (natVec k) * I) := by
                  exact mul_le_mul_of_nonneg_left hintegral_le hcoef_nonneg
            _ =
                Cdim * I *
                  (sobolevWeight alpha (natVec k) *
                    (c alpha N.1 k)^2) := by
                  rw [hnorm_c]
                  ring
    _ =
        Cdim * I *
          (indexBox d N.1).sum
            (fun k =>
              sobolevWeight alpha (natVec k) * (c alpha N.1 k)^2) := by
          rw [← Finset.mul_sum]

theorem exists_peak_weightedEnergy_control {d : ℕ} (hd_pos : 0 < d)
    {A K : Set (E d)} {alpha : ℝ} {y : E d} {E0 : Finset (E d)}
    (hA : AContextHD d A) (halpha : AlphaLeDimHalf d alpha)
    (seed : PeakSeed A K y E0) :
    ∃ Cdim EPhi : ℝ,
      0 < Cdim ∧
      0 ≤ EPhi ∧
      EPhi = ∫ t, ‖seed.Phi t‖ ^ 2 ∂(volume.restrict A) ∧
      ∀ N : PosNat,
      ∀ _C : PeakCandidate A K y E0 seed N.1
        (fun k => (c alpha N.1 k : ℂ)),
        WeightedEnergyIntegrable alpha A
          (candidateP A seed N.1 (fun k => (c alpha N.1 k : ℂ))) ∧
        weightedEnergy alpha A
          (candidateP A seed N.1 (fun k => (c alpha N.1 k : ℂ)))
          ≤ Cdim * EPhi *
            (indexBox d N.1).sum
              (fun k =>
                sobolevWeight alpha (natVec k) * (c alpha N.1 k)^2) := by
  rcases exists_peak_weightedEnergy_constant
      (d := d) hd_pos hA halpha seed with
    ⟨Cdim, hCdim_pos, hCdim_bound⟩
  let EPhi : ℝ := ∫ t, ‖seed.Phi t‖ ^ 2 ∂(volume.restrict A)
  have hEPhi_nonneg : 0 ≤ EPhi := by
    dsimp [EPhi]
    exact integral_nonneg fun t => sq_nonneg (‖seed.Phi t‖)
  refine ⟨Cdim, EPhi, hCdim_pos, hEPhi_nonneg, rfl, ?_⟩
  intro N C
  refine ⟨?_, ?_⟩
  · exact (peak_weightedMemLp_and_lintegral_formula
      (d := d) hd_pos hA halpha seed N C).1
  · exact hCdim_bound N C

theorem peak_weightedEnergy_integrable {d : ℕ} (hd_pos : 0 < d)
    {A K : Set (E d)} {alpha : ℝ} {y : E d} {E0 : Finset (E d)}
    (hA : AContextHD d A) (halpha : AlphaLeDimHalf d alpha)
    (seed : PeakSeed A K y E0)
    (N : PosNat)
    (C : PeakCandidate A K y E0 seed N.1
      (fun k => (c alpha N.1 k : ℂ))) :
    WeightedEnergyIntegrable alpha A
      (candidateP A seed N.1 (fun k => (c alpha N.1 k : ℂ))) := by
  exact (peak_weightedMemLp_and_lintegral_formula
    (d := d) hd_pos hA halpha seed N C).1

theorem peak_weightedNorm_tendsto_zero {d : ℕ} (hd_pos : 0 < d)
    {A K : Set (E d)} {alpha : ℝ} {y : E d} {E0 : Finset (E d)}
    (hA : AContextHD d A) (halpha : AlphaLeDimHalf d alpha)
    (seed : PeakSeed A K y E0)
    (F : ∀ N : PosNat,
      PeakCandidate A K y E0 seed N.1
        (fun k => (c alpha N.1 k : ℂ))) :
    Tendsto
      (fun n =>
        weightedNorm alpha A
          (candidateP A seed (n + 1)
            (fun k => (c alpha (n + 1) k : ℂ))))
      atTop (nhds 0) := by
  rcases exists_peak_weightedEnergy_control
      (d := d) hd_pos hA halpha seed with
    ⟨Cdim, EPhi, hCdim_pos, hEPhi_nonneg, hEPhi_eq, hcontrol⟩
  have hcoeff :
      Tendsto
        (fun n : ℕ =>
          (indexBox d (n + 1)).sum
            (fun k =>
              sobolevWeight alpha (natVec k) *
                (c alpha (n + 1) k)^2))
        atTop (nhds 0) :=
    (weighted_coeff_energy_tendsto_zero (d := d) hd_pos halpha).comp
      (tendsto_add_atTop_nat 1)
  have hupper_tendsto :
      Tendsto
        (fun n : ℕ =>
          Cdim * EPhi *
            (indexBox d (n + 1)).sum
              (fun k =>
                sobolevWeight alpha (natVec k) *
                  (c alpha (n + 1) k)^2))
        atTop (nhds 0) := by
    simpa using hcoeff.const_mul (Cdim * EPhi)
  have henergy_tendsto :
      Tendsto
        (fun n : ℕ =>
          weightedEnergy alpha A
            (candidateP A seed (n + 1)
              (fun k => (c alpha (n + 1) k : ℂ))))
        atTop (nhds 0) := by
    refine squeeze_zero (fun n => ?_) (fun n => ?_) hupper_tendsto
    · unfold weightedEnergy
      exact sq_nonneg _
    · exact (hcontrol
        ⟨n + 1, Nat.succ_le_succ (Nat.zero_le n)⟩
        (F ⟨n + 1, Nat.succ_le_succ (Nat.zero_le n)⟩)).2
  simpa [weightedNorm, weightedEnergy] using henergy_tendsto.sqrt

theorem finite_lattice_obstructions_on_compact {d : ℕ}
    {K : Set (E d)} {y : E d}
    (hK : IsCompact K) :
    (((fun x : E d => x - y) '' K) ∩ integerLattice d).Finite := by
  classical
  refine (latticeObstructionSet_finite (d := d) (K := K) (y := y) hK).subset ?_
  intro u hu
  rcases hu with ⟨⟨x, hxK, rfl⟩, hu_lattice⟩
  exact ⟨hu_lattice, by simpa [sub_eq_add_neg, add_assoc]⟩

theorem exists_open_neighborhood_finite_zeros {d : ℕ}
    {D : Set (E d)} {phi : E d → ℂ}
    (_hD_fin : D.Finite)
    (hphi_cont : Continuous phi)
    (hzero : ∀ z ∈ D, phi z = 0)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ U : Set (E d), IsOpen U ∧ D ⊆ U ∧
      ∀ u ∈ U, ‖phi u‖ < eps := by
  refine ⟨{u | ‖phi u‖ < eps}, ?_, ?_, ?_⟩
  · exact hphi_cont.norm.isOpen_preimage _ isOpen_Iio
  · intro z hz
    simp [hzero z hz, heps]
  · intro u hu
    exact hu

theorem PeakSeed.phi_vanish_latticeObstructionSet {d : ℕ}
    {A K : Set (E d)} {y : E d} {E0 : Finset (E d)}
    (seed : PeakSeed A K y E0) :
    ∀ u ∈ latticeObstructionSet K y, seed.phi u = 0 := by
  intro u hu
  rcases hu.1 with ⟨z, rfl⟩
  exact seed.phi_vanish_K_lattice z hu.2

theorem PeakSeed.phi_vanish_latticeObstruction_image {d : ℕ}
    {A K : Set (E d)} {y : E d} {E0 : Finset (E d)}
    (seed : PeakSeed A K y E0) :
    ∀ u ∈ ((fun x : E d => x - y) '' K) ∩ integerLattice d,
      seed.phi u = 0 := by
  intro u hu
  rcases hu.1 with ⟨x, hxK, rfl⟩
  rcases hu.2 with ⟨z, hz⟩
  have hzK : intVec z + y ∈ K := by
    rw [hz]
    simpa [sub_eq_add_neg, add_assoc] using hxK
  rw [← hz]
  exact seed.phi_vanish_K_lattice z hzK

theorem exists_open_neighborhood_finite_zeros_on_compact_image {d : ℕ}
    {D D_K : Set (E d)} {phi : E d → ℂ}
    (hD_fin : D.Finite)
    (_hD_sub : D ⊆ D_K)
    (hphi_cont : Continuous phi)
    (hzero : ∀ z ∈ D, phi z = 0)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ U : Set (E d), IsOpen U ∧ D ⊆ U ∧
      ∀ u ∈ D_K ∩ U, ‖phi u‖ < eps := by
  rcases exists_open_neighborhood_finite_zeros
      (d := d) hD_fin hphi_cont hzero heps with
    ⟨U, hU_open, hD_U, hsmall⟩
  exact ⟨U, hU_open, hD_U, fun u hu => hsmall u hu.2⟩

theorem compact_complement_away_from_lattice {d : ℕ}
    {D_K U : Set (E d)}
    (hDK : IsCompact D_K) (hU : IsOpen U)
    (hcover : D_K ∩ integerLattice d ⊆ U) :
    IsCompact (D_K \ U) ∧
      ∀ u ∈ D_K \ U, u ∉ integerLattice d := by
  refine ⟨hDK.diff hU, ?_⟩
  intro u hu hu_lattice
  exact hu.2 (hcover ⟨hu.1, hu_lattice⟩)

theorem bounded_on_compact_image {d : ℕ}
    {D_K : Set (E d)} {phi : E d → ℂ}
    (hDK : IsCompact D_K) (hphi_cont : Continuous phi) :
    ∃ Mphi : ℝ, 0 ≤ Mphi ∧ ∀ u ∈ D_K, ‖phi u‖ ≤ Mphi := by
  classical
  rcases bddAbove_def.mp
      (hDK.bddAbove_image (hphi_cont.norm.continuousOn)) with
    ⟨C, hC⟩
  refine ⟨max 0 C, le_max_left 0 C, ?_⟩
  intro u hu
  exact (hC (‖phi u‖) ⟨u, hu, rfl⟩).trans (le_max_right 0 C)

theorem product_small_on_neighborhood_union_complement {d : ℕ}
    {D_K U : Set (E d)} {phi QN : E d → ℂ}
    {eps Mphi etaQ : ℝ}
    (heps : 0 < eps)
    (_hMphi : 0 ≤ Mphi)
    (hetaQ : etaQ = eps / (2 * max Mphi 1))
    (hphi_U : ∀ u ∈ D_K ∩ U, ‖phi u‖ < eps / 2)
    (hphi_bd : ∀ u ∈ D_K, ‖phi u‖ ≤ Mphi)
    (hQ_one : ∀ u, ‖QN u‖ ≤ 1)
    (hQ_small : ∀ u ∈ D_K \ U, ‖QN u‖ < etaQ) :
    ∀ u ∈ D_K, ‖phi u * QN u‖ < eps := by
  intro u huDK
  by_cases huU : u ∈ U
  · have hphi : ‖phi u‖ < eps / 2 := hphi_U u ⟨huDK, huU⟩
    calc
      ‖phi u * QN u‖
          = ‖phi u‖ * ‖QN u‖ := norm_mul _ _
      _ ≤ ‖phi u‖ * 1 :=
          mul_le_mul_of_nonneg_left (hQ_one u) (norm_nonneg _)
      _ < eps := by linarith
  · let M : ℝ := max Mphi 1
    have hM_pos : 0 < M := by
      dsimp [M]
      exact lt_of_lt_of_le zero_lt_one (le_max_right Mphi 1)
    have hQ : ‖QN u‖ < eps / (2 * M) := by
      simpa [M, hetaQ] using hQ_small u ⟨huDK, huU⟩
    have hphi_le_M : ‖phi u‖ ≤ M :=
      (hphi_bd u huDK).trans (by dsimp [M]; exact le_max_left Mphi 1)
    have hM_mul_lt : M * ‖QN u‖ < eps / 2 := by
      have hlt := mul_lt_mul_of_pos_left hQ hM_pos
      have hcalc : M * (eps / (2 * M)) = eps / 2 := by
        field_simp [hM_pos.ne']
      simpa [hcalc] using hlt
    calc
      ‖phi u * QN u‖
          = ‖phi u‖ * ‖QN u‖ := norm_mul _ _
      _ ≤ M * ‖QN u‖ :=
          mul_le_mul_of_nonneg_right hphi_le_M (norm_nonneg _)
      _ < eps := by linarith

theorem peak_eventually_small_on_construction_compact {d : ℕ} (hd_pos : 0 < d)
    {A K : Set (E d)} {alpha : ℝ} {y : E d} {E0 : Finset (E d)}
    (halpha : AlphaLeDimHalf d alpha)
    (seed : PeakSeed A K y E0)
    (_F : ∀ N : PosNat,
      PeakCandidate A K y E0 seed N.1
        (fun k => (c alpha N.1 k : ℂ))) :
    ∀ eps > 0,
      ∀ᶠ N in atTop,
        ∀ x ∈ K,
          ‖candidatep seed (N + 1)
            (fun k => (c alpha (N + 1) k : ℂ)) x‖ < eps := by
  intro eps heps
  let D_K : Set (E d) := (fun x : E d => x - y) '' K
  have hDK : IsCompact D_K :=
    seed.hK.image (continuous_id.sub continuous_const)
  have hD_fin : (D_K ∩ integerLattice d).Finite :=
    finite_lattice_obstructions_on_compact (d := d) (K := K) (y := y) seed.hK
  have hzero : ∀ z ∈ D_K ∩ integerLattice d, seed.phi z = 0 :=
    seed.phi_vanish_latticeObstruction_image
  have heps_half : 0 < eps / 2 := by linarith
  rcases exists_open_neighborhood_finite_zeros
      (d := d) hD_fin seed.phi_cont hzero heps_half with
    ⟨U, hU_open, hD_U, hphi_U_all⟩
  rcases compact_complement_away_from_lattice
      (d := d) hDK hU_open hD_U with
    ⟨hcompact_away, haway_lattice⟩
  rcases bounded_on_compact_image hDK seed.phi_cont with
    ⟨Mphi, hMphi, hphi_bd⟩
  let etaQ : ℝ := eps / (2 * max Mphi 1)
  have hetaQ_pos : 0 < etaQ := by
    have hmax_pos : 0 < max Mphi 1 :=
      lt_of_lt_of_le zero_lt_one (le_max_right Mphi 1)
    dsimp [etaQ]
    positivity
  have hsmallQ :
      ∀ᶠ N in atTop,
        ∀ u ∈ D_K \ U, ‖Q (d := d) alpha N u‖ < etaQ :=
    Q_eventually_small_uniformOn_compact_away_lattice
      hd_pos halpha hcompact_away haway_lattice etaQ hetaQ_pos
  have hsmallQ_shift :
      ∀ᶠ N in atTop,
        ∀ u ∈ D_K \ U, ‖Q (d := d) alpha (N + 1) u‖ < etaQ :=
    (tendsto_add_atTop_nat 1).eventually hsmallQ
  filter_upwards [hsmallQ_shift] with N hQN x hxK
  have hprod :
      ∀ u ∈ D_K,
        ‖seed.phi u * Q (d := d) alpha (N + 1) u‖ < eps := by
    refine product_small_on_neighborhood_union_complement
      (d := d) (D_K := D_K) (U := U)
      (phi := seed.phi) (QN := Q (d := d) alpha (N + 1))
      (eps := eps) (Mphi := Mphi) (etaQ := etaQ)
      heps hMphi rfl ?_ hphi_bd ?_ hQN
    · intro u hu
      exact hphi_U_all u hu.2
    · intro u
      exact Q_norm_le_one halpha (Nat.succ_le_succ (Nat.zero_le N)) u
  have hxDK : x - y ∈ D_K := ⟨x, hxK, rfl⟩
  simpa [candidatep, Q] using hprod (x - y) hxDK

theorem exists_small_peak_with_finite_zeros {d : ℕ} (hd_pos : 0 < d)
    {A K : Set (E d)} {alpha eps : ℝ} {y : E d}
    {E0 : Finset (E d)}
    (hA : AContextHD d A)
    (halpha : AlphaLeDimHalf d alpha)
    (hK : IsCompact K)
    (hyK : y ∉ K)
    (hE : ∀ e ∈ E0, e ≠ y)
    (heps : 0 < eps) :
    ∃ p P : E d → ℂ,
      WeightedFourierWitness alpha A p P ∧
      Continuous p ∧
      p y = 1 ∧
      (∀ e ∈ E0, p e = 0) ∧
      (∀ x ∈ K, ‖p x‖ < eps) ∧
      weightedNorm alpha A P < eps := by
  classical
  rcases exists_peak_seed (d := d) hd_pos hA hK hyK hE with ⟨seed, _⟩
  let F : ∀ N : PosNat,
      PeakCandidate A K y E0 seed N.1
        (fun k => (c alpha N.1 k : ℂ)) :=
    fun N =>
      Classical.choose
        (exists_peak_candidate (d := d) hd_pos hA seed
          (N := N.1) N.2
          (b := fun k => (c alpha N.1 k : ℂ))
          (sum_c_complex_eq_one halpha N.2))
  have hsmallK :
      ∀ᶠ N in atTop,
        ∀ x ∈ K,
          ‖candidatep seed (N + 1)
            (fun k => (c alpha (N + 1) k : ℂ)) x‖ < eps :=
    peak_eventually_small_on_construction_compact
      (d := d) hd_pos halpha seed F eps heps
  have hsmallNorm :
      ∀ᶠ N in atTop,
        weightedNorm alpha A
          (candidateP A seed (N + 1)
            (fun k => (c alpha (N + 1) k : ℂ))) < eps :=
    (peak_weightedNorm_tendsto_zero
      (d := d) hd_pos hA halpha seed F).eventually (gt_mem_nhds heps)
  rcases eventually_atTop.1 (hsmallK.and hsmallNorm) with ⟨N, hN⟩
  let Npos : PosNat := ⟨N + 1, Nat.succ_le_succ (Nat.zero_le N)⟩
  let C : PeakCandidate A K y E0 seed Npos.1
      (fun k => (c alpha Npos.1 k : ℂ)) := F Npos
  rcases hN N (le_refl N) with ⟨hKsmall, hNormsmall⟩
  change
    ∀ x ∈ K,
      ‖candidatep seed Npos.1
        (fun k => (c alpha Npos.1 k : ℂ)) x‖ < eps at hKsmall
  change
    weightedNorm alpha A
      (candidateP A seed Npos.1
        (fun k => (c alpha Npos.1 k : ℂ))) < eps at hNormsmall
  refine ⟨candidatep seed Npos.1 (fun k => (c alpha Npos.1 k : ℂ)),
    candidateP A seed Npos.1 (fun k => (c alpha Npos.1 k : ℂ)),
    ?_, C.p_cont, C.p_y, C.p_zero_E, hKsmall, hNormsmall⟩
  exact PeakCandidate.toWeightedFourierWitness (d := d) hd_pos hA C
    (peak_weightedEnergy_integrable (d := d) hd_pos hA halpha seed Npos C)

end SpectralGapsPrelim.HigherDim
