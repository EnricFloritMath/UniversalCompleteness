import PeriodicWeakGapsHD.HigherDim.FiniteMomentInterpolation
import PeriodicWeakGapsHD.HigherDim.PositiveBoxPolynomials

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Topology ENNReal FourierTransform

namespace SpectralGapsPrelim.HigherDim

/-!
Peak candidates from one fixed fibre seed and arbitrary finite coefficients.
-/

private lemma exp2piI_add (u v : ℝ) :
    exp2piI (u + v) = exp2piI u * exp2piI v := by
  unfold exp2piI
  rw [← Complex.exp_add]
  congr 1
  apply Complex.ext
  · simp
  · simp
    ring

private lemma norm_exp2piI (u : ℝ) :
    ‖exp2piI u‖ = 1 := by
  simp [exp2piI, Complex.norm_exp]

private lemma continuous_exp2piI :
    Continuous exp2piI := by
  unfold exp2piI
  fun_prop

private lemma PhiZeroExt_eq_of_mem {d : ℕ}
    {A : Set (E d)} {Phi : E d → ℂ} {t : E d}
    (ht : t ∈ A) :
    PhiZeroExt A Phi t = Phi t := by
  simp [PhiZeroExt, ht]

private lemma PhiZeroExt_eq_zero_of_not_mem {d : ℕ}
    {A : Set (E d)} {Phi : E d → ℂ} {t : E d}
    (ht : t ∉ A) :
    PhiZeroExt A Phi t = 0 := by
  simp [PhiZeroExt, ht]

private lemma exp2piI_inner_sub {d : ℕ} (xi x y : E d) :
    exp2piI (inner ℝ xi x) * exp2piI (-(inner ℝ y xi)) =
      exp2piI (inner ℝ xi (x - y)) := by
  rw [← exp2piI_add]
  congr 1
  rw [inner_sub_right, real_inner_comm y xi]
  ring

private lemma continuous_coeffPolynomial {d N : ℕ}
    (b : (Fin d → ℕ) → ℂ) :
    Continuous (coeffPolynomial N b) := by
  unfold coeffPolynomial
  exact continuous_finsetSum (indexBox d N) (by
    intro k _hk
    exact continuous_const.mul
      (continuous_exp2piI.comp (by fun_prop)))

private lemma continuous_fiber_fourierMoment {d : ℕ}
    {A : Set (E d)} {Phi : E d → ℂ}
    (hPhi : Integrable Phi (volume.restrict A)) :
    Continuous
      (fun u : E d =>
        ∫ t, Phi t * exp2piI (inner ℝ t u) ∂volume.restrict A) := by
  let L : E d →ₗ[ℝ] E d →ₗ[ℝ] ℝ := -(innerₗ (E d))
  have hL :
      Continuous fun p : E d × E d => L p.1 p.2 := by
    simpa [L] using
      (continuous_inner.neg :
        Continuous fun p : E d × E d => -inner ℝ p.1 p.2)
  have hcont :
      Continuous
        (VectorFourier.fourierIntegral Real.fourierChar
          (volume.restrict A) L Phi) := by
    exact
      VectorFourier.fourierIntegral_continuous
        Real.continuous_fourierChar hL hPhi
  convert hcont using 1
  ext u
  simp [VectorFourier.fourierIntegral, L, exp2piI, Circle.smul_def,
    Real.fourierChar_apply, mul_comm, mul_assoc]

private lemma integral_exp_translate_PhiZeroExt {d : ℕ}
    {A : Set (E d)} (hA : MeasurableSet A) (Phi : E d → ℂ)
    (u a : E d) :
    (∫ xi : E d,
        exp2piI (inner ℝ xi u) * PhiZeroExt A Phi (xi - a)) =
      exp2piI (inner ℝ a u) *
        ∫ t : E d, Phi t * exp2piI (inner ℝ t u) ∂volume.restrict A := by
  let F : E d → ℂ :=
    fun xi => exp2piI (inner ℝ xi u) * PhiZeroExt A Phi (xi - a)
  calc
    (∫ xi : E d, exp2piI (inner ℝ xi u) *
        PhiZeroExt A Phi (xi - a)) =
        ∫ xi : E d, F xi := rfl
    _ = ∫ xi : E d, F (xi + a) := by
      exact (integral_add_right_eq_self F a).symm
    _ = ∫ xi : E d, exp2piI (inner ℝ (xi + a) u) *
          PhiZeroExt A Phi xi := by
      congr 1
      ext xi
      simp [F]
    _ = ∫ xi : E d, exp2piI (inner ℝ a u) *
          (PhiZeroExt A Phi xi * exp2piI (inner ℝ xi u)) := by
      apply integral_congr_ae
      filter_upwards with xi
      rw [show exp2piI (inner ℝ (xi + a) u) =
          exp2piI (inner ℝ xi u) * exp2piI (inner ℝ a u) by
        rw [← exp2piI_add]
        congr 1
        rw [inner_add_left]]
      ring
    _ = exp2piI (inner ℝ a u) *
        ∫ xi : E d, PhiZeroExt A Phi xi *
          exp2piI (inner ℝ xi u) := by
      rw [integral_const_mul]
    _ = exp2piI (inner ℝ a u) *
        ∫ t : E d, Phi t * exp2piI (inner ℝ t u) ∂volume.restrict A := by
      congr 1
      have hindicator :
          (fun xi : E d => PhiZeroExt A Phi xi *
              exp2piI (inner ℝ xi u)) =
            Set.indicator A
              (fun xi : E d => Phi xi * exp2piI (inner ℝ xi u)) := by
        ext xi
        by_cases hxi : xi ∈ A
        · simp [PhiZeroExt_eq_of_mem hxi, hxi]
        · simp [PhiZeroExt_eq_zero_of_not_mem hxi, hxi]
      rw [hindicator, integral_indicator hA]

theorem exists_peak_seed {d : ℕ} (hd_pos : 0 < d)
    {A K : Set (E d)} {y : E d} {E0 : Finset (E d)}
    (hA : AContextHD d A)
    (hK : IsCompact K)
    (hyK : y ∉ K)
    (hE : ∀ e ∈ E0, e ≠ y) :
    ∃ _seed : PeakSeed A K y E0, True := by
  classical
  let Dset : Set (E d) :=
    ((fun e : E d => e - y) '' (E0 : Set (E d))) ∪
      latticeObstructionSet K y
  have hDset_finite : Dset.Finite := by
    exact
      (E0.finite_toSet.image (fun e : E d => e - y)).union
        (latticeObstructionSet_finite hK)
  let D : Finset (E d) := hDset_finite.toFinset
  have hD_mem :
      ∀ h : E d,
        h ∈ D ↔
          h ∈ ((fun e : E d => e - y) '' (E0 : Set (E d))) ∪
            latticeObstructionSet K y := by
    intro h
    change h ∈ hDset_finite.toFinset ↔ h ∈ Dset
    exact finite_toFinset_mem hDset_finite h
  have hD_zero_not_mem : 0 ∉ D := by
    intro h0
    have h0' := (hD_mem 0).mp h0
    rcases h0' with h0E | h0K
    · rcases h0E with ⟨e, heE, heq⟩
      exact hE e heE (sub_eq_zero.mp heq)
    · exact zero_not_mem_latticeObstructionSet hyK h0K
  have hD_zero : ∀ h ∈ D, h ≠ 0 := by
    intro h hh hzero
    exact hD_zero_not_mem (hzero ▸ hh)
  obtain ⟨Phi, hPhi_meas, hPhi_L2, hPhi_int, hPhi_one, hPhi_zero⟩ :=
    exists_fiber_moment_interpolant_of_AContextHD hd_pos hA hD_zero
  let phi : E d → ℂ :=
    fun u => ∫ t, Phi t * exp2piI (inner ℝ t u) ∂volume.restrict A
  have hphi_zero : phi 0 = 1 := by
    simpa [phi, exp2piI] using hPhi_one
  have hphi_vanish_E : ∀ e ∈ E0, phi (e - y) = 0 := by
    intro e heE
    have hd : e - y ∈ D := by
      exact (hD_mem (e - y)).mpr (Or.inl ⟨e, by simpa using heE, rfl⟩)
    have hz := hPhi_zero (e - y) hd
    simpa [phi, real_inner_comm] using hz
  have hphi_vanish_K_lattice :
      ∀ z : Fin d → ℤ, intVec z + y ∈ K → phi (intVec z) = 0 := by
    intro z hzK
    have hd : intVec z ∈ D := by
      exact (hD_mem (intVec z)).mpr
        (Or.inr ⟨⟨z, rfl⟩, hzK⟩)
    have hz := hPhi_zero (intVec z) hd
    simpa [phi, real_inner_comm] using hz
  exact
    ⟨{
      hK := hK
      hyK := hyK
      hE := hE
      D := D
      D_mem := hD_mem
      D_zero_not_mem := hD_zero_not_mem
      Phi := Phi
      Phi_aestronglyMeasurable := hPhi_meas
      Phi_memL2 := hPhi_L2
      Phi_integrable := hPhi_int
      Phi_moment_one := hPhi_one
      Phi_moment_zero := hPhi_zero
      phi := phi
      phi_def := by
        intro u
        rfl
      phi_cont := continuous_fiber_fourierMoment hPhi_int
      phi_zero := hphi_zero
      phi_vanish_E := hphi_vanish_E
      phi_vanish_K_lattice := hphi_vanish_K_lattice
    }, trivial⟩

theorem PhiZeroExt_aestronglyMeasurable {d : ℕ}
    {A : Set (E d)} {Phi : E d → ℂ}
    (hA : MeasurableSet A)
    (hPhi : AEStronglyMeasurable Phi (volume.restrict A)) :
    AEStronglyMeasurable (PhiZeroExt A Phi) volume := by
  simpa [PhiZeroExt] using
    ((aestronglyMeasurable_indicator_iff (μ := volume)
      (f := Phi) hA).mpr hPhi)

theorem PhiZeroExt_integrable_volume_iff {d : ℕ}
    {A : Set (E d)} {Phi : E d → ℂ}
    (hA : MeasurableSet A) :
    Integrable (PhiZeroExt A Phi) volume ↔
      Integrable Phi (volume.restrict A) := by
  simpa [PhiZeroExt, IntegrableOn] using
    (integrable_indicator_iff (μ := volume) (f := Phi) hA)

theorem PhiZeroExt_memLp_volume_iff {d : ℕ}
    {A : Set (E d)} {Phi : E d → ℂ}
    (hA : MeasurableSet A) :
    MemLp (PhiZeroExt A Phi) 2 volume ↔
      MemLp Phi 2 (volume.restrict A) := by
  simpa [PhiZeroExt] using
    (memLp_indicator_iff_restrict (μ := volume) (p := (2 : ℝ≥0∞))
      (f := Phi) hA)

theorem shifted_PhiZeroExt_integrable {d : ℕ}
    {A : Set (E d)} {Phi : E d → ℂ}
    (hA : MeasurableSet A)
    (hPhi : Integrable Phi (volume.restrict A))
    (k : Fin d → ℕ) :
    Integrable (fun xi => PhiZeroExt A Phi (xi - natVec k)) volume := by
  have hPhi0 : Integrable (PhiZeroExt A Phi) volume :=
    (PhiZeroExt_integrable_volume_iff hA).2 hPhi
  simpa [sub_eq_add_neg] using hPhi0.comp_add_right (-(natVec k))

theorem shifted_PhiZeroExt_memLp {d : ℕ}
    {A : Set (E d)} {Phi : E d → ℂ}
    (hA : MeasurableSet A)
    (hPhi : MemLp Phi 2 (volume.restrict A))
    (k : Fin d → ℕ) :
    MemLp (fun xi => PhiZeroExt A Phi (xi - natVec k)) 2 volume := by
  have hPhi0 : MemLp (PhiZeroExt A Phi) 2 volume :=
    (PhiZeroExt_memLp_volume_iff hA).2 hPhi
  simpa [Function.comp_def, sub_eq_add_neg] using
    hPhi0.comp_measurePreserving
      (measurePreserving_add_right (μ := volume) (-(natVec k)))

theorem shifted_zeroExtension_supported_in_spectrum {d : ℕ}
    {A : Set (E d)} {Phi : E d → ℂ}
    (k : Fin d → ℕ) :
    SupportedInSpectrumAE A
      (fun xi => PhiZeroExt A Phi (xi - natVec k)) := by
  refine Filter.Eventually.of_forall ?_
  intro xi hxi
  have hnot : xi - natVec k ∉ A := by
    intro hmem
    have hs' :=
      mem_spectrum_of_mem_translate (A := A) hmem
        (fun i : Fin d => (k i : ℤ))
    have hxi_eq : (xi - natVec k) +
        intVec (fun i : Fin d => (k i : ℤ)) = xi := by
      rw [← natVec_eq_intVec_natCast k]
      abel
    exact hxi (hxi_eq ▸ hs')
  exact PhiZeroExt_eq_zero_of_not_mem hnot

theorem candidate_support_in_spectrum {d : ℕ}
    {A K : Set (E d)} {y : E d} {E0 : Finset (E d)}
    (seed : PeakSeed A K y E0)
    {N : ℕ} {b : (Fin d → ℕ) → ℂ} :
    SupportedInSpectrumAE A (candidateP A seed N b) := by
  refine Filter.Eventually.of_forall ?_
  intro xi hxi
  dsimp [candidateP]
  have hsum_zero :
      (indexBox d N).sum
        (fun k => b k * PhiZeroExt A seed.Phi (xi - natVec k)) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro k _hk
    have hnot : xi - natVec k ∉ A := by
      intro hmem
      have hs' :=
        mem_spectrum_of_mem_translate (A := A) hmem
          (fun i : Fin d => (k i : ℤ))
      have hxi_eq : (xi - natVec k) +
          intVec (fun i : Fin d => (k i : ℤ)) = xi := by
        rw [← natVec_eq_intVec_natCast k]
        abel
      exact hxi (hxi_eq ▸ hs')
    simp [PhiZeroExt_eq_zero_of_not_mem hnot]
  simp [hsum_zero]

theorem candidate_integrable {d : ℕ}
    {A K : Set (E d)} {y : E d} {E0 : Finset (E d)}
    (hA : AContextHD d A) (seed : PeakSeed A K y E0)
    {N : ℕ} {b : (Fin d → ℕ) → ℂ} :
    Integrable (candidateP A seed N b) volume := by
  have hsum_int :
      Integrable
        (fun xi : E d =>
          (indexBox d N).sum
            (fun k => b k * PhiZeroExt A seed.Phi (xi - natVec k))) volume := by
    simpa using
      (integrable_finsetSum (μ := volume) (indexBox d N)
        (f := fun k xi => b k * PhiZeroExt A seed.Phi (xi - natVec k))
        (by
          intro k _hk
          exact
            (shifted_PhiZeroExt_integrable hA.measurable
              seed.Phi_integrable k).const_mul (b k)))
  have hexp_aesm :
      AEStronglyMeasurable
        (fun xi : E d => exp2piI (-(inner ℝ y xi))) volume := by
    exact (continuous_exp2piI.comp (by fun_prop)).aestronglyMeasurable
  change
    Integrable
      (fun xi : E d =>
        exp2piI (-(inner ℝ y xi)) *
          (indexBox d N).sum
            (fun k => b k * PhiZeroExt A seed.Phi (xi - natVec k)))
      volume
  refine hsum_int.bdd_mul (c := 1) hexp_aesm ?_
  filter_upwards with xi
  rw [norm_exp2piI]

theorem candidate_memL2 {d : ℕ}
    {A K : Set (E d)} {y : E d} {E0 : Finset (E d)}
    (hA : AContextHD d A) (seed : PeakSeed A K y E0)
    {N : ℕ} {b : (Fin d → ℕ) → ℂ} :
    MemLp (candidateP A seed N b) 2 volume := by
  have hsum_L2 :
      MemLp
        (fun xi : E d =>
          (indexBox d N).sum
            (fun k => b k * PhiZeroExt A seed.Phi (xi - natVec k))) 2 volume := by
    simpa using
      (memLp_finsetSum (μ := volume) (p := (2 : ℝ≥0∞)) (indexBox d N)
        (f := fun k xi => b k * PhiZeroExt A seed.Phi (xi - natVec k))
        (by
          intro k _hk
          exact
            (shifted_PhiZeroExt_memLp hA.measurable
              seed.Phi_memL2 k).const_mul (b k)))
  have hexp_aesm :
      AEStronglyMeasurable
        (fun xi : E d => exp2piI (-(inner ℝ y xi))) volume := by
    exact (continuous_exp2piI.comp (by fun_prop)).aestronglyMeasurable
  change
    MemLp
      (fun xi : E d =>
        exp2piI (-(inner ℝ y xi)) *
          (indexBox d N).sum
            (fun k => b k * PhiZeroExt A seed.Phi (xi - natVec k)))
      2 volume
  refine hsum_L2.of_le_mul (c := 1) ?_ ?_
  · exact (hexp_aesm.mul hsum_L2.aestronglyMeasurable)
  · filter_upwards with xi
    rw [norm_mul, norm_exp2piI, one_mul]

theorem candidate_continuous {d : ℕ}
    {A K : Set (E d)} {y : E d} {E0 : Finset (E d)}
    (seed : PeakSeed A K y E0)
    {N : ℕ} {b : (Fin d → ℕ) → ℂ} :
    Continuous (candidatep seed N b) := by
  change Continuous
    (fun x : E d => seed.phi (x - y) * coeffPolynomial N b (x - y))
  exact
    (seed.phi_cont.comp (by fun_prop)).mul
      ((continuous_coeffPolynomial b).comp (by fun_prop))

theorem candidate_values {d : ℕ}
    {A K : Set (E d)} {y : E d} {E0 : Finset (E d)}
    (seed : PeakSeed A K y E0)
    {N : ℕ} {b : (Fin d → ℕ) → ℂ}
    (hsum : (indexBox d N).sum b = 1) :
    candidatep seed N b y = 1 ∧
      ∀ e ∈ E0, candidatep seed N b e = 0 := by
  constructor
  · dsimp [candidatep]
    simp [seed.phi_zero, coeffPolynomial_zero hsum]
  · intro e he
    dsimp [candidatep]
    simp [seed.phi_vanish_E e he]

theorem candidate_inverse_integral_identity {d : ℕ} (hd_pos : 0 < d)
    {A K : Set (E d)} {y : E d} {E0 : Finset (E d)}
    (hA : AContextHD d A)
    (seed : PeakSeed A K y E0)
    {N : ℕ} {b : (Fin d → ℕ) → ℂ}
    (hN : 1 ≤ N) :
    ∀ x : E d,
      candidatep seed N b x =
        inverseFourierIntegral (candidateP A seed N b) x := by
  have _hd_pos : 0 < d := hd_pos
  have _hN : 1 ≤ N := hN
  intro x
  let u : E d := x - y
  have hterm_int :
      ∀ k ∈ indexBox d N,
        Integrable
          (fun xi : E d =>
            fourierChar xi x *
              (exp2piI (-(inner ℝ y xi)) *
                (b k * PhiZeroExt A seed.Phi (xi - natVec k)))) volume := by
    intro k _hk
    have hbase :
        Integrable
          (fun xi : E d => PhiZeroExt A seed.Phi (xi - natVec k)) volume :=
      shifted_PhiZeroExt_integrable hA.measurable seed.Phi_integrable k
    have hscaled :
        Integrable
          (fun xi : E d => b k * PhiZeroExt A seed.Phi (xi - natVec k)) volume :=
      hbase.const_mul (b k)
    have hmid :
        Integrable
          (fun xi : E d =>
            exp2piI (-(inner ℝ y xi)) *
              (b k * PhiZeroExt A seed.Phi (xi - natVec k))) volume := by
      refine hscaled.bdd_mul (c := 1) ?_ ?_
      · exact (continuous_exp2piI.comp (by fun_prop)).aestronglyMeasurable
      · filter_upwards with xi
        rw [norm_exp2piI]
    refine hmid.bdd_mul (c := 1) ?_ ?_
    · exact (continuous_exp2piI.comp (by fun_prop)).aestronglyMeasurable
    · filter_upwards with xi
      simp [fourierChar, norm_exp2piI]
  calc
    candidatep seed N b x =
        seed.phi u * coeffPolynomial N b u := by
      rfl
    _ =
        (indexBox d N).sum
          (fun k =>
            ∫ xi : E d,
              fourierChar xi x *
                (exp2piI (-(inner ℝ y xi)) *
                  (b k * PhiZeroExt A seed.Phi (xi - natVec k)))) := by
      rw [coeffPolynomial]
      calc
        seed.phi u *
            (indexBox d N).sum
              (fun k => b k * exp2piI (inner ℝ (natVec k) u)) =
            (indexBox d N).sum
              (fun k => b k *
                (exp2piI (inner ℝ (natVec k) u) * seed.phi u)) := by
          simp [Finset.mul_sum, mul_assoc, mul_comm]
        _ =
            (indexBox d N).sum
              (fun k =>
                ∫ xi : E d,
                  fourierChar xi x *
                    (exp2piI (-(inner ℝ y xi)) *
                      (b k * PhiZeroExt A seed.Phi (xi - natVec k)))) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          have hcalc :
              (∫ xi : E d,
                  fourierChar xi x *
                    (exp2piI (-(inner ℝ y xi)) *
                      (b k * PhiZeroExt A seed.Phi (xi - natVec k)))) =
                b k *
                  (exp2piI (inner ℝ (natVec k) u) * seed.phi u) := by
            calc
              (∫ xi : E d,
                  fourierChar xi x *
                    (exp2piI (-(inner ℝ y xi)) *
                      (b k * PhiZeroExt A seed.Phi (xi - natVec k)))) =
                  ∫ xi : E d,
                    b k *
                      (exp2piI (inner ℝ xi u) *
                        PhiZeroExt A seed.Phi (xi - natVec k)) := by
                apply integral_congr_ae
                filter_upwards with xi
                rw [fourierChar, ← mul_assoc, exp2piI_inner_sub]
                simp [u, mul_assoc, mul_comm]
              _ =
                  b k *
                    ∫ xi : E d,
                      exp2piI (inner ℝ xi u) *
                        PhiZeroExt A seed.Phi (xi - natVec k) := by
                rw [integral_const_mul]
              _ =
                  b k *
                    (exp2piI (inner ℝ (natVec k) u) *
                      ∫ t : E d,
                        seed.Phi t * exp2piI (inner ℝ t u)
                          ∂volume.restrict A) := by
                rw [integral_exp_translate_PhiZeroExt hA.measurable seed.Phi u (natVec k)]
              _ = b k * (exp2piI (inner ℝ (natVec k) u) * seed.phi u) := by
                rw [seed.phi_def u]
          exact hcalc.symm
    _ = inverseFourierIntegral (candidateP A seed N b) x := by
      unfold inverseFourierIntegral candidateP
      rw [← integral_finsetSum (indexBox d N) hterm_int]
      congr 1
      ext xi
      simp [Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]

theorem candidate_inverse_fourier_identity {d : ℕ} (hd_pos : 0 < d)
    {A K : Set (E d)} {y : E d} {E0 : Finset (E d)}
    (hA : AContextHD d A)
    (seed : PeakSeed A K y E0)
    {N : ℕ} {b : (Fin d → ℕ) → ℂ}
    (hN : 1 ≤ N) :
    ContinuousInvFourierRep
      (candidateP A seed N b) (candidatep seed N b) := by
  exact
    continuousInvFourierRep_of_integrable_inverseIntegral
      (candidate_integrable hA seed)
      (candidate_memL2 hA seed)
      (candidate_continuous seed)
      (candidate_inverse_integral_identity hd_pos hA seed hN)

theorem exists_peak_candidate {d : ℕ} (hd_pos : 0 < d)
    {A K : Set (E d)} {y : E d} {E0 : Finset (E d)}
    (hA : AContextHD d A)
    (seed : PeakSeed A K y E0)
    {N : ℕ} (hN : 1 ≤ N)
    {b : (Fin d → ℕ) → ℂ}
    (hsum : (indexBox d N).sum b = 1) :
    ∃ _C : PeakCandidate A K y E0 seed N b, True := by
  have _hd_pos : 0 < d := hd_pos
  have hvalues := candidate_values seed hsum
  exact
    ⟨{
      hN := hN
      sum_b := hsum
      P_integrable := candidate_integrable hA seed
      P_memL2 := candidate_memL2 hA seed
      P_supported := candidate_support_in_spectrum seed
      p_cont := candidate_continuous seed
      p_y := hvalues.1
      p_zero_E := hvalues.2
    }, trivial⟩

theorem PeakCandidate.toWeightedFourierSide {d : ℕ}
    {A K : Set (E d)} {y : E d} {E0 : Finset (E d)}
    {seed : PeakSeed A K y E0} {N : ℕ}
    {b : (Fin d → ℕ) → ℂ}
    (C : PeakCandidate A K y E0 seed N b)
    (h_weighted : WeightedEnergyIntegrable alpha A (candidateP A seed N b)) :
    WeightedFourierSide alpha A (candidateP A seed N b) := by
  exact
    { aestronglyMeasurable := C.P_memL2.aestronglyMeasurable
      supported := C.P_supported
      weightedMemLp := h_weighted
      memL2 := C.P_memL2 }

theorem PeakCandidate.toWeightedFourierWitness {d : ℕ} (hd_pos : 0 < d)
    {A K : Set (E d)} {y : E d} {E0 : Finset (E d)}
    (hA : AContextHD d A)
    {seed : PeakSeed A K y E0} {N : ℕ}
    {b : (Fin d → ℕ) → ℂ}
    (C : PeakCandidate A K y E0 seed N b)
    (h_weighted : WeightedEnergyIntegrable alpha A (candidateP A seed N b)) :
    WeightedFourierWitness alpha A
      (candidatep seed N b) (candidateP A seed N b) := by
  exact
    { side := C.toWeightedFourierSide h_weighted
      invRep := candidate_inverse_fourier_identity hd_pos hA seed C.hN }

end SpectralGapsPrelim.HigherDim
