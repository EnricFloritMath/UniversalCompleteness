import PeriodicWeakGapsHD.HigherDim.ExponentialIndependence

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Topology ENNReal FourierTransform

namespace SpectralGapsPrelim.HigherDim

/-!
Finite moment interpolation on the fibre `A`.
-/

private lemma star_exp2piI (u : ℝ) :
    star (exp2piI u) = exp2piI (-u) := by
  unfold exp2piI
  change (starRingEnd ℂ) (Complex.exp (((2 * Real.pi * u : ℝ) : ℂ) * Complex.I)) =
    Complex.exp (((2 * Real.pi * (-u) : ℝ) : ℂ) * Complex.I)
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring_nf
  rw [mul_comm, ← mul_neg]
  simp

private lemma continuous_exp2piI :
    Continuous exp2piI := by
  unfold exp2piI
  fun_prop

private lemma exp2piI_add (u v : ℝ) :
    exp2piI (u + v) = exp2piI u * exp2piI v := by
  unfold exp2piI
  rw [← Complex.exp_add]
  congr 1
  apply Complex.ext
  all_goals simp
  all_goals ring_nf

private lemma star_exp2piI_inner_mul {d : ℕ} (h h' t : E d) :
    star (exp2piI (inner ℝ h t)) * exp2piI (inner ℝ h' t) =
      exp2piI (inner ℝ (h' - h) t) := by
  rw [star_exp2piI, ← exp2piI_add]
  congr 1
  rw [inner_sub_left]
  ring

private lemma ofReal_norm_sq_eq_star_mul (z : ℂ) :
    ((‖z‖ ^ 2 : ℝ) : ℂ) = star z * z := by
  rw [Complex.star_def]
  rw [← Complex.normSq_eq_conj_mul_self]
  congr 1
  simpa [RCLike.normSq, Complex.normSq] using (RCLike.normSq_eq_def' z).symm

private lemma integrable_exp2piI_inner {d : ℕ}
    (μ : Measure (E d)) [IsFiniteMeasure μ] (h : E d) :
    Integrable (fun t : E d => exp2piI (inner ℝ h t)) μ := by
  refine Integrable.of_bound (continuous_exp2piI.comp (by fun_prop)).aestronglyMeasurable 1 ?_
  filter_upwards with t
  simp [exp2piI, Complex.norm_exp]

private lemma memLp_star_exp2piI_inner {d : ℕ}
    (μ : Measure (E d)) [IsFiniteMeasure μ] (h : E d) :
    MemLp (fun t : E d => star (exp2piI (inner ℝ h t))) 2 μ := by
  refine MemLp.of_bound ?_ 1 ?_
  · apply Continuous.aestronglyMeasurable
    unfold exp2piI
    fun_prop
  · filter_upwards with t
    simp [exp2piI, Complex.norm_exp]

private lemma inner_toLp_star_exp2piI_inner_eq_integral {d : ℕ}
    (μ : Measure (E d)) [IsFiniteMeasure μ] (h : E d) (x : Lp ℂ 2 μ) :
    inner ℂ
        ((memLp_star_exp2piI_inner μ h).toLp
          (fun t : E d => star (exp2piI (inner ℝ h t)))) x =
      ∫ t, x t * exp2piI (inner ℝ h t) ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MeasureTheory.MemLp.coeFn_toLp
    (memLp_star_exp2piI_inner μ h)] with t ht
  rw [RCLike.inner_apply, ht]
  simp

private lemma exists_vector_with_inner_values
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℂ E']
    {v : ι → E'} (hv : LinearIndependent ℂ v) (a : ι → ℂ) :
    ∃ x : E', ∀ i, inner ℂ (v i) x = a i := by
  classical
  let V : Submodule ℂ E' := Submodule.span ℂ (Set.range v)
  let b : Module.Basis ι ℂ V := Module.Basis.span hv
  let T : V →ₗ[ℂ] (ι → ℂ) :=
    { toFun := fun x i => inner ℂ (v i) (x : E')
      map_add' := by
        intro x y
        ext i
        simp
      map_smul' := by
        intro c x
        ext i
        simp }
  have hTinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot]
    exact (Submodule.eq_bot_iff (LinearMap.ker T)).2 (by
      intro x hx
      have hxT : T x = 0 := by
        simpa [LinearMap.mem_ker] using hx
      have hxinner : ∀ i, inner ℂ (v i) (x : E') = 0 := by
        intro i
        exact congr_fun hxT i
      have hxsum : (x : E') = ∑ i, (b.repr x i) • v i := by
        have hsumV : (∑ i, (b.repr x i) • b i : V) = x :=
          Module.Basis.sum_repr b x
        calc
          (x : E') = V.subtype x := rfl
          _ = V.subtype (∑ i, (b.repr x i) • b i) := by rw [hsumV]
          _ = ∑ i, (b.repr x i) • (b i : E') := by
            rw [map_sum]
            apply Finset.sum_congr rfl
            intro i _hi
            rw [map_smul]
            rfl
          _ = ∑ i, (b.repr x i) • v i := by
            apply Finset.sum_congr rfl
            intro i _hi
            rw [show (b i : E') = v i from Module.Basis.coe_span_apply hv i]
      have hinner_self : inner ℂ (x : E') (x : E') = 0 := by
        nth_rw 1 [hxsum]
        rw [sum_inner]
        exact Finset.sum_eq_zero fun i _hi => by
          simp [inner_smul_left, hxinner i]
      exact Subtype.ext (inner_self_eq_zero.mp hinner_self))
  letI : FiniteDimensional ℂ V := Module.Basis.finiteDimensional_of_finite b
  have hdim : Module.finrank ℂ V = Module.finrank ℂ (ι → ℂ) := by
    rw [Module.finrank_eq_card_basis b, Module.finrank_fintype_fun_eq_card]
  have hsurj : Function.Surjective T :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hTinj
  rcases hsurj a with ⟨x, hx⟩
  refine ⟨(x : E'), ?_⟩
  intro i
  exact congr_fun hx i

theorem exists_fiber_moment_interpolant_hd {d : ℕ} (hd_pos : 0 < d)
    {A : Set (E d)}
    (hA_meas : MeasurableSet A)
    (hA_pos : 0 < volume A)
    (hA_finite : volume A < ∞)
    {D : Finset (E d)}
    (hD_zero : ∀ h ∈ D, h ≠ 0) :
    ∃ Phi : E d → ℂ,
      AEStronglyMeasurable Phi (volume.restrict A) ∧
      MemLp Phi 2 (volume.restrict A) ∧
      Integrable Phi (volume.restrict A) ∧
      (∫ t, Phi t ∂(volume.restrict A)) = 1 ∧
      (∀ h ∈ D,
        (∫ t, Phi t * exp2piI (inner ℝ h t) ∂(volume.restrict A)) = 0) := by
  classical
  let μ : Measure (E d) := volume.restrict A
  haveI : IsFiniteMeasure μ :=
    ⟨by simpa [μ, Measure.restrict_apply_univ] using hA_finite⟩
  let S : Finset (E d) := insert 0 D
  let ι := {x : E d // x ∈ S}
  haveI : Fintype ι := by
    dsimp [ι]
    infer_instance
  haveI : DecidableEq ι := Classical.decEq ι
  let freq : ι → E d := fun i => i.1
  let e : E d → E d → ℂ := fun h t => star (exp2piI (inner ℝ h t))
  let v : ι → Lp ℂ 2 μ := fun i =>
    (memLp_star_exp2piI_inner μ (freq i)).toLp (e (freq i))
  have hv : LinearIndependent ℂ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hsum_coe :
        ((∑ j, g j • v j : Lp ℂ 2 μ) : E d → ℂ) =ᵐ[μ]
          fun t => ∑ j, g j * e (freq j) t := by
      refine (MeasureTheory.Lp.coeFn_finsetSum Finset.univ
        (fun j => g j • v j)).trans ?_
      have hterm : ∀ᵐ t ∂μ,
          ∀ j, ((g j • v j : Lp ℂ 2 μ) : E d → ℂ) t =
            g j * e (freq j) t := by
        exact Filter.eventually_all.2 fun j => by
          refine (MeasureTheory.Lp.coeFn_smul (g j) (v j)).trans ?_
          exact Filter.EventuallyEq.const_smul
            (MeasureTheory.MemLp.coeFn_toLp
              (memLp_star_exp2piI_inner μ (freq j))) (g j)
      filter_upwards [hterm] with t ht
      simp [ht]
    have hsum_zero :
        ((∑ j, g j • v j : Lp ℂ 2 μ) : E d → ℂ) =ᵐ[μ] 0 := by
      rw [hg]
      exact MeasureTheory.Lp.coeFn_zero ℂ 2 μ
    have hzero_sum :
        (fun t => ∑ j, g j * e (freq j) t) =ᵐ[μ] 0 :=
      hsum_coe.symm.trans hsum_zero
    have hneg_inj : Function.Injective fun j : ι => -freq j := by
      intro j k h
      apply Subtype.ext
      exact neg_injective h
    let negEmb : ι ↪ E d := ⟨fun j => -freq j, hneg_inj⟩
    let coeff : E d → ℂ := fun y =>
      if hy : ∃ j : ι, negEmb j = y then g (Classical.choose hy) else 0
    have hcoeff_neg : ∀ j : ι, coeff (negEmb j) = g j := by
      intro j
      have hmem : ∃ k : ι, negEmb k = negEmb j := ⟨j, rfl⟩
      have hchoose : Classical.choose hmem = j :=
        hneg_inj (Classical.choose_spec hmem)
      dsimp [coeff]
      rw [dif_pos hmem, hchoose]
    have hzero_exp : ∀ᵐ t ∂μ,
        ((Finset.univ.map negEmb).sum
          (fun h => coeff h * exp2piI (inner ℝ h t))) = 0 := by
      filter_upwards [hzero_sum] with t ht
      rw [Finset.sum_map]
      calc
        ∑ x, coeff (negEmb x) * exp2piI (inner ℝ (negEmb x) t)
            = ∑ x, g x * e (freq x) t := by
              apply Finset.sum_congr rfl
              intro x _hx
              rw [hcoeff_neg x]
              simp [e, negEmb, star_exp2piI, inner_neg_left]
        _ = 0 := ht
    have hgzero := exp_sum_eq_zero_ae_of_coeffs_zero_hd
      (d := d) hd_pos hA_meas hA_pos (s := Finset.univ.map negEmb)
      (c := coeff) hzero_exp
    have hi_mem : negEmb i ∈ Finset.univ.map negEmb := by
      simp [negEmb]
    have hcoeff_zero : coeff (negEmb i) = 0 :=
      hgzero (negEmb i) hi_mem
    simpa [hcoeff_neg] using hcoeff_zero
  let target : ι → ℂ := fun i => if (i : E d) = 0 then 1 else 0
  rcases exists_vector_with_inner_values (v := v) hv target with ⟨x, hx⟩
  let Phi : E d → ℂ := fun t => x t
  have hmoment : ∀ i : ι,
      ∫ t, Phi t * exp2piI (inner ℝ (freq i) t) ∂μ = target i := by
    intro i
    have hcalc :
        inner ℂ (v i) x =
          ∫ t, x t * exp2piI (inner ℝ (freq i) t) ∂μ := by
      dsimp [v, e]
      exact inner_toLp_star_exp2piI_inner_eq_integral μ (freq i) x
    simpa [Phi] using hcalc.symm.trans (hx i)
  refine ⟨Phi, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Phi, μ] using (MeasureTheory.Lp.aestronglyMeasurable x)
  · simpa [Phi, μ] using (MeasureTheory.Lp.memLp x)
  · have hPhi_mem : MemLp Phi 2 μ := by
      simpa [Phi] using (MeasureTheory.Lp.memLp x)
    simpa [μ] using (MeasureTheory.MemLp.integrable (by norm_num) hPhi_mem)
  · let i0 : ι := ⟨0, by simp [S]⟩
    have h := hmoment i0
    simpa [Phi, μ, target, freq, i0, exp2piI] using h
  · intro h hhD
    let ih : ι := ⟨h, by simp [S, hhD]⟩
    have hh_ne : h ≠ 0 := hD_zero h hhD
    have hmoment_h := hmoment ih
    simpa [Phi, μ, target, freq, ih, hh_ne] using hmoment_h

theorem exists_fiber_moment_interpolant_of_AContextHD {d : ℕ} (hd_pos : 0 < d)
    {A : Set (E d)}
    (hA : AContextHD d A)
    {D : Finset (E d)}
    (hD_zero : ∀ h ∈ D, h ≠ 0) :
    ∃ Phi : E d → ℂ,
      AEStronglyMeasurable Phi (volume.restrict A) ∧
      MemLp Phi 2 (volume.restrict A) ∧
      Integrable Phi (volume.restrict A) ∧
      (∫ t, Phi t ∂(volume.restrict A)) = 1 ∧
      (∀ h ∈ D,
        (∫ t, Phi t * exp2piI (inner ℝ h t) ∂(volume.restrict A)) = 0) := by
  exact exists_fiber_moment_interpolant_hd hd_pos hA.measurable hA.positive
    (AContextHD.finite_volume hA) hD_zero

theorem gram_quadratic_form_eq_integral_norm_sq {d : ℕ}
    {A : Set (E d)} {D0 : Finset (E d)}
    (hA_meas : MeasurableSet A)
    (hA_finite : volume A < ∞)
    (c : E d → ℂ) :
    D0.sum (fun h => D0.sum (fun h' =>
      star (c h) * c h' *
        ∫ t, exp2piI (inner ℝ (h' - h) t) ∂(volume.restrict A))) =
      ∫ t,
        ‖D0.sum (fun h => c h * exp2piI (inner ℝ h t))‖ ^ 2
        ∂(volume.restrict A) := by
  classical
  let μ : Measure (E d) := volume.restrict A
  haveI : IsFiniteMeasure μ :=
    ⟨by simpa [μ, Measure.restrict_apply_univ] using hA_finite⟩
  have _hA_meas : MeasurableSet A := hA_meas
  let F : E d → ℂ := fun t =>
    D0.sum (fun h => c h * exp2piI (inner ℝ h t))
  have hpoint : ∀ t : E d,
      ((‖F t‖ ^ 2 : ℝ) : ℂ) =
        D0.sum (fun h => D0.sum (fun h' =>
          star (c h) * c h' * exp2piI (inner ℝ (h' - h) t))) := by
    intro t
    calc
      ((‖F t‖ ^ 2 : ℝ) : ℂ)
          = D0.sum (fun h' => D0.sum (fun h =>
              star (exp2piI (inner ℝ h t)) *
                (star (c h) * (c h' * exp2piI (inner ℝ h' t))))) := by
            simpa [F, Finset.sum_mul, Finset.mul_sum, star_mul, mul_assoc] using
              (ofReal_norm_sq_eq_star_mul (F t))
      _ = D0.sum (fun h => D0.sum (fun h' =>
              star (exp2piI (inner ℝ h t)) *
                (star (c h) * (c h' * exp2piI (inner ℝ h' t))))) := by
            rw [Finset.sum_comm]
      _ = D0.sum (fun h => D0.sum (fun h' =>
              star (c h) * c h' * exp2piI (inner ℝ (h' - h) t))) := by
            apply Finset.sum_congr rfl
            intro h hh
            apply Finset.sum_congr rfl
            intro h' hh'
            calc
              star (exp2piI (inner ℝ h t)) *
                  (star (c h) * (c h' * exp2piI (inner ℝ h' t)))
                  = star (c h) * c h' *
                      (star (exp2piI (inner ℝ h t)) *
                        exp2piI (inner ℝ h' t)) := by
                    ring
              _ = star (c h) * c h' * exp2piI (inner ℝ (h' - h) t) := by
                    rw [star_exp2piI_inner_mul]
  have hterm_int : ∀ h ∈ D0, ∀ h' ∈ D0,
      Integrable
        (fun t : E d =>
          star (c h) * c h' * exp2piI (inner ℝ (h' - h) t)) μ := by
    intro h _hh h' _hh'
    simpa [mul_assoc] using
      (integrable_exp2piI_inner μ (h' - h)).const_mul (star (c h) * c h')
  calc
    D0.sum (fun h => D0.sum (fun h' =>
      star (c h) * c h' *
        ∫ t, exp2piI (inner ℝ (h' - h) t) ∂(volume.restrict A)))
        = D0.sum (fun h => D0.sum (fun h' =>
            ∫ t,
              star (c h) * c h' * exp2piI (inner ℝ (h' - h) t) ∂μ)) := by
          apply Finset.sum_congr rfl
          intro h hh
          apply Finset.sum_congr rfl
          intro h' hh'
          rw [MeasureTheory.integral_const_mul]
    _ = D0.sum (fun h =>
          ∫ t, D0.sum (fun h' =>
            star (c h) * c h' * exp2piI (inner ℝ (h' - h) t)) ∂μ) := by
          apply Finset.sum_congr rfl
          intro h hh
          exact (MeasureTheory.integral_finsetSum D0
            (fun h' hh' => hterm_int h hh h' hh')).symm
    _ = ∫ t, D0.sum (fun h => D0.sum (fun h' =>
          star (c h) * c h' * exp2piI (inner ℝ (h' - h) t))) ∂μ := by
          exact (MeasureTheory.integral_finsetSum D0
            (fun h hh => MeasureTheory.integrable_finsetSum D0
              (fun h' hh' => hterm_int h hh h' hh'))).symm
    _ = ∫ t, ‖D0.sum (fun h => c h * exp2piI (inner ℝ h t))‖ ^ 2
        ∂(volume.restrict A) := by
          change
            ∫ t, D0.sum (fun h => D0.sum (fun h' =>
              star (c h) * c h' * exp2piI (inner ℝ (h' - h) t))) ∂μ =
              (((∫ t,
                ‖D0.sum (fun h => c h * exp2piI (inner ℝ h t))‖ ^ 2 ∂μ) : ℝ) : ℂ)
          have h_ofReal :
              (∫ t : E d,
                ((‖D0.sum (fun h => c h * exp2piI (inner ℝ h t))‖ ^ 2 : ℝ) : ℂ) ∂μ) =
                (((∫ t : E d,
                  ‖D0.sum (fun h => c h * exp2piI (inner ℝ h t))‖ ^ 2 ∂μ) : ℝ) : ℂ) :=
            integral_ofReal (μ := μ)
          rw [← h_ofReal]
          change
            ∫ t, D0.sum (fun h => D0.sum (fun h' =>
              star (c h) * c h' * exp2piI (inner ℝ (h' - h) t))) ∂μ =
              ∫ t,
                ((‖D0.sum (fun h => c h * exp2piI (inner ℝ h t))‖ ^ 2 : ℝ) : ℂ) ∂μ
          apply integral_congr_ae
          filter_upwards with t
          symm
          simpa [F, μ] using hpoint t

theorem gram_integral_norm_sq_zero_iff_ae_zero {d : ℕ}
    {A : Set (E d)} {D0 : Finset (E d)}
    (hA_meas : MeasurableSet A)
    (hA_finite : volume A < ∞)
    (c : E d → ℂ) :
    (∫ t,
        ‖D0.sum (fun h => c h * exp2piI (inner ℝ h t))‖ ^ 2
        ∂(volume.restrict A)) = 0 ↔
      (∀ᵐ t ∂(volume.restrict A),
        D0.sum (fun h => c h * exp2piI (inner ℝ h t)) = 0) := by
  classical
  have _hA_meas : MeasurableSet A := hA_meas
  let μ : Measure (E d) := volume.restrict A
  haveI : IsFiniteMeasure μ :=
    ⟨by simpa [μ, Measure.restrict_apply_univ] using hA_finite⟩
  let F : E d → ℂ := fun t =>
    D0.sum (fun h => c h * exp2piI (inner ℝ h t))
  have hF_cont : Continuous F := by
    dsimp [F]
    exact continuous_finsetSum D0 fun h _hh =>
      continuous_const.mul (continuous_exp2piI.comp (by fun_prop))
  let C : ℝ := D0.sum fun h => ‖c h‖
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact Finset.sum_nonneg fun h _hh => norm_nonneg (c h)
  have hint : Integrable (fun t => ‖F t‖ ^ 2) μ := by
    refine Integrable.of_bound (hF_cont.norm.pow 2).aestronglyMeasurable (C ^ 2) ?_
    filter_upwards with t
    have hF_le : ‖F t‖ ≤ C := by
      calc
        ‖F t‖ ≤ D0.sum (fun h => ‖c h * exp2piI (inner ℝ h t)‖) := by
          dsimp [F]
          exact norm_sum_le D0 fun h => c h * exp2piI (inner ℝ h t)
        _ = C := by
          dsimp [C]
          apply Finset.sum_congr rfl
          intro h _hh
          simp [exp2piI, Complex.norm_exp]
    rw [Real.norm_of_nonneg (sq_nonneg (‖F t‖))]
    exact pow_le_pow_left₀ (norm_nonneg (F t)) hF_le 2
  have hnonneg : 0 ≤ᵐ[μ] fun t => ‖F t‖ ^ 2 :=
    Filter.Eventually.of_forall fun t => sq_nonneg (‖F t‖)
  rw [show (∫ t,
        ‖D0.sum (fun h => c h * exp2piI (inner ℝ h t))‖ ^ 2
        ∂(volume.restrict A)) = 0 ↔
      (∫ t, ‖F t‖ ^ 2 ∂μ) = 0 by rfl]
  constructor
  · intro hzero
    have hsq_zero :
        (fun t => ‖F t‖ ^ 2) =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae hnonneg hint).1 hzero
    filter_upwards [hsq_zero] with t ht
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp ht)
  · intro hF_zero
    have hsq_zero : (fun t => ‖F t‖ ^ 2) =ᵐ[μ] 0 := by
      filter_upwards [hF_zero] with t ht
      have htF : F t = 0 := by
        simpa [F] using ht
      simp [htF]
    exact (integral_eq_zero_iff_of_nonneg_ae hnonneg hint).2 hsq_zero

theorem gram_kernel_coefficients_zero {d : ℕ} (hd_pos : 0 < d)
    {A : Set (E d)}
    (hA_meas : MeasurableSet A) (hA_pos : 0 < volume A)
    (hA_finite : volume A < ∞)
    {D0 : Finset (E d)} {c : E d → ℂ}
    (hquad :
      D0.sum (fun h => D0.sum (fun h' =>
        star (c h) * c h' *
          ∫ t, exp2piI (inner ℝ (h' - h) t) ∂(volume.restrict A))) = 0) :
    ∀ h ∈ D0, c h = 0 := by
  have hnorm_zero :
      (∫ t,
          ‖D0.sum (fun h => c h * exp2piI (inner ℝ h t))‖ ^ 2
          ∂(volume.restrict A)) = 0 := by
    have hcomplex_zero :
        (((∫ t,
            ‖D0.sum (fun h => c h * exp2piI (inner ℝ h t))‖ ^ 2
            ∂(volume.restrict A)) : ℝ) : ℂ) = 0 := by
      rw [← gram_quadratic_form_eq_integral_norm_sq hA_meas hA_finite c]
      exact hquad
    exact Complex.ofReal_eq_zero.mp hcomplex_zero
  have hae_zero :
      ∀ᵐ t ∂(volume.restrict A),
        D0.sum (fun h => c h * exp2piI (inner ℝ h t)) = 0 :=
    (gram_integral_norm_sq_zero_iff_ae_zero hA_meas hA_finite c).1 hnorm_zero
  exact exp_sum_eq_zero_ae_of_coeffs_zero_hd hd_pos hA_meas hA_pos hae_zero

theorem gramMatrix_invertible_of_exp_independent {d : ℕ} (hd_pos : 0 < d)
    {A : Set (E d)}
    (hA_meas : MeasurableSet A) (hA_pos : 0 < volume A)
    (hA_finite : volume A < ∞)
    {D0 : Finset (E d)} :
    IsUnit (Matrix.det
      (fun h1 : D0 => fun h2 : D0 =>
        ∫ t, exp2piI (inner ℝ ((h1 : E d) - (h2 : E d)) t)
          ∂(volume.restrict A))) := by
  classical
  let G : Matrix D0 D0 ℂ := fun h1 h2 =>
    ∫ t, exp2piI (inner ℝ ((h2 : E d) - (h1 : E d)) t)
      ∂(volume.restrict A)
  have hG_inj : Function.Injective G.mulVec := by
    intro x y hxy
    have hker : Matrix.mulVec G (x - y) = 0 := by
      rw [Matrix.mulVec_sub, hxy, sub_self]
    let c : E d → ℂ := fun h => if hh : h ∈ D0 then (x - y) ⟨h, hh⟩ else 0
    have hc_apply : ∀ h (hh : h ∈ D0), c h = (x - y) ⟨h, hh⟩ := by
      intro h hh
      simp [c, hh]
    have hquad :
        D0.sum (fun h => D0.sum (fun h' =>
          star (c h) * c h' *
            ∫ t, exp2piI (inner ℝ (h' - h) t) ∂(volume.restrict A))) = 0 := by
      refine Finset.sum_eq_zero fun h hh => ?_
      have hrow :
          D0.sum (fun h' =>
            c h' * ∫ t, exp2piI (inner ℝ (h' - h) t)
              ∂(volume.restrict A)) = 0 := by
        have hzrow := congr_fun hker ⟨h, hh⟩
        have hattach :
            D0.sum (fun h' =>
              c h' * ∫ t, exp2piI (inner ℝ (h' - h) t)
                ∂(volume.restrict A))
              =
            ∑ j : D0,
              c j * ∫ t, exp2piI (inner ℝ ((j : E d) - h) t)
                ∂(volume.restrict A) := by
          simpa using
            (Finset.sum_attach D0
              (fun h' =>
                c h' * ∫ t, exp2piI (inner ℝ (h' - h) t)
                  ∂(volume.restrict A))).symm
        calc
          D0.sum (fun h' =>
              c h' * ∫ t, exp2piI (inner ℝ (h' - h) t)
                ∂(volume.restrict A))
              = ∑ j : D0,
                  c j * ∫ t, exp2piI (inner ℝ ((j : E d) - h) t)
                    ∂(volume.restrict A) := hattach
          _ = ∑ j : D0,
                  G ⟨h, hh⟩ j * (x - y) j := by
                apply Finset.sum_congr rfl
                intro j _hj
                rw [hc_apply j.1 j.2]
                simp [G, mul_comm]
          _ = 0 := by
            simpa [Matrix.mulVec, dotProduct] using hzrow
      calc
        D0.sum (fun h' =>
            star (c h) * c h' *
              ∫ t, exp2piI (inner ℝ (h' - h) t) ∂(volume.restrict A))
            = star (c h) *
                D0.sum (fun h' =>
                  c h' * ∫ t, exp2piI (inner ℝ (h' - h) t)
                    ∂(volume.restrict A)) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro h' _hh'
              ring
        _ = 0 := by simp [hrow]
    have hc_zero := gram_kernel_coefficients_zero hd_pos hA_meas hA_pos hA_finite hquad
    have hsub_zero : x - y = 0 := by
      ext i
      have hci : c i = 0 := hc_zero i.1 i.2
      simpa [c, i.2] using hci
    exact sub_eq_zero.mp hsub_zero
  have hG_unit : IsUnit G :=
    (Matrix.mulVec_injective_iff_isUnit).1 hG_inj
  have hG_det : IsUnit G.det :=
    (Matrix.isUnit_iff_isUnit_det G).1 hG_unit
  have hGT_det : IsUnit G.transpose.det :=
    Matrix.isUnit_det_transpose G hG_det
  change IsUnit G.transpose.det
  exact hGT_det

theorem chosen_moment_vector_exists {d : ℕ} (hd_pos : 0 < d)
    {A : Set (E d)}
    (hA_meas : MeasurableSet A) (hA_pos : 0 < volume A)
    (hA_finite : volume A < ∞)
    {D : Finset (E d)} (hD_zero : ∀ h ∈ D, h ≠ 0) :
    ∃ Phi : E d → ℂ,
      AEStronglyMeasurable Phi (volume.restrict A) ∧
      MemLp Phi 2 (volume.restrict A) ∧
      Integrable Phi (volume.restrict A) ∧
      (∫ t, Phi t ∂(volume.restrict A)) = 1 ∧
      (∀ h ∈ D,
        (∫ t, Phi t * exp2piI (inner ℝ h t) ∂(volume.restrict A)) = 0) := by
  exact exists_fiber_moment_interpolant_hd hd_pos hA_meas hA_pos hA_finite hD_zero

end SpectralGapsPrelim.HigherDim
