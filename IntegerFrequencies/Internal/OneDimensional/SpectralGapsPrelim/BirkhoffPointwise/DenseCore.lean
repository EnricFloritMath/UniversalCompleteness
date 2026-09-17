import SpectralGapsPrelim.BirkhoffPointwise.Conventions

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Topology ENNReal

namespace SpectralGapsPrelim.BirkhoffPointwise

variable {X : Type*} [MeasurableSpace X]
variable {μ : Measure X} [IsProbabilityMeasure μ] {τ : X → X}

omit [IsProbabilityMeasure μ] in
private lemma koopmanL2CLM_norm_le_one
    (hτ_mp : MeasurePreserving τ μ μ) :
    ‖koopmanL2CLM (μ := μ) hτ_mp‖ ≤ 1 := by
  simpa [koopmanL2CLM] using
    (koopmanL2 (μ := μ) hτ_mp).norm_toContinuousLinearMap_le

omit [IsProbabilityMeasure μ] in
private lemma koopmanL2_ae_eq_comp
    (hτ_mp : MeasurePreserving τ μ μ) (g : Lp ℝ 2 μ) :
    (fun x => (koopmanL2 (μ := μ) hτ_mp g) x)
      =ᵐ[μ]
    fun x => g (τ x) := by
  simpa [koopmanL2, Function.comp_def] using
    (Lp.coeFn_compMeasurePreserving (μ := μ) (μb := μ) (f := τ) g hτ_mp)

private lemma l2ToL1_ae_eq (g : Lp ℝ 2 μ) :
    (fun x => l2ToL1 (μ := μ) g x) =ᵐ[μ] fun x => g x := by
  rw [l2ToL1]
  exact Filter.EventuallyEq.rfl

private lemma l2_norm_controls_l1_norm (g : Lp ℝ 2 μ) :
    ‖l2ToL1 (μ := μ) g‖ ≤ ‖g‖ := by
  -- Proof idea: thin local wrapper around the shared inclusion estimate.
  exact l2ToL1_norm_le (μ := μ) g

private lemma integrable_l2_coeFn (g : Lp ℝ 2 μ) :
    Integrable (fun x => g x) μ := by
  rw [← memLp_one_iff_integrable]
  have hg_one : (g : X →ₘ[μ] ℝ) ∈ Lp ℝ 1 μ :=
    (MeasureTheory.Lp.antitone
      (E := ℝ) (μ := μ) (p := 1) (q := 2)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)) g.2
  exact (Lp.mem_Lp_iff_memLp).1 hg_one

lemma L2CoboundaryCore.integrable_g
    (C : L2CoboundaryCore (X := X) τ μ) :
    Integrable (fun x => C.g x) μ := by
  exact integrable_l2_coeFn (μ := μ) C.g

lemma L2CoboundaryCore.integrable_g_comp
    (hτ_mp : MeasurePreserving τ μ μ)
    (C : L2CoboundaryCore (X := X) τ μ) :
    Integrable (fun x => C.g (τ x)) μ := by
  exact integrable_comp_measurePreserving hτ_mp C.integrable_g

lemma L2CoboundaryCore.toL2_ae_eq_toFun
    (hτ_mp : MeasurePreserving τ μ μ)
    (C : L2CoboundaryCore (X := X) τ μ) :
    (fun x => (C.toL2 (τ := τ) hτ_mp) x)
      =ᵐ[μ]
    C.toFun (τ := τ) := by
  -- Proof idea: combine a.e. representatives for constants, `C.g`, and
  -- `koopmanL2`.
  filter_upwards [
    Lp.coeFn_sub (Lp.const 2 μ C.c + C.g) (koopmanL2 (μ := μ) hτ_mp C.g),
    Lp.coeFn_add (Lp.const 2 μ C.c) C.g,
    Lp.coeFn_const (α := X) (p := 2) μ C.c,
    koopmanL2_ae_eq_comp (μ := μ) hτ_mp C.g
  ] with x hsub hadd hconst hkoop
  rw [L2CoboundaryCore.toL2, L2CoboundaryCore.toFun, hsub]
  simp only [Pi.sub_apply]
  rw [hadd]
  simp only [Pi.add_apply]
  rw [hconst, hkoop]
  rfl

lemma L2CoboundaryCore.toL1_ae_eq_toFun
    (hτ_mp : MeasurePreserving τ μ μ)
    (C : L2CoboundaryCore (X := X) τ μ) :
    (fun x => (C.toL1 (τ := τ) hτ_mp) x)
      =ᵐ[μ]
    C.toFun (τ := τ) := by
  exact (l2ToL1_ae_eq (μ := μ) (C.toL2 (τ := τ) hτ_mp)).trans
    (C.toL2_ae_eq_toFun (τ := τ) hτ_mp)

lemma L2CoboundaryCore.memLp_toFun_one
    (hτ_mp : MeasurePreserving τ μ μ)
    (C : L2CoboundaryCore (X := X) τ μ) :
    MemLp (C.toFun (τ := τ)) 1 μ := by
  exact MeasureTheory.MemLp.ae_eq
    (C.toL1_ae_eq_toFun (τ := τ) hτ_mp)
    (Lp.memLp (C.toL1 (τ := τ) hτ_mp))

lemma L2CoboundaryCore.integrable_toFun
    (hτ_mp : MeasurePreserving τ μ μ)
    (C : L2CoboundaryCore (X := X) τ μ) :
    Integrable (C.toFun (τ := τ)) μ := by
  exact (memLp_one_iff_integrable).1 (C.memLp_toFun_one (τ := τ) hτ_mp)

lemma L2CoboundaryCore.toL1_eq_toL1_toFun
    (hτ_mp : MeasurePreserving τ μ μ)
    (C : L2CoboundaryCore (X := X) τ μ) :
    C.toL1 (τ := τ) hτ_mp
      =
    (C.integrable_toFun (τ := τ) hτ_mp).toL1
      (C.toFun (τ := τ)) := by
  apply Subtype.ext
  apply AEEqFun.ext
  exact (C.toL1_ae_eq_toFun (τ := τ) hτ_mp).trans
    ((C.integrable_toFun (τ := τ) hτ_mp).coeFn_toL1).symm

omit [IsProbabilityMeasure μ] in
private lemma fixed_l2_ae_const
    (hτ : Ergodic τ μ) {k : Lp ℝ 2 μ}
    (hk : koopmanL2 (μ := μ) hτ.toMeasurePreserving k = k) :
    ∃ c : ℝ, (fun x => k x) =ᵐ[μ] fun _ => c := by
  have hU_eq_k :
      (fun x => (koopmanL2 (μ := μ) hτ.toMeasurePreserving k) x)
        =ᵐ[μ] fun x => k x := by
    rw [hk]
  have hk_comp : (fun x => k (τ x)) =ᵐ[μ] fun x => k x :=
    (koopmanL2_ae_eq_comp (μ := μ) hτ.toMeasurePreserving k).symm.trans
      hU_eq_k
  rcases hτ.ae_eq_const_of_ae_eq_comp_ae (Lp.memLp k).1
      (by simpa [Function.comp_def] using hk_comp) with ⟨c, hc⟩
  exact ⟨c, hc.mono fun x hx => by simpa using hx⟩

private lemma fixed_l2_eq_Lp_const
    (hτ : Ergodic τ μ) {k : Lp ℝ 2 μ}
    (hk : koopmanL2 (μ := μ) hτ.toMeasurePreserving k = k) :
    ∃ c : ℝ, k = Lp.const 2 μ c := by
  rcases fixed_l2_ae_const (τ := τ) hτ hk with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  apply Subtype.ext
  apply AEEqFun.ext
  exact hc.trans (Lp.coeFn_const (α := X) (p := 2) μ c).symm

omit [IsProbabilityMeasure μ] in
private lemma sub_birkhoffAverage_mem_range_id_sub_koopman
    (hτ_mp : MeasurePreserving τ μ μ)
    (h : Lp ℝ 2 μ) {N : ℕ} (hN : 0 < N) :
    h - birkhoffAverage ℝ
          (koopmanL2CLM (μ := μ) hτ_mp)
          id N h
      ∈ Set.range
          (fun g : Lp ℝ 2 μ =>
            g - koopmanL2 (μ := μ) hτ_mp g) := by
  classical
  let V : Lp ℝ 2 μ →ₗᵢ[ℝ] Lp ℝ 2 μ :=
    koopmanL2 (μ := μ) hτ_mp
  refine ⟨(N : ℝ)⁻¹ •
    (Finset.sum (Finset.range N)
      (fun q => Finset.sum (Finset.range q) (fun i => V^[i] h))), ?_⟩
  simp [V, koopmanL2CLM, birkhoffAverage, birkhoffSum, Finset.smul_sum]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  have hinner (q : ℕ) :
      Finset.sum (Finset.range q) (fun i =>
          (N : ℝ)⁻¹ • (⇑(koopmanL2 (μ := μ) hτ_mp))^[i] h -
            (N : ℝ)⁻¹ •
              (koopmanL2 (μ := μ) hτ_mp)
                ((⇑(koopmanL2 (μ := μ) hτ_mp))^[i] h))
        =
      (N : ℝ)⁻¹ • (h - (⇑(koopmanL2 (μ := μ) hτ_mp))^[q] h) := by
    have hstep :
        (fun i : ℕ =>
          (N : ℝ)⁻¹ • (⇑(koopmanL2 (μ := μ) hτ_mp))^[i] h -
            (N : ℝ)⁻¹ •
              (koopmanL2 (μ := μ) hτ_mp)
                ((⇑(koopmanL2 (μ := μ) hτ_mp))^[i] h))
          =
        fun i : ℕ =>
          (N : ℝ)⁻¹ • (⇑(koopmanL2 (μ := μ) hτ_mp))^[i] h -
            (N : ℝ)⁻¹ • (⇑(koopmanL2 (μ := μ) hτ_mp))^[i + 1] h := by
      funext i
      rw [Function.iterate_succ_apply']
    rw [hstep, Finset.sum_range_sub']
    simp [smul_sub]
  simp_rw [hinner]
  simp_rw [smul_sub]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const]
  rw [Finset.card_range]
  congr 1
  rw [← Nat.cast_smul_eq_nsmul ℝ N ((N : ℝ)⁻¹ • h), smul_smul]
  have hN_real : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [mul_inv_cancel₀ hN_real, one_smul]

omit [IsProbabilityMeasure μ] in
private lemma sub_projection_mem_closure_range_id_sub_koopman
    (hτ_mp : MeasurePreserving τ μ μ)
    (h : Lp ℝ 2 μ) :
    h -
        ((koopmanL2CLM (μ := μ) hτ_mp).eqLocus
          (1 : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)).orthogonalProjectionOnto h
      ∈ closure
          (Set.range
            (fun g : Lp ℝ 2 μ =>
              g - koopmanL2 (μ := μ) hτ_mp g)) := by
  let U : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
    koopmanL2CLM (μ := μ) hτ_mp
  have htend :
      Tendsto (fun N : ℕ => birkhoffAverage ℝ U id N h) atTop
        (nhds
          (((U.eqLocus
            (1 : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)).orthogonalProjectionOnto h :
              (U.eqLocus (1 : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ))) :
            Lp ℝ 2 μ)) := by
    simpa [U] using
      ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection
        (koopmanL2CLM (μ := μ) hτ_mp)
        (koopmanL2CLM_norm_le_one (μ := μ) hτ_mp) h
  have htend_sub :
      Tendsto
        (fun N : ℕ => h - birkhoffAverage ℝ U id N h) atTop
        (nhds
          (h -
            (((U.eqLocus
              (1 : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)).orthogonalProjectionOnto h :
                (U.eqLocus (1 : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ))) :
              Lp ℝ 2 μ))) :=
    tendsto_const_nhds.sub htend
  have hevent :
      ∀ᶠ N : ℕ in atTop,
        h - birkhoffAverage ℝ U id N h ∈
          Set.range
            (fun g : Lp ℝ 2 μ =>
              g - koopmanL2 (μ := μ) hτ_mp g) := by
    refine eventually_atTop.2 ⟨1, fun N hN => ?_⟩
    exact sub_birkhoffAverage_mem_range_id_sub_koopman
      (τ := τ) hτ_mp h (Nat.lt_of_lt_of_le Nat.zero_lt_one hN)
  simpa [U] using mem_closure_of_tendsto htend_sub hevent

private lemma fixed_projection_eq_Lp_const
    (hτ : Ergodic τ μ) (h : Lp ℝ 2 μ) :
    ∃ c : ℝ,
      ((koopmanL2CLM (μ := μ) hτ.toMeasurePreserving).eqLocus
          (1 : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)).orthogonalProjectionOnto h
        =
      Lp.const 2 μ c := by
  let U : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
    koopmanL2CLM (μ := μ) hτ.toMeasurePreserving
  let K : Submodule ℝ (Lp ℝ 2 μ) :=
    U.eqLocus (1 : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
  let P : Lp ℝ 2 μ := K.orthogonalProjectionOnto h
  change ∃ c : ℝ, P = Lp.const 2 μ c
  have hP_mem : P ∈ K := (K.orthogonalProjectionOnto h).2
  have hP_fixed_clm : U P = P := by
    simpa [K] using hP_mem
  have hP_fixed : koopmanL2 (μ := μ) hτ.toMeasurePreserving P = P := by
    simpa [U, koopmanL2CLM] using hP_fixed_clm
  exact fixed_l2_eq_Lp_const (τ := τ) hτ hP_fixed

private lemma range_id_sub_koopman_subset_range_core_toL2
    (hτ_mp : MeasurePreserving τ μ μ) :
    Set.range
        (fun g : Lp ℝ 2 μ =>
          g - koopmanL2 (μ := μ) hτ_mp g)
      ⊆
    Set.range
        (L2CoboundaryCore.toL2 (τ := τ) (μ := μ) hτ_mp) := by
  rintro _ ⟨g, rfl⟩
  exact ⟨⟨0, g⟩, by simp [L2CoboundaryCore.toL2]⟩

private lemma lp_const_mem_range_l2CoboundaryCore_toL2
    (hτ_mp : MeasurePreserving τ μ μ) (c : ℝ) :
    Lp.const 2 μ c ∈
      Set.range
        (L2CoboundaryCore.toL2 (τ := τ) (μ := μ) hτ_mp) := by
  exact ⟨⟨c, 0⟩, by simp [L2CoboundaryCore.toL2]⟩

private lemma add_mem_range_l2CoboundaryCore_toL2
    (hτ_mp : MeasurePreserving τ μ μ)
    {a b : Lp ℝ 2 μ}
    (ha : a ∈
      Set.range
        (L2CoboundaryCore.toL2 (τ := τ) (μ := μ) hτ_mp))
    (hb : b ∈
      Set.range
        (L2CoboundaryCore.toL2 (τ := τ) (μ := μ) hτ_mp)) :
    a + b ∈
      Set.range
        (L2CoboundaryCore.toL2 (τ := τ) (μ := μ) hτ_mp) := by
  rcases ha with ⟨A, rfl⟩
  rcases hb with ⟨B, rfl⟩
  refine ⟨⟨A.c + B.c, A.g + B.g⟩, ?_⟩
  simp [L2CoboundaryCore.toL2, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

private lemma l2_mem_closure_range_toL2
    (hτ : Ergodic τ μ) (h : Lp ℝ 2 μ) :
    h ∈ closure
      (Set.range
        (L2CoboundaryCore.toL2 (τ := τ) (μ := μ)
          hτ.toMeasurePreserving)) := by
  -- Proof idea: decompose `h` as `(h - P h) + P h`; put `h - P h` in the
  -- closure of `range (I - U)` by mean ergodic theorem and finite telescoping;
  -- identify `P h` with a constant using `fixed_projection_eq_Lp_const`;
  -- then use the two range-inclusion helpers above.
  let U : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
    koopmanL2CLM (μ := μ) hτ.toMeasurePreserving
  let K : Submodule ℝ (Lp ℝ 2 μ) :=
    U.eqLocus (1 : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
  let P : Lp ℝ 2 μ := K.starProjection h
  let S : Set (Lp ℝ 2 μ) :=
    Set.range
      (L2CoboundaryCore.toL2 (τ := τ) (μ := μ)
        hτ.toMeasurePreserving)
  change h ∈ closure S
  have hminus :
      h - P ∈ closure S := by
    have hraw :
        h - (((K.orthogonalProjectionOnto h : K) : Lp ℝ 2 μ)) ∈
          closure
            (Set.range
              (fun g : Lp ℝ 2 μ =>
                g - koopmanL2 (μ := μ) hτ.toMeasurePreserving g)) := by
      simpa [U, K] using
        sub_projection_mem_closure_range_id_sub_koopman
          (τ := τ) hτ.toMeasurePreserving h
    exact closure_mono
      (range_id_sub_koopman_subset_range_core_toL2
        (τ := τ) hτ.toMeasurePreserving)
      (by
        have hproj : (((K.orthogonalProjectionOnto h : K) : Lp ℝ 2 μ)) = P := rfl
        rwa [hproj] at hraw)
  rcases fixed_projection_eq_Lp_const (τ := τ) hτ h with ⟨c, hP_const⟩
  have hP_const' : P = Lp.const 2 μ c := by
    simpa [U, K, P, Submodule.starProjection_apply] using hP_const
  have hP_mem : P ∈ S := by
    simpa [S, hP_const'] using
      lp_const_mem_range_l2CoboundaryCore_toL2
        (τ := τ) hτ.toMeasurePreserving c
  have hP_closure : P ∈ closure S := subset_closure hP_mem
  have hadd : (h - P) + P ∈ closure S := by
    refine map_mem_closure₂ (f := fun x y => x + y) continuous_add
      hminus hP_closure ?_
    intro a ha b hb
    exact add_mem_range_l2CoboundaryCore_toL2
      (τ := τ) hτ.toMeasurePreserving ha hb
  simpa [sub_add_cancel] using hadd


private lemma l2_coboundaryCore_denseRange_toL2
    (hτ : Ergodic τ μ) :
    DenseRange
      (L2CoboundaryCore.toL2 (τ := τ) (μ := μ) hτ.toMeasurePreserving) := by
  rw [denseRange_iff_closure_range]
  exact Set.eq_univ_of_forall fun h =>
    l2_mem_closure_range_toL2 (τ := τ) hτ h

private lemma denseRange_l2ToL1 :
    DenseRange (l2ToL1 (μ := μ)) := by
  have hsimple_dense :
      DenseRange ((↑) : Lp.simpleFunc ℝ 1 μ → Lp ℝ 1 μ) :=
    Lp.simpleFunc.denseRange (E := ℝ) (μ := μ)
      (p := 1) (by norm_num : (1 : ℝ≥0∞) ≠ ∞)
  have hsubset :
      Set.range ((↑) : Lp.simpleFunc ℝ 1 μ → Lp ℝ 1 μ)
        ⊆ Set.range (l2ToL1 (μ := μ)) := by
    rintro _ ⟨s, rfl⟩
    let f : SimpleFunc X ℝ := Lp.simpleFunc.toSimpleFunc s
    have hf_two : MemLp f 2 μ := f.memLp_of_isFiniteMeasure 2 μ
    refine ⟨hf_two.toLp f, ?_⟩
    apply Subtype.ext
    apply AEEqFun.ext
    exact (l2ToL1_ae_eq (μ := μ) (hf_two.toLp f)).trans
      ((MemLp.coeFn_toLp hf_two).trans (Lp.simpleFunc.toSimpleFunc_eq_toFun s))
  rw [denseRange_iff_closure_range]
  rw [denseRange_iff_closure_range] at hsimple_dense
  exact Set.eq_univ_of_forall fun y =>
    closure_mono hsubset (by
      rw [hsimple_dense]
      trivial)

/-- Density of the quotient-level `L2` coboundary core in `L1`. -/
theorem denseRange_l2CoboundaryCore_toL1
    (hτ : Ergodic τ μ) :
    DenseRange (L2CoboundaryCore.toL1 (τ := τ) (μ := μ)
      hτ.toMeasurePreserving) := by
  change DenseRange
    (fun C : L2CoboundaryCore (X := X) τ μ =>
      l2ToL1 (μ := μ) (C.toL2 (τ := τ) hτ.toMeasurePreserving))
  exact DenseRange.comp (g := l2ToL1 (μ := μ))
    (f := L2CoboundaryCore.toL2 (τ := τ) (μ := μ) hτ.toMeasurePreserving)
    denseRange_l2ToL1
    (l2_coboundaryCore_denseRange_toL2 (τ := τ) hτ)
    (l2ToL1 (μ := μ)).continuous

lemma L2CoboundaryCore.l1_dist_to_core_eq_integral_abs_toFun
    (hτ_mp : MeasurePreserving τ μ μ)
    {F : X → ℝ} (hF : Integrable F μ)
    (C : L2CoboundaryCore (X := X) τ μ) :
    dist (hF.toL1 F) (C.toL1 (τ := τ) hτ_mp)
      =
    ∫ x, |F x - C.toFun (τ := τ) x| ∂μ := by
  rw [L1.dist_eq_integral_dist]
  apply integral_congr_ae
  filter_upwards [hF.coeFn_toL1, C.toL1_ae_eq_toFun (τ := τ) hτ_mp] with x hFx hCx
  rw [hFx, hCx]
  simp [Real.dist_eq]

/-- Quantitative raw `L1` approximation by the dense core. -/
theorem exists_core_approx_integral_lt
    (hτ : Ergodic τ μ)
    {F : X → ℝ} (hF : Integrable F μ)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ C : L2CoboundaryCore (X := X) τ μ,
      ∫ x, |F x - C.toFun (τ := τ) x| ∂μ < eps := by
  have hclosure :
      hF.toL1 F ∈ closure
        (Set.range
          (L2CoboundaryCore.toL1 (τ := τ) (μ := μ) hτ.toMeasurePreserving)) := by
    rw [(denseRange_l2CoboundaryCore_toL1 (τ := τ) hτ).closure_range]
    trivial
  rcases (Metric.mem_closure_range_iff.mp hclosure eps heps) with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  rwa [← C.l1_dist_to_core_eq_integral_abs_toFun (τ := τ) hτ.toMeasurePreserving hF]

end SpectralGapsPrelim.BirkhoffPointwise
