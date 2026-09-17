import PeriodicWeakGapsHD.HigherDim.Definitions

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Topology ENNReal FourierTransform SchwartzMap

namespace SpectralGapsPrelim.HigherDim

/-!
Setup lemmas for the higher-dimensional nonuniqueness theorem.
-/

@[simp] lemma coord_toE {d : ℕ} (x : Fin d → ℝ) (i : Fin d) :
    coord (toE x) i = x i := by
  rfl

@[simp] lemma coord_intVec {d : ℕ} (k : Fin d → ℤ) (i : Fin d) :
    coord (intVec k) i = (k i : ℝ) := by
  rfl

@[simp] private lemma coord_sub_intVec {d : ℕ} (x : E d)
    (k : Fin d → ℤ) (i : Fin d) :
    coord (x - intVec k) i = coord x i - (k i : ℝ) := by
  calc
    coord (x - intVec k) i = coord x i - coord (intVec k) i := by
      simp [coord]
    _ = coord x i - (k i : ℝ) := by
      rw [coord_intVec]

@[simp] lemma coord_natVec {d : ℕ} (k : Fin d → ℕ) (i : Fin d) :
    coord (natVec k) i = (k i : ℝ) := by
  rfl

lemma continuous_coord {d : ℕ} (i : Fin d) :
    Continuous (fun x : E d => coord x i) := by
  simpa [coord] using
    (PiLp.continuous_apply (p := (2 : ℝ≥0∞)) (β := fun _ : Fin d => ℝ) i)

private lemma homeomorph_symm_eq_toE {d : ℕ} (x : Fin d → ℝ) :
    ((PiLp.homeomorph (p := (2 : ℝ≥0∞)) (β := fun _ : Fin d => ℝ)).symm x : E d) =
      toE x := by
  apply PiLp.ext
  intro i
  change
    (PiLp.homeomorph (p := (2 : ℝ≥0∞)) (β := fun _ : Fin d => ℝ))
      ((PiLp.homeomorph (p := (2 : ℝ≥0∞)) (β := fun _ : Fin d => ℝ)).symm x) i =
    x i
  exact congrArg (fun f : Fin d → ℝ => f i)
    ((PiLp.homeomorph (p := (2 : ℝ≥0∞)) (β := fun _ : Fin d => ℝ)).apply_symm_apply x)

theorem intVec_injective {d : ℕ} :
    Function.Injective (intVec : (Fin d → ℤ) → E d) := by
  intro k l hkl
  funext i
  apply Int.cast_injective (α := ℝ)
  exact congrArg (fun x : E d => coord x i) hkl

theorem integerLattice_closed (d : ℕ) :
    IsClosed (integerLattice d) := by
  let e : E d ≃ₜ (Fin d → ℝ) :=
    PiLp.homeomorph (p := (2 : ℝ≥0∞)) (β := fun _ : Fin d => ℝ)
  let raw : (Fin d → ℤ) → (Fin d → ℝ) := fun k i => (k i : ℝ)
  have hraw_closed : IsClosed (Set.range raw) := by
    let S : Set (Fin d → ℝ) :=
      Set.univ.pi fun _ : Fin d => Set.range ((↑) : ℤ → ℝ)
    have hS_closed : IsClosed S := by
      simpa [S] using
      (Topology.IsClosedEmbedding.piMap
        (f := fun _ : Fin d => ((↑) : ℤ → ℝ))
        (fun _ : Fin d => Int.isClosedEmbedding_coe_real)).isClosed_range
    have hraw_eq : Set.range raw = S := by
      ext x
      constructor
      · rintro ⟨k, rfl⟩ i -
        exact ⟨k i, rfl⟩
      · intro hx
        have hx' : ∀ i : Fin d, ∃ z : ℤ, (z : ℝ) = x i := fun i => hx i trivial
        choose k hk using hx'
        exact ⟨k, funext hk⟩
    exact hraw_eq.symm ▸ hS_closed
  have h_esymm_raw (k : Fin d → ℤ) : e.symm (raw k) = intVec k := by
    apply PiLp.ext
    intro i
    change e (e.symm (raw k)) i = raw k i
    exact congrArg (fun f : Fin d → ℝ => f i) (e.apply_symm_apply (raw k))
  have h_lattice : integerLattice d = e.symm '' Set.range raw := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨raw k, ⟨k, rfl⟩, (h_esymm_raw k).symm⟩
    · rintro ⟨v, ⟨k, rfl⟩, rfl⟩
      exact ⟨k, h_esymm_raw k⟩
  rw [h_lattice]
  exact e.symm.isClosed_image.mpr hraw_closed

theorem integerLattice_discrete_localFinite {d : ℕ} (R : ℝ) :
    ((integerLattice d) ∩ Metric.closedBall (0 : E d) R).Finite := by
  let e : E d ≃ₜ (Fin d → ℝ) :=
    PiLp.homeomorph (p := (2 : ℝ≥0∞)) (β := fun _ : Fin d => ℝ)
  let raw : (Fin d → ℤ) → (Fin d → ℝ) := fun k i => (k i : ℝ)
  have hraw_emb : Topology.IsClosedEmbedding raw := by
    have hmap :
        Topology.IsClosedEmbedding (Pi.map fun _ : Fin d => ((↑) : ℤ → ℝ)) :=
      Topology.IsClosedEmbedding.piMap
        (f := fun _ : Fin d => ((↑) : ℤ → ℝ))
        (fun _ : Fin d => Int.isClosedEmbedding_coe_real)
    convert hmap using 1
    funext k i
    rfl
  have hint_emb : Topology.IsClosedEmbedding (intVec : (Fin d → ℤ) → E d) := by
    have hcomp : Topology.IsClosedEmbedding (e.symm ∘ raw) :=
      e.symm.isClosedEmbedding.comp hraw_emb
    convert hcomp using 1
    funext k
    exact (homeomorph_symm_eq_toE (d := d) (raw k)).symm
  let pre : Set (Fin d → ℤ) :=
    (intVec : (Fin d → ℤ) → E d) ⁻¹' Metric.closedBall (0 : E d) R
  have hpre_compact : IsCompact pre :=
    hint_emb.isCompact_preimage (isCompact_closedBall (0 : E d) R)
  have hpre_finite : pre.Finite := hpre_compact.finite_of_discrete
  refine (hpre_finite.image (intVec : (Fin d → ℤ) → E d)).subset ?_
  intro x hx
  rcases hx.1 with ⟨k, rfl⟩
  exact ⟨k, hx.2, rfl⟩

theorem measurableSet_unitCube (d : ℕ) :
    MeasurableSet (unitCube d) := by
  have hclosed : IsClosed (unitCube d) := by
    rw [unitCube]
    convert (isClosed_iInter fun i : Fin d =>
      isClosed_Icc.preimage (continuous_coord i) :
        IsClosed (⋂ i : Fin d, {x : E d | coord x i ∈ Set.Icc (0 : ℝ) 1})) using 1
    ext x
    simp [Set.mem_iInter, Set.mem_Icc]
  exact hclosed.measurableSet

theorem volume_unitCube_lt_top (d : ℕ) :
    volume (unitCube d) < ∞ := by
  let e : E d ≃ₜ (Fin d → ℝ) :=
    PiLp.homeomorph (p := (2 : ℝ≥0∞)) (β := fun _ : Fin d => ℝ)
  let rawCube : Set (Fin d → ℝ) :=
    Set.univ.pi fun _ : Fin d => Set.Icc (0 : ℝ) 1
  have hraw_compact : IsCompact rawCube := by
    simpa [rawCube] using
      (isCompact_univ_pi fun _ : Fin d => (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)))
  have hcube : unitCube d = e ⁻¹' rawCube := by
    ext x
    change (∀ i : Fin d, 0 ≤ coord x i ∧ coord x i ≤ 1) ↔ e x ∈ rawCube
    simp only [rawCube, Set.mem_pi, Set.mem_univ, Set.mem_Icc]
    constructor
    · intro hx i _
      exact hx i
    · intro hx i
      exact hx i trivial
  have hcube_compact : IsCompact (unitCube d) := by
    rw [hcube]
    exact e.isCompact_preimage.mpr hraw_compact
  exact hcube_compact.measure_lt_top

theorem AContextHD.finite_volume {d : ℕ} {A : Set (E d)}
    (hA : AContextHD d A) :
    volume A < ∞ := by
  exact lt_of_le_of_lt (measure_mono hA.subset_unitCube) (volume_unitCube_lt_top d)

theorem spectrum_eq_iUnion_latticeTranslate {d : ℕ} (A : Set (E d)) :
    spectrum A = Set.iUnion fun k : Fin d → ℤ => latticeTranslate A k := by
  ext xi
  simp [spectrum]

theorem measurableSet_latticeTranslate {d : ℕ} {A : Set (E d)}
    (hA : MeasurableSet A) (k : Fin d → ℤ) :
    MeasurableSet (latticeTranslate A k) := by
  change MeasurableSet ((fun xi : E d => xi - intVec k) ⁻¹' A)
  exact hA.preimage ((continuous_id.sub continuous_const).measurable)

theorem AContextHD.measurableSet_spectrum {d : ℕ} {A : Set (E d)}
    (hA : AContextHD d A) :
    MeasurableSet (spectrum A) := by
  rw [spectrum_eq_iUnion_latticeTranslate]
  exact MeasurableSet.iUnion fun k => measurableSet_latticeTranslate hA.measurable k

theorem mem_spectrum_of_mem_translate {d : ℕ} {A : Set (E d)} {t : E d}
    (ht : t ∈ A) (k : Fin d → ℤ) :
    t + intVec k ∈ spectrum A := by
  refine ⟨k, ?_⟩
  simpa [latticeTranslate] using ht

private lemma volume_coord_eq_zero {d : ℕ} (i : Fin d) (c : ℝ) :
    volume ({x : E d | coord x i = c}) = 0 := by
  have hpre :
      ({x : E d | coord x i = c} : Set (E d)) =
        (WithLp.ofLp : E d → Fin d → ℝ) ⁻¹'
          ({f : Fin d → ℝ | f i = c}) := by
    ext x
    rfl
  rw [hpre]
  exact
    (PiLp.volume_preserving_ofLp (ι := Fin d)).quasiMeasurePreserving.preimage_null
      (by
        simpa [MeasureTheory.volume_pi] using
          (MeasureTheory.Measure.pi_hyperplane
            (fun _ : Fin d => (volume : Measure ℝ)) i c))

theorem ae_disjoint_lattice_translates {d : ℕ} {A : Set (E d)}
    (hA_sub : A ⊆ unitCube d)
    {k l : Fin d → ℤ} (hkl : k ≠ l) :
    volume (latticeTranslate A k ∩ latticeTranslate A l) = 0 := by
  -- Reduce overlap to coordinate boundary hyperplanes.
  classical
  obtain ⟨i, hi⟩ : ∃ i : Fin d, k i ≠ l i := by
    by_contra h
    apply hkl
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  rcases lt_or_gt_of_ne hi with hlt | hgt
  · refine measure_mono_null (t := {x : E d | coord x i = (l i : ℝ)}) ?_
      (volume_coord_eq_zero i (l i : ℝ))
    intro x hx
    have hxkA : x - intVec k ∈ A := hx.1
    have hxlA : x - intVec l ∈ A := hx.2
    have hxkC : x - intVec k ∈ unitCube d := hA_sub hxkA
    have hxlC : x - intVec l ∈ unitCube d := hA_sub hxlA
    have hxkI : 0 ≤ coord x i - (k i : ℝ) ∧ coord x i - (k i : ℝ) ≤ 1 := by
      simpa using hxkC i
    have hxlI : 0 ≤ coord x i - (l i : ℝ) ∧ coord x i - (l i : ℝ) ≤ 1 := by
      simpa using hxlC i
    have hkl_succ : k i + 1 ≤ l i := Int.add_one_le_iff.mpr hlt
    have hkl_real : (k i : ℝ) + 1 ≤ (l i : ℝ) := by exact_mod_cast hkl_succ
    show coord x i = (l i : ℝ)
    linarith
  · refine measure_mono_null (t := {x : E d | coord x i = (k i : ℝ)}) ?_
      (volume_coord_eq_zero i (k i : ℝ))
    intro x hx
    have hxkA : x - intVec k ∈ A := hx.1
    have hxlA : x - intVec l ∈ A := hx.2
    have hxkC : x - intVec k ∈ unitCube d := hA_sub hxkA
    have hxlC : x - intVec l ∈ unitCube d := hA_sub hxlA
    have hxkI : 0 ≤ coord x i - (k i : ℝ) ∧ coord x i - (k i : ℝ) ≤ 1 := by
      simpa using hxkC i
    have hxlI : 0 ≤ coord x i - (l i : ℝ) ∧ coord x i - (l i : ℝ) ≤ 1 := by
      simpa using hxlC i
    have hlk_succ : l i + 1 ≤ k i := Int.add_one_le_iff.mpr hgt
    have hlk_real : (l i : ℝ) + 1 ≤ (k i : ℝ) := by exact_mod_cast hlk_succ
    show coord x i = (k i : ℝ)
    linarith

private lemma sobolevPower_nonneg {d : ℕ} (alpha : ℝ) (xi : E d) :
    0 ≤ sobolevPower alpha xi := by
  unfold sobolevPower
  split_ifs
  · norm_num
  · exact Real.rpow_nonneg (norm_nonneg xi) _

lemma one_le_sobolevWeight {d : ℕ} (alpha : ℝ) (xi : E d) :
    1 ≤ sobolevWeight alpha xi := by
  have hpow : 0 ≤ sobolevPower alpha xi := sobolevPower_nonneg alpha xi
  unfold sobolevWeight
  linarith

lemma sobolevWeight_pos {d : ℕ} (alpha : ℝ) (xi : E d) :
    0 < sobolevWeight alpha xi := by
  exact zero_lt_one.trans_le (one_le_sobolevWeight alpha xi)

lemma sobolevWeight_nonneg {d : ℕ} (alpha : ℝ) (xi : E d) :
    0 ≤ sobolevWeight alpha xi := by
  exact (sobolevWeight_pos alpha xi).le

lemma sobolevWeight_zero {d : ℕ} (xi : E d) :
    sobolevWeight (d := d) 0 xi = 2 := by
  norm_num [sobolevWeight, sobolevPower]

private lemma volume_restrict_spectrum_le_weightedMeasure {d : ℕ}
    {A : Set (E d)} {alpha : ℝ} :
    volume.restrict (spectrum A) ≤ weightedMeasure alpha A := by
  calc
    volume.restrict (spectrum A)
        = (volume.restrict (spectrum A)).withDensity
            (fun _ : E d => (1 : ℝ≥0∞)) :=
            (withDensity_one (μ := volume.restrict (spectrum A))).symm
    _ ≤ weightedMeasure alpha A := by
        unfold weightedMeasure
        refine
          withDensity_mono
            (μ := volume.restrict (spectrum A))
            (f := fun _ : E d => (1 : ℝ≥0∞))
            (g := fun xi : E d => ENNReal.ofReal (sobolevWeight alpha xi))
            (Eventually.of_forall fun xi => ?_)
        simpa using
          (ENNReal.ofReal_le_ofReal (one_le_sobolevWeight alpha xi))

theorem exists_translateWeightConstant {d : ℕ} (_hd_pos : 0 < d)
    (halpha : AlphaLeDimHalf d alpha) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ t : E d, t ∈ unitCube d →
      ∀ k : Fin d → ℕ,
        (∀ i : Fin d, 1 ≤ k i) →
        sobolevWeight alpha (t + natVec k)
          ≤ C * sobolevWeight alpha (natVec k) := by
  -- Compare `‖t + k‖` and `‖k‖` uniformly for `t ∈ [0,1]^d`.
  let C : ℝ := 1 + Real.rpow 2 (2 * alpha)
  have hC_pos : 0 < C := by
    have hpow_nonneg : 0 ≤ Real.rpow 2 (2 * alpha) :=
      Real.rpow_nonneg (by norm_num) _
    exact zero_lt_one.trans_le (by dsimp [C]; exact le_add_of_nonneg_right hpow_nonneg)
  refine ⟨C, hC_pos, ?_⟩
  intro t ht k hk
  have hnorm_t_le : ‖t‖ ≤ ‖natVec k‖ := by
    rw [← sq_le_sq₀ (norm_nonneg t) (norm_nonneg (natVec k))]
    calc
      ‖t‖ ^ 2 = ∑ i : Fin d, ‖coord t i‖ ^ 2 := by
        simp [coord, PiLp.norm_sq_eq_of_L2]
      _ ≤ ∑ i : Fin d, ‖coord (natVec k) i‖ ^ 2 := by
        refine Finset.sum_le_sum ?_
        intro i _hi
        have hti : 0 ≤ coord t i ∧ coord t i ≤ 1 := ht i
        have hki : (1 : ℝ) ≤ (k i : ℝ) := by exact_mod_cast hk i
        have hcoord_le : ‖coord t i‖ ≤ ‖coord (natVec k) i‖ := by
          rw [coord_natVec]
          rw [Real.norm_eq_abs, abs_of_nonneg hti.1]
          rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
          exact hti.2.trans hki
        exact pow_le_pow_left₀ (norm_nonneg _) hcoord_le 2
      _ = ‖natVec k‖ ^ 2 := by
        simp [coord, PiLp.norm_sq_eq_of_L2]
  have hnorm_sum_le : ‖t + natVec k‖ ≤ 2 * ‖natVec k‖ := by
    calc
      ‖t + natVec k‖ ≤ ‖t‖ + ‖natVec k‖ := norm_add_le t (natVec k)
      _ ≤ 2 * ‖natVec k‖ := by linarith
  have hp_nonneg : 0 ≤ 2 * alpha := by linarith [halpha.nonneg]
  have hpow_le :
      sobolevPower alpha (t + natVec k)
        ≤ Real.rpow 2 (2 * alpha) * sobolevPower alpha (natVec k) := by
    by_cases hzero : alpha = 0
    · simp [sobolevPower, hzero]
    · have hbase_nonneg : 0 ≤ 2 * ‖natVec k‖ := by positivity
      have hraw :
          Real.rpow ‖t + natVec k‖ (2 * alpha)
            ≤ Real.rpow (2 * ‖natVec k‖) (2 * alpha) :=
        Real.rpow_le_rpow (norm_nonneg _) hnorm_sum_le hp_nonneg
      have hmul :
          Real.rpow (2 * ‖natVec k‖) (2 * alpha) =
            Real.rpow 2 (2 * alpha) * Real.rpow ‖natVec k‖ (2 * alpha) := by
        simpa using
          (Real.mul_rpow (x := (2 : ℝ)) (y := ‖natVec k‖)
            (z := 2 * alpha) (by norm_num) (norm_nonneg _))
      calc
        sobolevPower alpha (t + natVec k)
            = Real.rpow ‖t + natVec k‖ (2 * alpha) := by
                simp [sobolevPower, hzero]
        _ ≤ Real.rpow (2 * ‖natVec k‖) (2 * alpha) := hraw
        _ = Real.rpow 2 (2 * alpha) *
              Real.rpow ‖natVec k‖ (2 * alpha) := hmul
        _ = Real.rpow 2 (2 * alpha) * sobolevPower alpha (natVec k) := by
              simp [sobolevPower, hzero]
  unfold sobolevWeight
  have hM_nonneg : 0 ≤ Real.rpow 2 (2 * alpha) :=
    Real.rpow_nonneg (by norm_num) _
  have hpow_k_nonneg : 0 ≤ sobolevPower alpha (natVec k) :=
    sobolevPower_nonneg alpha (natVec k)
  dsimp [C]
  calc
    1 + sobolevPower alpha (t + natVec k)
        ≤ 1 + Real.rpow 2 (2 * alpha) * sobolevPower alpha (natVec k) := by
          simpa [add_comm] using add_le_add_left hpow_le 1
    _ ≤ (1 + Real.rpow 2 (2 * alpha)) *
          (1 + sobolevPower alpha (natVec k)) := by
          nlinarith [mul_nonneg hM_nonneg hpow_k_nonneg]

theorem weighted_memLp_volume_of_supported {d : ℕ}
    {A : Set (E d)} {alpha : ℝ} {P : E d → ℂ}
    (hA : AContextHD d A)
    (hP_meas : AEStronglyMeasurable P volume)
    (hP_supp : SupportedInSpectrumAE A P)
    (hP_weighted : MemLp P 2 (weightedMeasure alpha A)) :
    MemLp P 2 volume := by
  have hP_restrict : MemLp P 2 (volume.restrict (spectrum A)) :=
    MemLp.mono_measure
      (volume_restrict_spectrum_le_weightedMeasure (A := A) (alpha := alpha))
      hP_weighted
  have hP_indicator : MemLp ((spectrum A).indicator P) 2 volume :=
    (memLp_indicator_iff_restrict hA.measurableSet_spectrum).2 hP_restrict
  have hP_indicator_ae : (spectrum A).indicator P =ᵐ[volume] P := by
    filter_upwards [hP_supp] with xi hxi
    by_cases hmem : xi ∈ spectrum A
    · simp [hmem]
    · simp [hmem, hxi hmem]
  refine ⟨hP_meas, ?_⟩
  exact (hP_indicator.ae_eq hP_indicator_ae).2

private lemma eLpNorm_volume_le_weighted_of_supported {d : ℕ}
    {A : Set (E d)} {alpha : ℝ} {P : E d → ℂ}
    (hA : AContextHD d A)
    (hP_supp : SupportedInSpectrumAE A P) :
    eLpNorm P 2 volume ≤ eLpNorm P 2 (weightedMeasure alpha A) := by
  have hP_indicator_ae : P =ᵐ[volume] (spectrum A).indicator P := by
    filter_upwards [hP_supp] with xi hxi
    by_cases hmem : xi ∈ spectrum A
    · simp [hmem]
    · simp [hmem, hxi hmem]
  calc
    eLpNorm P 2 volume
        = eLpNorm ((spectrum A).indicator P) 2 volume :=
            eLpNorm_congr_ae hP_indicator_ae
    _ = eLpNorm P 2 (volume.restrict (spectrum A)) :=
            eLpNorm_indicator_eq_eLpNorm_restrict hA.measurableSet_spectrum
    _ ≤ eLpNorm P 2 (weightedMeasure alpha A) :=
            eLpNorm_mono_measure P
              (volume_restrict_spectrum_le_weightedMeasure (A := A) (alpha := alpha))

theorem weightedL2_tendsto_to_global_L2_tendsto {d : ℕ}
    {A : Set (E d)} {alpha : ℝ}
    {F : ℕ → E d → ℂ} {H : E d → ℂ}
    (hA : AContextHD d A)
    (hDiff : ∀ n, WeightedFourierSide alpha A (fun xi => F n xi - H xi))
    (h_weighted :
      Tendsto
        (fun n => eLpNorm (fun xi => F n xi - H xi)
          2 (weightedMeasure alpha A))
        atTop (nhds 0)) :
    Tendsto
      (fun n => eLpNorm (fun xi => F n xi - H xi) 2 volume)
      atTop (nhds 0) := by
  refine
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      (g := fun _ : ℕ => (0 : ℝ≥0∞))
      (h := fun n => eLpNorm (fun xi => F n xi - H xi)
        2 (weightedMeasure alpha A))
      tendsto_const_nhds h_weighted ?_ ?_
  · intro n
    exact bot_le
  · intro n
    exact
      eLpNorm_volume_le_weighted_of_supported
        (A := A) (alpha := alpha) hA (hDiff n).supported

private lemma inverseFourierIntegral_eq_fourierInv {d : ℕ} (P : E d → ℂ) :
    (fun x : E d => inverseFourierIntegral P x) = (𝓕⁻ P : E d → ℂ) := by
  funext x
  rw [inverseFourierIntegral, Real.fourierInv_eq']
  simp [fourierChar, exp2piI, smul_eq_mul, mul_comm, mul_assoc]

private lemma continuous_inverseFourierIntegral_of_integrable {d : ℕ}
    {P : E d → ℂ}
    (hP_int : Integrable P volume) :
    Continuous (fun x : E d => inverseFourierIntegral P x) := by
  have hFourier : Continuous (𝓕 P : E d → ℂ) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hP_int
  have hInv : Continuous (𝓕⁻ P : E d → ℂ) := by
    rw [show (𝓕⁻ P : E d → ℂ) = (fun x : E d => 𝓕 P (-x)) by
      funext x
      exact Real.fourierInv_eq_fourier_neg P x]
    exact hFourier.comp continuous_neg
  simpa [inverseFourierIntegral_eq_fourierInv P] using hInv

private lemma fourierInv_toLp_ae_eq_fourierInv_of_integrable_memL2 {d : ℕ}
    {P : E d → ℂ}
    (hP_int : Integrable P volume)
    (hP_L2 : MemLp P 2 volume) :
    (((𝓕⁻ (hP_L2.toLp P : Lp (α := E d) ℂ 2 volume)) :
        Lp (α := E d) ℂ 2 volume) : E d → ℂ)
      =ᵐ[volume] (𝓕⁻ P : E d → ℂ) := by
  let u : Lp (α := E d) ℂ 2 volume :=
    𝓕⁻ (hP_L2.toLp P : Lp (α := E d) ℂ 2 volume)
  have hu_loc : LocallyIntegrable (u : E d → ℂ) volume :=
    (Lp.memLp u).locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hcont : Continuous (𝓕⁻ P : E d → ℂ) := by
    simpa [inverseFourierIntegral_eq_fourierInv P] using
      (continuous_inverseFourierIntegral_of_integrable hP_int)
  have hFourier_loc : LocallyIntegrable (𝓕⁻ P : E d → ℂ) volume :=
    hcont.locallyIntegrable
  refine ae_eq_of_integral_contDiff_smul_eq hu_loc hFourier_loc ?_
  intro g hg_smooth hg_cpt
  let φ : 𝓢(E d, ℂ) :=
    (hg_cpt.comp_left rfl).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp hg_smooth)
  have hswap :
      ∫ ξ : E d, (𝓕⁻ P ξ) • φ ξ ∂volume =
        ∫ x : E d, P x • (𝓕⁻ (φ : E d → ℂ) x) ∂volume := by
    simpa [Real.fourierInv_eq, VectorFourier.fourierIntegral,
      innerₗ_apply_apply, real_inner_comm, mul_comm] using
      (VectorFourier.integral_fourierIntegral_smul_eq_flip
        (L := -innerₗ (E d)) (μ := volume) (ν := volume) (f := P) (g := φ)
        Real.continuous_fourierChar continuous_inner.neg
        hP_int (φ.integrable (μ := volume)))
  calc
    ∫ x : E d, g x • u x ∂volume
        = ∫ x : E d, φ x • u x ∂volume := by
            apply integral_congr_ae
            filter_upwards with x
            simp [φ]
    _ = (u : TemperedDistribution (E d) ℂ) φ := by
            rw [MeasureTheory.Lp.toTemperedDistribution_apply]
    _ =
        (𝓕⁻ ((hP_L2.toLp P : Lp (α := E d) ℂ 2 volume) :
          TemperedDistribution (E d) ℂ)) φ := by
            change
              ((((𝓕⁻ (hP_L2.toLp P : Lp (α := E d) ℂ 2 volume)) :
                    Lp (α := E d) ℂ 2 volume) : TemperedDistribution (E d) ℂ) φ)
                =
              (𝓕⁻ ((hP_L2.toLp P : Lp (α := E d) ℂ 2 volume) :
                TemperedDistribution (E d) ℂ)) φ
            rw [← MeasureTheory.Lp.fourierInv_toTemperedDistribution_eq
              (hP_L2.toLp P : Lp (α := E d) ℂ 2 volume)]
    _ =
        ((hP_L2.toLp P : Lp (α := E d) ℂ 2 volume) :
          TemperedDistribution (E d) ℂ) (𝓕⁻ φ) := by
            rw [TemperedDistribution.fourierInv_apply]
    _ =
        ∫ x : E d, (𝓕⁻ φ) x •
          ((hP_L2.toLp P : Lp (α := E d) ℂ 2 volume) : E d → ℂ) x ∂volume := by
            rw [MeasureTheory.Lp.toTemperedDistribution_apply]
    _ = ∫ x : E d, (𝓕⁻ φ) x • P x ∂volume := by
            apply integral_congr_ae
            filter_upwards [hP_L2.coeFn_toLp] with x hx
            rw [hx]
    _ = ∫ x : E d, P x • (𝓕⁻ (φ : E d → ℂ) x) ∂volume := by
            apply integral_congr_ae
            filter_upwards with x
            simp [SchwartzMap.fourierInv_coe, mul_comm]
    _ = ∫ x : E d, (𝓕⁻ P x) • φ x ∂volume := hswap.symm
    _ = ∫ x : E d, φ x • (𝓕⁻ P x) ∂volume := by
            apply integral_congr_ae
            filter_upwards with x
            simp [mul_comm]
    _ = ∫ x : E d, g x • (𝓕⁻ P : E d → ℂ) x ∂volume := by
            apply integral_congr_ae
            filter_upwards with x
            simp [φ]

private lemma fourierInv_toLp_eq_inverseFourierIntegral_of_integrable_memL2 {d : ℕ}
    {P : E d → ℂ}
    (hP_int : Integrable P volume)
    (hP_L2 : MemLp P 2 volume) :
    ∃ hF : MemLp (fun x : E d => inverseFourierIntegral P x) 2 volume,
      (𝓕⁻ (hP_L2.toLp P : Lp (α := E d) ℂ 2 volume) :
          Lp (α := E d) ℂ 2 volume)
        = hF.toLp (fun x : E d => inverseFourierIntegral P x) := by
  let u : Lp (α := E d) ℂ 2 volume :=
    𝓕⁻ (hP_L2.toLp P : Lp (α := E d) ℂ 2 volume)
  have hAeFourier : (u : E d → ℂ) =ᵐ[volume] (𝓕⁻ P : E d → ℂ) := by
    simpa [u] using
      fourierInv_toLp_ae_eq_fourierInv_of_integrable_memL2 hP_int hP_L2
  have hAe : (u : E d → ℂ) =ᵐ[volume] fun x => inverseFourierIntegral P x := by
    simpa [inverseFourierIntegral_eq_fourierInv P] using hAeFourier
  have hF : MemLp (fun x : E d => inverseFourierIntegral P x) 2 volume :=
    MemLp.ae_eq hAe (Lp.memLp u)
  refine ⟨hF, ?_⟩
  calc
    (𝓕⁻ (hP_L2.toLp P : Lp (α := E d) ℂ 2 volume) :
        Lp (α := E d) ℂ 2 volume) = u := rfl
    _ = (Lp.memLp u).toLp (u : E d → ℂ) :=
        (Lp.toLp_coeFn u (Lp.memLp u)).symm
    _ = hF.toLp (fun x : E d => inverseFourierIntegral P x) :=
        MemLp.toLp_congr (Lp.memLp u) hF hAe

theorem continuousInvFourierRep_of_integrable_inverseIntegral {d : ℕ}
    {P f : E d → ℂ}
    (hP_int : Integrable P volume)
    (hP_L2 : MemLp P 2 volume)
    (hf_cont : Continuous f)
    (hf_def : ∀ x, f x = inverseFourierIntegral P x) :
    ContinuousInvFourierRep P f := by
  rcases fourierInv_toLp_eq_inverseFourierIntegral_of_integrable_memL2
      hP_int hP_L2 with ⟨hF, hEq⟩
  have hAe :
      (fun x : E d => inverseFourierIntegral P x) =ᵐ[volume] f :=
    Filter.Eventually.of_forall fun x => (hf_def x).symm
  have hf_mem : MemLp f 2 volume :=
    MemLp.ae_eq hAe hF
  refine ⟨hP_L2, hf_mem, hf_cont, ?_⟩
  calc
    (𝓕⁻ (hP_L2.toLp P) : Lp (α := E d) ℂ 2 volume)
        = hF.toLp (fun x : E d => inverseFourierIntegral P x) := hEq
    _ = hf_mem.toLp f :=
        MemLp.toLp_congr hF hf_mem hAe

theorem ContinuousInvFourierRep.ae_eq_inverse {d : ℕ}
    {P f : E d → ℂ} (h : ContinuousInvFourierRep P f) :
    (((𝓕⁻ (h.P_memL2.toLp P) :
        Lp (α := E d) ℂ 2 volume) : E d → ℂ) =ᵐ[volume] f) := by
  rw [h.inv_eq_l2]
  exact h.f_memL2.coeFn_toLp

theorem SupportedInSpectrumAE.smul {d : ℕ}
    {A : Set (E d)} {P : E d → ℂ}
    (c : ℂ) (hP : SupportedInSpectrumAE A P) :
    SupportedInSpectrumAE A (fun xi => c * P xi) := by
  filter_upwards [hP] with xi hxi hxi_not_mem
  simp [hxi hxi_not_mem]

theorem SupportedInSpectrumAE.add {d : ℕ}
    {A : Set (E d)} {P Q : E d → ℂ}
    (hP : SupportedInSpectrumAE A P) (hQ : SupportedInSpectrumAE A Q) :
    SupportedInSpectrumAE A (fun xi => P xi + Q xi) := by
  filter_upwards [hP, hQ] with xi hPxi hQxi hxi_not_mem
  simp [hPxi hxi_not_mem, hQxi hxi_not_mem]

theorem WeightedFourierSide.smul {d : ℕ}
    {A : Set (E d)} {alpha : ℝ} {P : E d → ℂ}
    (c : ℂ) (hP : WeightedFourierSide alpha A P) :
    WeightedFourierSide alpha A (fun xi => c * P xi) := by
  have hcP : (c • P) = (fun xi : E d => c * P xi) := by
    ext xi
    simp [Pi.smul_apply, smul_eq_mul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [hcP] using hP.aestronglyMeasurable.const_smul c
  · exact SupportedInSpectrumAE.smul c hP.supported
  · simpa [hcP] using hP.weightedMemLp.const_smul c
  · simpa [hcP] using hP.memL2.const_smul c

theorem WeightedFourierSide.add {d : ℕ}
    {A : Set (E d)} {alpha : ℝ} {P Q : E d → ℂ}
    (hP : WeightedFourierSide alpha A P)
    (hQ : WeightedFourierSide alpha A Q) :
    WeightedFourierSide alpha A (fun xi => P xi + Q xi) := by
  have hPQ : (P + Q) = (fun xi : E d => P xi + Q xi) := by
    ext xi
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [hPQ] using hP.aestronglyMeasurable.add hQ.aestronglyMeasurable
  · exact SupportedInSpectrumAE.add hP.supported hQ.supported
  · simpa [hPQ] using hP.weightedMemLp.add hQ.weightedMemLp
  · simpa [hPQ] using hP.memL2.add hQ.memL2

theorem ContinuousInvFourierRep.smul {d : ℕ}
    {P f : E d → ℂ}
    (c : ℂ) (h : ContinuousInvFourierRep P f) :
    ContinuousInvFourierRep (fun xi => c * P xi) (fun x => c * f x) := by
  have hcP : (c • P) = (fun xi : E d => c * P xi) := by
    ext xi
    simp [Pi.smul_apply, smul_eq_mul]
  have hcf : (c • f) = (fun x : E d => c * f x) := by
    ext x
    simp [Pi.smul_apply, smul_eq_mul]
  have hPmem : MemLp (fun xi : E d => c * P xi) 2 volume := by
    simpa [hcP] using h.P_memL2.const_smul c
  have hfmem : MemLp (fun x : E d => c * f x) 2 volume := by
    simpa [hcf] using h.f_memL2.const_smul c
  refine ⟨hPmem, hfmem, continuous_const.mul h.f_cont, ?_⟩
  have htoLpP :
      hPmem.toLp (fun xi : E d => c * P xi) =
        c • h.P_memL2.toLp P := by
    simpa [hcP] using h.P_memL2.toLp_const_smul c
  have htoLpf :
      hfmem.toLp (fun x : E d => c * f x) =
        c • h.f_memL2.toLp f := by
    simpa [hcf] using h.f_memL2.toLp_const_smul c
  rw [htoLpP, htoLpf, ← h.inv_eq_l2]
  simp

theorem ContinuousInvFourierRep.add {d : ℕ}
    {P Q f g : E d → ℂ}
    (hP : ContinuousInvFourierRep P f)
    (hQ : ContinuousInvFourierRep Q g) :
    ContinuousInvFourierRep (fun xi => P xi + Q xi) (fun x => f x + g x) := by
  have hPQ : (P + Q) = (fun xi : E d => P xi + Q xi) := by
    ext xi
    rfl
  have hfg : (f + g) = (fun x : E d => f x + g x) := by
    ext x
    rfl
  have hPmem : MemLp (fun xi : E d => P xi + Q xi) 2 volume := by
    simpa [hPQ] using hP.P_memL2.add hQ.P_memL2
  have hfmem : MemLp (fun x : E d => f x + g x) 2 volume := by
    simpa [hfg] using hP.f_memL2.add hQ.f_memL2
  refine ⟨hPmem, hfmem, hP.f_cont.add hQ.f_cont, ?_⟩
  have htoLpP :
      hPmem.toLp (fun xi : E d => P xi + Q xi) =
        hP.P_memL2.toLp P + hQ.P_memL2.toLp Q := by
    simpa [hPQ] using hP.P_memL2.toLp_add hQ.P_memL2
  have htoLpf :
      hfmem.toLp (fun x : E d => f x + g x) =
        hP.f_memL2.toLp f + hQ.f_memL2.toLp g := by
    simpa [hfg] using hP.f_memL2.toLp_add hQ.f_memL2
  rw [htoLpP, htoLpf, ← hP.inv_eq_l2, ← hQ.inv_eq_l2]
  simp

theorem WeightedFourierWitness.zero {d : ℕ}
    {A : Set (E d)} {alpha : ℝ} :
    WeightedFourierWitness alpha A (fun _ : E d => 0) (fun _ : E d => 0) := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · fun_prop
    · exact Filter.Eventually.of_forall fun _ _ => rfl
    · simp [weightedMeasure]
    · simp
  · refine ⟨?_, ?_, ?_, ?_⟩
    · simp
    · simp
    · fun_prop
    · change
        (𝓕⁻ ((MemLp.zero' (α := E d) (ε := ℂ) (μ := volume) (p := 2)).toLp
          (0 : E d → ℂ)) : Lp (α := E d) ℂ 2 volume) =
        (MemLp.zero' (α := E d) (ε := ℂ) (μ := volume) (p := 2)).toLp
          (0 : E d → ℂ)
      rw [MemLp.toLp_zero]
      simp

theorem WeightedFourierWitness.smul {d : ℕ}
    {A : Set (E d)} {alpha : ℝ} {f P : E d → ℂ}
    (c : ℂ) (h : WeightedFourierWitness alpha A f P) :
    WeightedFourierWitness alpha A (fun x => c * f x) (fun xi => c * P xi) := by
  exact ⟨WeightedFourierSide.smul c h.side, ContinuousInvFourierRep.smul c h.invRep⟩

theorem WeightedFourierWitness.add {d : ℕ}
    {A : Set (E d)} {alpha : ℝ} {f g P Q : E d → ℂ}
    (hP : WeightedFourierWitness alpha A f P)
    (hQ : WeightedFourierWitness alpha A g Q) :
    WeightedFourierWitness alpha A (fun x => f x + g x) (fun xi => P xi + Q xi) := by
  exact ⟨WeightedFourierSide.add hP.side hQ.side, ContinuousInvFourierRep.add hP.invRep hQ.invRep⟩

theorem WeightedFourierWitness.finset_sum {ι : Type*} [DecidableEq ι]
    {d : ℕ} {A : Set (E d)} {alpha : ℝ}
    (s : Finset ι) {f P : ι → E d → ℂ}
    (h : ∀ i ∈ s, WeightedFourierWitness alpha A (f i) (P i)) :
    WeightedFourierWitness alpha A
      (fun x => s.sum (fun i => f i x))
      (fun xi => s.sum (fun i => P i xi)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using (WeightedFourierWitness.zero (A := A) (alpha := alpha))
  | insert a s ha ih =>
      simpa [Finset.sum_insert, ha] using
        WeightedFourierWitness.add (h a (by simp))
          (ih fun i hi => h i (by simp [hi]))

theorem WeightedFourierWitness.continuous {d : ℕ}
    {A : Set (E d)} {alpha : ℝ} {f P : E d → ℂ}
    (h : WeightedFourierWitness alpha A f P) :
    Continuous f := by
  exact h.invRep.f_cont

theorem WeightedFourierWitness.memL2 {d : ℕ}
    {A : Set (E d)} {alpha : ℝ} {f P : E d → ℂ}
    (h : WeightedFourierWitness alpha A f P) :
    MemLp f 2 volume := by
  exact h.invRep.f_memL2

private lemma weightedNorm_eq_norm_toLp {d : ℕ}
    {A : Set (E d)} {alpha : ℝ} {P : E d → ℂ}
    (hP : WeightedEnergyIntegrable alpha A P) :
    weightedNorm alpha A P = ‖hP.toLp P‖ := by
  rw [weightedNorm]
  exact (Lp.norm_toLp (f := P) (hf := hP)).symm

theorem weightedNorm_smul_le {d : ℕ}
    {A : Set (E d)} {alpha : ℝ} {P : E d → ℂ}
    (c : ℂ)
    (hP : WeightedEnergyIntegrable alpha A P) :
    weightedNorm alpha A (fun xi => c * P xi)
      ≤ ‖c‖ * weightedNorm alpha A P := by
  have hcP : (c • P) = (fun xi : E d => c * P xi) := by
    ext xi
    simp [Pi.smul_apply, smul_eq_mul]
  have hmem : WeightedEnergyIntegrable alpha A (fun xi : E d => c * P xi) := by
    change MemLp (fun xi : E d => c * P xi) 2 (weightedMeasure alpha A)
    simpa [hcP] using hP.const_smul c
  calc
    weightedNorm alpha A (fun xi : E d => c * P xi)
        = ‖hmem.toLp (fun xi : E d => c * P xi)‖ :=
            weightedNorm_eq_norm_toLp hmem
    _ = ‖c • hP.toLp P‖ := by
        have htoLp :
            hmem.toLp (fun xi : E d => c * P xi) =
              c • hP.toLp P := by
          simpa [hcP] using hP.toLp_const_smul c
        rw [htoLp]
    _ ≤ ‖c‖ * ‖hP.toLp P‖ := norm_smul_le c (hP.toLp P)
    _ = ‖c‖ * weightedNorm alpha A P := by
        rw [← weightedNorm_eq_norm_toLp hP]

theorem weightedNorm_add_le {d : ℕ}
    {A : Set (E d)} {alpha : ℝ} {P Q : E d → ℂ}
    (hP : WeightedEnergyIntegrable alpha A P)
    (hQ : WeightedEnergyIntegrable alpha A Q) :
    weightedNorm alpha A (fun xi => P xi + Q xi)
      ≤ weightedNorm alpha A P + weightedNorm alpha A Q := by
  have hPQ : (P + Q) = (fun xi : E d => P xi + Q xi) := by
    ext xi
    rfl
  have hmem : WeightedEnergyIntegrable alpha A (fun xi : E d => P xi + Q xi) := by
    change MemLp (fun xi : E d => P xi + Q xi) 2 (weightedMeasure alpha A)
    simpa [hPQ] using hP.add hQ
  calc
    weightedNorm alpha A (fun xi : E d => P xi + Q xi)
        = ‖hmem.toLp (fun xi : E d => P xi + Q xi)‖ :=
            weightedNorm_eq_norm_toLp hmem
    _ = ‖hP.toLp P + hQ.toLp Q‖ := by
        have htoLp :
            hmem.toLp (fun xi : E d => P xi + Q xi) =
              hP.toLp P + hQ.toLp Q := by
          simpa [hPQ] using hP.toLp_add hQ
        rw [htoLp]
    _ ≤ ‖hP.toLp P‖ + ‖hQ.toLp Q‖ := norm_add_le _ _
    _ = weightedNorm alpha A P + weightedNorm alpha A Q := by
        rw [← weightedNorm_eq_norm_toLp hP,
          ← weightedNorm_eq_norm_toLp hQ]

theorem weightedNorm_finset_sum_le {ι : Type*} [DecidableEq ι]
    {d : ℕ} {A : Set (E d)} {alpha : ℝ}
    (s : Finset ι) (P : ι → E d → ℂ)
    (hP : ∀ i ∈ s, WeightedEnergyIntegrable alpha A (P i)) :
    weightedNorm alpha A (fun xi => s.sum (fun i => P i xi))
      ≤ s.sum (fun i => weightedNorm alpha A (P i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [weightedNorm]
  | insert a s ha ih =>
      have htail :
          WeightedEnergyIntegrable alpha A
            (fun xi : E d => s.sum (fun i => P i xi)) := by
        change MemLp (fun xi : E d => s.sum (fun i => P i xi)) 2
          (weightedMeasure alpha A)
        simpa using
          (memLp_finsetSum
            (μ := weightedMeasure alpha A) (p := (2 : ℝ≥0∞))
            (s := s) (f := P)
            (fun i hi => hP i (by simp [hi])))
      have hstep :
          weightedNorm alpha A
              (fun xi : E d => P a xi + s.sum (fun i => P i xi))
            ≤ weightedNorm alpha A (P a) +
                weightedNorm alpha A (fun xi : E d => s.sum (fun i => P i xi)) :=
        weightedNorm_add_le (hP a (by simp)) htail
      have hih :
          weightedNorm alpha A (fun xi : E d => s.sum (fun i => P i xi))
            ≤ s.sum (fun i => weightedNorm alpha A (P i)) :=
        ih fun i hi => hP i (by simp [hi])
      calc
        weightedNorm alpha A
            (fun xi : E d => (insert a s).sum (fun i => P i xi))
            = weightedNorm alpha A
                (fun xi : E d => P a xi + s.sum (fun i => P i xi)) := by
              congr 1
              ext xi
              simp [Finset.sum_insert, ha]
        _ ≤ weightedNorm alpha A (P a) +
              weightedNorm alpha A
                (fun xi : E d => s.sum (fun i => P i xi)) := hstep
        _ ≤ weightedNorm alpha A (P a) +
              s.sum (fun i => weightedNorm alpha A (P i)) :=
              add_le_add le_rfl hih
        _ = (insert a s).sum (fun i => weightedNorm alpha A (P i)) := by
              simp [Finset.sum_insert, ha]

private lemma norm_sq_finset_sum_eq_sum_norm_sq_of_disjoint_at
    {ι X : Type*} [DecidableEq ι]
    {s : Finset ι} {S : ι → Set X} {F : ι → X → ℂ} {x : X}
    (h_supp : ∀ i ∈ s, F i x ≠ 0 → x ∈ S i)
    (h_disj :
      ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
        x ∉ S i ∩ S j) :
    ‖s.sum (fun i => F i x)‖ ^ 2 =
      s.sum (fun i => ‖F i x‖ ^ 2) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert a s ha ih =>
      have hsupp_tail : ∀ i ∈ s, F i x ≠ 0 → x ∈ S i := by
        intro i hi
        exact h_supp i (by simp [hi])
      have hdisj_tail :
          ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
            x ∉ S i ∩ S j := by
        intro i hi j hj hij
        exact h_disj i (by simp [hi]) j (by simp [hj]) hij
      by_cases hFa : F a x = 0
      · have hsum_left :
            (insert a s).sum (fun i => F i x) =
              s.sum (fun i => F i x) := by
          simp [Finset.sum_insert, ha, hFa]
        have hsum_right :
            (insert a s).sum (fun i => ‖F i x‖ ^ 2) =
              s.sum (fun i => ‖F i x‖ ^ 2) := by
          simp [Finset.sum_insert, ha, hFa]
        rw [hsum_left, hsum_right]
        exact ih hsupp_tail hdisj_tail
      · have htail_zero : ∀ i ∈ s, F i x = 0 := by
          intro i hi
          by_contra hFi
          have hSa : x ∈ S a := h_supp a (by simp [ha]) hFa
          have hSi : x ∈ S i := h_supp i (by simp [hi]) hFi
          have hai : a ≠ i := by
            intro h
            exact ha (by simpa [h] using hi)
          exact h_disj a (by simp [ha]) i (by simp [hi]) hai ⟨hSa, hSi⟩
        have hsum_tail_zero : s.sum (fun i => F i x) = 0 :=
          Finset.sum_eq_zero htail_zero
        have hnorm_tail_zero : s.sum (fun i => ‖F i x‖ ^ 2) = 0 := by
          refine Finset.sum_eq_zero ?_
          intro i hi
          simp [htail_zero i hi]
        simp [Finset.sum_insert, ha, hsum_tail_zero, hnorm_tail_zero]

theorem lintegral_norm_sq_finset_sum_of_ae_disjoint_support
    {ι X : Type*} [DecidableEq ι] [MeasurableSpace X]
    {μ : Measure X} {s : Finset ι}
    {S : ι → Set X} {F : ι → X → ℂ}
    (hF_meas : ∀ i ∈ s, AEStronglyMeasurable (F i) μ)
    (_hS_meas : ∀ i ∈ s, MeasurableSet (S i))
    (h_supp : ∀ i ∈ s, ∀ᵐ x ∂μ, F i x ≠ 0 → x ∈ S i)
    (h_disj :
      ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
        μ (S i ∩ S j) = 0) :
    ∫⁻ x, ENNReal.ofReal (‖s.sum (fun i => F i x)‖ ^ 2) ∂μ =
      s.sum (fun i =>
        ∫⁻ x, ENNReal.ofReal (‖F i x‖ ^ 2) ∂μ) := by
  -- Use `hF_meas` to obtain measurability of the nonnegative norm-square
  -- integrands. On the full-measure set where supports are disjoint, only one
  -- summand is nonzero, so the pointwise norm-square identity integrates.
  classical
  have h_supp_all :
      ∀ᵐ x ∂μ, ∀ i ∈ s, F i x ≠ 0 → x ∈ S i := by
    exact (Filter.eventually_all_finset s).2 fun i hi => h_supp i hi
  have h_disj_all :
      ∀ᵐ x ∂μ, ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
        x ∉ S i ∩ S j := by
    refine (Filter.eventually_all_finset s).2 ?_
    intro i hi
    refine (Filter.eventually_all_finset s).2 ?_
    intro j hj
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall fun _ hne => (hne hij).elim
    · filter_upwards [compl_mem_ae_iff.2 (h_disj i hi j hj hij)] with x hx _hne
      exact hx
  have h_integrand_aemeas :
      ∀ i ∈ s,
        AEMeasurable (fun x => ENNReal.ofReal (‖F i x‖ ^ 2)) μ := by
    intro i hi
    exact (((hF_meas i hi).norm.pow 2).aemeasurable.ennreal_ofReal)
  have h_pointwise :
      (fun x => ENNReal.ofReal (‖s.sum (fun i => F i x)‖ ^ 2))
        =ᵐ[μ]
      (fun x => s.sum (fun i =>
        ENNReal.ofReal (‖F i x‖ ^ 2))) := by
    filter_upwards [h_supp_all, h_disj_all] with x hsuppx hdisjx
    have hreal :=
      norm_sq_finset_sum_eq_sum_norm_sq_of_disjoint_at
        (s := s) (S := S) (F := F) (x := x) hsuppx hdisjx
    calc
      ENNReal.ofReal (‖s.sum (fun i => F i x)‖ ^ 2)
          = ENNReal.ofReal (s.sum (fun i => ‖F i x‖ ^ 2)) := by
              rw [hreal]
      _ = s.sum (fun i => ENNReal.ofReal (‖F i x‖ ^ 2)) := by
              exact ENNReal.ofReal_sum_of_nonneg
                (fun i _hi => sq_nonneg ‖F i x‖)
  calc
    ∫⁻ x, ENNReal.ofReal (‖s.sum (fun i => F i x)‖ ^ 2) ∂μ
        = ∫⁻ x, s.sum (fun i =>
            ENNReal.ofReal (‖F i x‖ ^ 2)) ∂μ :=
            lintegral_congr_ae h_pointwise
    _ = s.sum (fun i =>
          ∫⁻ x, ENNReal.ofReal (‖F i x‖ ^ 2) ∂μ) := by
          rw [lintegral_finsetSum' s h_integrand_aemeas]

theorem finite_toFinset_mem {α : Type*} [DecidableEq α]
    {s : Set α} (hs : s.Finite) (x : α) :
    x ∈ hs.toFinset ↔ x ∈ s := by
  exact hs.mem_toFinset

theorem finite_image_toFinset_mem {α β : Type*} [DecidableEq β]
    {s : Set α} (hs : s.Finite) (f : α → β) (y : β) :
    y ∈ (hs.image f).toFinset ↔ y ∈ f '' s := by
  exact (hs.image f).mem_toFinset

theorem latticeObstructionSet_finite {d : ℕ}
    {K : Set (E d)} {y : E d}
    (hK : IsCompact K) :
    (latticeObstructionSet K y).Finite := by
  have htranslate_compact : IsCompact ((fun x : E d => x - y) '' K) :=
    hK.image (continuous_id.sub continuous_const)
  rcases htranslate_compact.isBounded.subset_closedBall (0 : E d) with ⟨R, hR⟩
  refine (integerLattice_discrete_localFinite (d := d) R).subset ?_
  intro h hh
  refine ⟨hh.1, ?_⟩
  apply hR
  refine ⟨h + y, hh.2, ?_⟩
  abel_nf

theorem zero_not_mem_latticeObstructionSet {d : ℕ}
    {K : Set (E d)} {y : E d}
    (hyK : y ∉ K) :
    0 ∉ latticeObstructionSet K y := by
  intro h
  exact hyK (by simpa [latticeObstructionSet] using h.2)

end SpectralGapsPrelim.HigherDim
