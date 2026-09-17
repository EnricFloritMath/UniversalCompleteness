import PeriodicWeakGapsHD.HigherDim.Setup
import SpectralGapsPrelim.Theorem112.ExponentialIndependence

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Topology ENNReal FourierTransform

namespace SpectralGapsPrelim.HigherDim

/-!
Positive-measure exponential independence on line fibres.
-/

private lemma exists_accumulation_zero_of_ae_zero_on_pos_measure_mem
    {g : ℝ → ℂ} (_hg_cont : Continuous g)
    {B : Set ℝ} (_hB_meas : MeasurableSet B)
    (hB_pos : 0 < volume B)
    (hg_zero : ∀ᵐ t ∂volume.restrict B, g t = 0) :
    ∃ x : ℝ, ∃ᶠ y in nhds x, y ≠ x ∧ y ∈ B ∧ g y = 0 := by
  let bad : Set ℝ := {t | g t ≠ 0}
  have hbad_restrict : volume.restrict B bad = 0 := by
    simpa [bad] using (ae_iff.mp hg_zero)
  have hbad_inter : volume (B ∩ bad) = 0 := by
    simpa [Set.inter_comm] using
      (Measure.measure_inter_eq_zero_of_restrict (μ := volume) (s := B) (t := bad)
        hbad_restrict)
  let E : Set ℝ := B \ (B ∩ bad)
  have hE_pos : 0 < volume E := by
    change 0 < volume (B \ (B ∩ bad))
    rw [measure_sdiff_null hbad_inter]
    exact hB_pos
  rcases exists_accPt_of_noAtoms (μ := volume) (E := E) hE_pos with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  rw [accPt_iff_frequently] at hx
  exact hx.mono fun y hy =>
    ⟨hy.1, hy.2.1, by
      have hy_not_bad : y ∉ bad := fun hybad => hy.2.2 ⟨hy.2.1, hybad⟩
      simpa [bad] using hy_not_bad⟩

private lemma frequently_complex_ofReal_zero_of_real_accumulation
    {G : ℂ → ℂ} {x : ℝ}
    (hfreq :
      ∃ᶠ y in nhds x, y ≠ x ∧ G (Complex.ofReal y) = 0) :
    ∃ᶠ z in nhds (Complex.ofReal x),
      z ≠ Complex.ofReal x ∧ G z = 0 := by
  exact Tendsto.frequently_map (fun y : ℝ => Complex.ofReal y)
    (Complex.continuous_ofReal.tendsto x)
    (fun y hy => ⟨fun h => hy.1 (Complex.ofReal_injective h), hy.2⟩)
    hfreq

private lemma real_complex_exponential_sum_eq {ι : Type*} [Fintype ι]
    (d : ι → ℝ) (c : ι → ℂ) (t : ℝ) :
    (∑ j : ι,
        c j *
          Complex.exp (((((2 * Real.pi * d j : ℝ) : ℂ) * Complex.I) *
            (t : ℂ)))) =
      ∑ j : ι, c j * exp2piI (d j * t) := by
  classical
  apply Finset.sum_congr rfl
  intro j _hj
  congr 1
  simp [exp2piI]
  ring_nf

private lemma exp2piI_add (u v : ℝ) :
    exp2piI (u + v) = exp2piI u * exp2piI v := by
  unfold exp2piI
  rw [← Complex.exp_add]
  congr 1
  apply Complex.ext
  · simp
  · simp
    ring

private lemma exp2piI_ne_zero (u : ℝ) :
    exp2piI u ≠ 0 := by
  unfold exp2piI
  exact Complex.exp_ne_zero _

private lemma exp_sum_continuous {ι : Type*} [Fintype ι]
    (d : ι → ℝ) (c : ι → ℂ) :
    Continuous (fun t : ℝ => ∑ j : ι, c j * exp2piI (d j * t)) := by
  unfold exp2piI
  fun_prop

private lemma exp_sum_analytic {ι : Type*} [Fintype ι]
    (d : ι → ℝ) (c : ι → ℂ) :
    AnalyticOnNhd ℂ
      (fun z : ℂ =>
        ∑ j : ι,
          c j *
            Complex.exp (((((2 * Real.pi * d j : ℝ) : ℂ) * Complex.I) * z)))
      Set.univ := by
  classical
  apply Finset.analyticOnNhd_fun_sum
  intro j _hj
  have hlin : AnalyticOnNhd ℂ
      (fun z : ℂ => ((((2 * Real.pi * d j : ℝ) : ℂ) * Complex.I) * z))
      Set.univ := by
    change AnalyticOnNhd ℂ
      (fun z : ℂ =>
        ((ContinuousLinearMap.mul ℂ ℂ)
          (((2 * Real.pi * d j : ℝ) : ℂ) * Complex.I)) z)
      Set.univ
    exact ((((ContinuousLinearMap.mul ℂ ℂ)
      (((2 * Real.pi * d j : ℝ) : ℂ) * Complex.I))).analyticOnNhd Set.univ)
  exact (analyticOnNhd_const (v := c j)).mul hlin.cexp

private lemma norm_firstCoordinateVector {d : ℕ} (hd_pos : 0 < d) :
    ‖firstCoordinateVector hd_pos‖ = 1 := by
  simp [firstCoordinateVector, coordinateVector, toE, PiLp.norm_eq_of_L2]

private lemma firstCoordinateVector_ne_zero {d : ℕ} (hd_pos : 0 < d) :
    firstCoordinateVector hd_pos ≠ 0 := by
  intro h
  have hnorm := congrArg (fun x : E d => ‖x‖) h
  simp [norm_firstCoordinateVector hd_pos] at hnorm

private lemma measurableSet_lineFibre {d : ℕ} {A : Set (E d)}
    (hA_meas : MeasurableSet A) (w v : E d) :
    MeasurableSet (lineFibre A w v) := by
  change MeasurableSet ((fun s : ℝ => w + s • v) ⁻¹' A)
  exact hA_meas.preimage (by fun_prop)

theorem exists_separating_direction {d : ℕ} (hd_pos : 0 < d)
    (s : Finset (E d)) :
    ∃ v : E d,
      v ≠ 0 ∧
      ∀ h1 ∈ s, ∀ h2 ∈ s,
        h1 ≠ h2 → inner ℝ h1 v ≠ inner ℝ h2 v := by
  classical
  let pairs : Finset (E d × E d) := (s.product s).filter fun p => p.1 ≠ p.2
  by_cases hpairs_empty : pairs = ∅
  · refine ⟨firstCoordinateVector hd_pos, firstCoordinateVector_ne_zero hd_pos, ?_⟩
    intro h1 hh1 h2 hh2 hne
    have hp_mem : (h1, h2) ∈ pairs := by
      simp [pairs, hh1, hh2, hne]
    rw [hpairs_empty] at hp_mem
    simp at hp_mem
  let L : {p // p ∈ pairs} → Module.Dual ℝ (E d) := fun p =>
    (innerSL ℝ (p.1.1 - p.1.2)).toLinearMap
  have hL : ∀ p : {p // p ∈ pairs}, ∃ x : E d, L p x ≠ 0 := by
    intro p
    refine ⟨p.1.1 - p.1.2, ?_⟩
    have hp_ne : p.1.1 ≠ p.1.2 := by
      exact (Finset.mem_filter.mp p.2).2
    have hdiff : p.1.1 - p.1.2 ≠ 0 := sub_ne_zero.mpr hp_ne
    simpa only [L, ContinuousLinearMap.coe_coe, innerSL_apply_apply, inner_sub_left] using
      (inner_self_ne_zero (𝕜 := ℝ) (x := p.1.1 - p.1.2)).mpr hdiff
  rcases Module.Dual.exists_forall_ne_zero_of_forall_exists L hL with ⟨v, hv⟩
  refine ⟨v, ?_, ?_⟩
  · by_contra hv0
    obtain ⟨p0, hp0⟩ := (Finset.nonempty_of_ne_empty hpairs_empty).exists_mem
    exact (hv ⟨p0, hp0⟩) (by simp [hv0])
  · intro h1 hh1 h2 hh2 hne
    have hp_mem : (h1, h2) ∈ pairs := by
      simp [pairs, hh1, hh2, hne]
    have hvpair := hv ⟨(h1, h2), hp_mem⟩
    have hdiff :
        inner ℝ h1 v - inner ℝ h2 v ≠ 0 := by
      simpa only [L, ContinuousLinearMap.coe_coe, innerSL_apply_apply, inner_sub_left] using
        hvpair
    exact sub_ne_zero.mp hdiff

theorem coordinate_positive_fibre_of_posMeasure {d : ℕ} (hd_pos : 0 < d)
    {A : Set (E d)}
    (hA_meas : MeasurableSet A) (hA_pos : 0 < volume A) :
    ∃ w : E d,
      coord w ⟨0, hd_pos⟩ = 0 ∧
      MeasurableSet (lineFibre A w (firstCoordinateVector hd_pos)) ∧
      0 < volume (lineFibre A w (firstCoordinateVector hd_pos)) := by
  classical
  let e : E d := firstCoordinateVector hd_pos
  by_contra hno
  have hfibre_zero_hyper :
      ∀ w : E d, coord w ⟨0, hd_pos⟩ = 0 →
        volume (lineFibre A w e) = 0 := by
    intro w hw
    by_contra hzero
    exact hno ⟨w, hw, by simpa [e] using measurableSet_lineFibre hA_meas w e,
      pos_iff_ne_zero.mpr hzero⟩
  have hfibre_zero_all :
      ∀ y : E d, volume {s : ℝ | y + LinearMap.toSpanSingleton ℝ (E d) e s ∈ A} = 0 := by
    intro y
    let c : ℝ := coord y ⟨0, hd_pos⟩
    let w : E d := y - c • e
    have hw_coord : coord w ⟨0, hd_pos⟩ = 0 := by
      simp [w, c, e, firstCoordinateVector, coordinateVector, coord, toE]
    have hw_zero : volume (lineFibre A w e) = 0 :=
      hfibre_zero_hyper w hw_coord
    have hpre :
        {s : ℝ | y + LinearMap.toSpanSingleton ℝ (E d) e s ∈ A} =
          (fun s : ℝ => s + c) ⁻¹' lineFibre A w e := by
      ext s
      change y + s • e ∈ A ↔ w + (s + c) • e ∈ A
      have hpoint : y + s • e = w + (s + c) • e := by
        simp [w, add_smul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      rw [hpoint]
    rw [hpre, measure_preimage_add_right, hw_zero]
  have hAe :
      ∀ᵐ y ∂(volume : Measure (E d)), y ∈ Aᶜ := by
    refine MeasureTheory.ae_mem_of_ae_add_linearMap_mem
      (L := LinearMap.toSpanSingleton ℝ (E d) e)
      (μ := (volume : Measure ℝ)) (ν := (volume : Measure (E d)))
      hA_meas.compl ?_
    intro y
    rw [ae_iff]
    simpa [LinearMap.toSpanSingleton_apply] using hfibre_zero_all y
  have hA_zero : volume A = 0 := by
    simpa using (ae_iff.mp hAe)
  exact hA_pos.ne' hA_zero

theorem exists_coordinate_positive_fibre_with_ae_zero {d : ℕ} (hd_pos : 0 < d)
    {A : Set (E d)}
    (hA_meas : MeasurableSet A) (hA_pos : 0 < volume A)
    {G : E d → ℂ}
    (hG_cont : Continuous G)
    (hG_zero_ae : ∀ᵐ t ∂(volume.restrict A), G t = 0) :
    ∃ w : E d,
      coord w ⟨0, hd_pos⟩ = 0 ∧
      MeasurableSet (lineFibre A w (firstCoordinateVector hd_pos)) ∧
      0 < volume (lineFibre A w (firstCoordinateVector hd_pos)) ∧
      (∀ᵐ s ∂(volume.restrict (lineFibre A w (firstCoordinateVector hd_pos))),
        G (w + s • firstCoordinateVector hd_pos) = 0) := by
  classical
  let e : E d := firstCoordinateVector hd_pos
  let bad : Set (E d) := A ∩ G ⁻¹' ({0}ᶜ : Set ℂ)
  have hbad_ne_meas : MeasurableSet (G ⁻¹' ({0}ᶜ : Set ℂ)) :=
    hG_cont.measurable (measurableSet_singleton (0 : ℂ)).compl
  have hbad_meas : MeasurableSet bad := hA_meas.inter hbad_ne_meas
  have hbad_restrict : volume.restrict A (G ⁻¹' ({0}ᶜ : Set ℂ)) = 0 := by
    simpa [Set.preimage] using (ae_iff.mp hG_zero_ae)
  have hbad_zero : volume bad = 0 := by
    simpa [bad, Set.inter_comm] using
      (Measure.measure_inter_eq_zero_of_restrict (μ := volume) (s := A)
        (t := G ⁻¹' ({0}ᶜ : Set ℂ)) hbad_restrict)
  have hbad_ae_compl :
      ∀ᵐ y ∂(volume : Measure (E d)), y ∈ badᶜ := by
    rw [ae_iff]
    simpa using hbad_zero
  have hgood_base :
      ∀ᵐ y ∂(volume : Measure (E d)),
        ∀ᵐ s ∂(volume : Measure ℝ),
          y + LinearMap.toSpanSingleton ℝ (E d) e s ∈ badᶜ := by
    exact (MeasureTheory.ae_ae_add_linearMap_mem_iff
      (L := LinearMap.toSpanSingleton ℝ (E d) e)
      (μ := (volume : Measure ℝ)) (ν := (volume : Measure (E d)))
      hbad_meas.compl).2 hbad_ae_compl
  by_contra hno
  have hA_line_zero_ae :
      ∀ᵐ y ∂(volume : Measure (E d)),
        volume {s : ℝ | y + LinearMap.toSpanSingleton ℝ (E d) e s ∈ A} = 0 := by
    filter_upwards [hgood_base] with y hy_good
    by_contra hy_nonzero
    have hy_pos :
        0 < volume {s : ℝ | y + LinearMap.toSpanSingleton ℝ (E d) e s ∈ A} :=
      pos_iff_ne_zero.mpr hy_nonzero
    let c : ℝ := coord y ⟨0, hd_pos⟩
    let w : E d := y - c • e
    have hw_coord : coord w ⟨0, hd_pos⟩ = 0 := by
      simp [w, c, e, firstCoordinateVector, coordinateVector, coord, toE]
    have hpreA :
        {s : ℝ | y + LinearMap.toSpanSingleton ℝ (E d) e s ∈ A} =
          (fun s : ℝ => s + c) ⁻¹' lineFibre A w e := by
      ext s
      change y + s • e ∈ A ↔ w + (s + c) • e ∈ A
      have hpoint : y + s • e = w + (s + c) • e := by
        simp [w, add_smul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      rw [hpoint]
    have hw_pos : 0 < volume (lineFibre A w e) := by
      rw [hpreA, measure_preimage_add_right] at hy_pos
      exact hy_pos
    have hy_bad_zero :
        volume {s : ℝ | y + LinearMap.toSpanSingleton ℝ (E d) e s ∈ bad} = 0 := by
      have h := ae_iff.mp hy_good
      simpa using h
    have hpreBad :
        {s : ℝ | y + LinearMap.toSpanSingleton ℝ (E d) e s ∈ bad} =
          (fun s : ℝ => s + c) ⁻¹' lineFibre bad w e := by
      ext s
      change y + s • e ∈ bad ↔ w + (s + c) • e ∈ bad
      have hpoint : y + s • e = w + (s + c) • e := by
        simp [w, add_smul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      rw [hpoint]
    have hw_bad_zero : volume (lineFibre bad w e) = 0 := by
      rw [hpreBad, measure_preimage_add_right] at hy_bad_zero
      exact hy_bad_zero
    have hw_good :
        ∀ᵐ s ∂(volume : Measure ℝ), w + s • e ∈ badᶜ := by
      rw [ae_iff]
      simpa [lineFibre] using hw_bad_zero
    have hzero_restrict :
        ∀ᵐ s ∂(volume.restrict (lineFibre A w e)),
          G (w + s • e) = 0 := by
      rw [ae_restrict_iff' (measurableSet_lineFibre hA_meas w e)]
      filter_upwards [hw_good] with s hs_good hsA
      by_contra hne
      have hA_mem : w + s • e ∈ A := by
        simpa [lineFibre] using hsA
      exact hs_good ⟨hA_mem, hne⟩
    exact hno ⟨w, hw_coord,
      by simpa [e] using measurableSet_lineFibre hA_meas w e,
      by simpa [e] using hw_pos,
      by simpa [e] using hzero_restrict⟩
  have hAline_compl :
      ∀ᵐ y ∂(volume : Measure (E d)),
        ∀ᵐ s ∂(volume : Measure ℝ),
          y + LinearMap.toSpanSingleton ℝ (E d) e s ∈ Aᶜ := by
    filter_upwards [hA_line_zero_ae] with y hy_zero
    rw [ae_iff]
    simpa using hy_zero
  have hA_compl_ae :
      ∀ᵐ y ∂(volume : Measure (E d)), y ∈ Aᶜ :=
    (MeasureTheory.ae_ae_add_linearMap_mem_iff
      (L := LinearMap.toSpanSingleton ℝ (E d) e)
      (μ := (volume : Measure ℝ)) (ν := (volume : Measure (E d)))
      hA_meas.compl).1 hAline_compl
  have hA_zero : volume A = 0 := by
    simpa using (ae_iff.mp hA_compl_ae)
  exact hA_pos.ne' hA_zero

theorem linearIsometry_map_positive_fibre {d : ℕ} (hd_pos : 0 < d)
    {v : E d} (hv : v ≠ 0) :
    ∃ U : E d ≃ₗᵢ[ℝ] E d,
      U v = ‖v‖ • firstCoordinateVector hd_pos := by
  let e : E d := firstCoordinateVector hd_pos
  let u : E d := ‖v‖⁻¹ • v
  have hv_norm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hu_norm : ‖u‖ = 1 := by
    simp [u, norm_smul, hv_norm]
  have he_norm : ‖e‖ = 1 := by
    simpa [e] using norm_firstCoordinateVector hd_pos
  let U : E d ≃ₗᵢ[ℝ] E d := Submodule.reflection (ℝ ∙ (u - e))ᗮ
  refine ⟨U, ?_⟩
  have hUu : U u = e := by
    simpa [U] using (Submodule.reflection_sub (F := E d) (v := u) (w := e)
      (by simp [hu_norm, he_norm]))
  calc
    U v = U (‖v‖ • u) := by
      congr 1
      simp [u, smul_smul, hv_norm]
    _ = ‖v‖ • U u := by
      exact U.map_smulₛₗ ‖v‖ u
    _ = ‖v‖ • firstCoordinateVector hd_pos := by
      simp [hUu, e]

theorem exists_positive_line_fibre {d : ℕ} (hd_pos : 0 < d)
    {A : Set (E d)} {v : E d}
    (hv : v ≠ 0)
    (hA_meas : MeasurableSet A)
    (hA_pos : 0 < volume A)
    {G : E d → ℂ}
    (hG_cont : Continuous G)
    (hG_zero_ae : ∀ᵐ t ∂(volume.restrict A), G t = 0) :
    ∃ w : E d,
      inner ℝ w v = 0 ∧
      MeasurableSet (lineFibre A w v) ∧
      0 < volume (lineFibre A w v) ∧
      (∀ᵐ s ∂(volume.restrict (lineFibre A w v)),
        G (w + s • v) = 0) := by
  have _ : 0 < d := hd_pos
  classical
  let bad : Set (E d) := A ∩ G ⁻¹' ({0}ᶜ : Set ℂ)
  have hbad_ne_meas : MeasurableSet (G ⁻¹' ({0}ᶜ : Set ℂ)) :=
    hG_cont.measurable (measurableSet_singleton (0 : ℂ)).compl
  have hbad_meas : MeasurableSet bad := hA_meas.inter hbad_ne_meas
  have hbad_restrict : volume.restrict A (G ⁻¹' ({0}ᶜ : Set ℂ)) = 0 := by
    simpa [Set.preimage] using (ae_iff.mp hG_zero_ae)
  have hbad_zero : volume bad = 0 := by
    simpa [bad, Set.inter_comm] using
      (Measure.measure_inter_eq_zero_of_restrict (μ := volume) (s := A)
        (t := G ⁻¹' ({0}ᶜ : Set ℂ)) hbad_restrict)
  have hbad_ae_compl :
      ∀ᵐ y ∂(volume : Measure (E d)), y ∈ badᶜ := by
    rw [ae_iff]
    simpa using hbad_zero
  have hgood_base :
      ∀ᵐ y ∂(volume : Measure (E d)),
        ∀ᵐ s ∂(volume : Measure ℝ),
          y + LinearMap.toSpanSingleton ℝ (E d) v s ∈ badᶜ := by
    exact (MeasureTheory.ae_ae_add_linearMap_mem_iff
      (L := LinearMap.toSpanSingleton ℝ (E d) v)
      (μ := (volume : Measure ℝ)) (ν := (volume : Measure (E d)))
      hbad_meas.compl).2 hbad_ae_compl
  by_contra hno
  have hinner_vv_ne : inner ℝ v v ≠ 0 :=
    (inner_self_ne_zero (𝕜 := ℝ) (x := v)).mpr hv
  have hA_line_zero_ae :
      ∀ᵐ y ∂(volume : Measure (E d)),
        volume {s : ℝ | y + LinearMap.toSpanSingleton ℝ (E d) v s ∈ A} = 0 := by
    filter_upwards [hgood_base] with y hy_good
    by_contra hy_nonzero
    have hy_pos :
        0 < volume {s : ℝ | y + LinearMap.toSpanSingleton ℝ (E d) v s ∈ A} :=
      pos_iff_ne_zero.mpr hy_nonzero
    let c : ℝ := inner ℝ y v / inner ℝ v v
    let w : E d := y - c • v
    have hscale : c * inner ℝ v v = inner ℝ y v := by
      simpa [c] using div_mul_cancel₀ (inner ℝ y v) hinner_vv_ne
    have hw_orth : inner ℝ w v = 0 := by
      calc
        inner ℝ w v = inner ℝ y v - c * inner ℝ v v := by
          simp [w, inner_sub_left, real_inner_smul_left]
        _ = 0 := by
          rw [hscale]
          simp
    have hpreA :
        {s : ℝ | y + LinearMap.toSpanSingleton ℝ (E d) v s ∈ A} =
          (fun s : ℝ => s + c) ⁻¹' lineFibre A w v := by
      ext s
      change y + s • v ∈ A ↔ w + (s + c) • v ∈ A
      have hpoint : y + s • v = w + (s + c) • v := by
        simp [w, add_smul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      rw [hpoint]
    have hw_pos : 0 < volume (lineFibre A w v) := by
      rw [hpreA, measure_preimage_add_right] at hy_pos
      exact hy_pos
    have hy_bad_zero :
        volume {s : ℝ | y + LinearMap.toSpanSingleton ℝ (E d) v s ∈ bad} = 0 := by
      have h := ae_iff.mp hy_good
      simpa using h
    have hpreBad :
        {s : ℝ | y + LinearMap.toSpanSingleton ℝ (E d) v s ∈ bad} =
          (fun s : ℝ => s + c) ⁻¹' lineFibre bad w v := by
      ext s
      change y + s • v ∈ bad ↔ w + (s + c) • v ∈ bad
      have hpoint : y + s • v = w + (s + c) • v := by
        simp [w, add_smul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      rw [hpoint]
    have hw_bad_zero : volume (lineFibre bad w v) = 0 := by
      rw [hpreBad, measure_preimage_add_right] at hy_bad_zero
      exact hy_bad_zero
    have hw_good :
        ∀ᵐ s ∂(volume : Measure ℝ), w + s • v ∈ badᶜ := by
      rw [ae_iff]
      simpa [lineFibre] using hw_bad_zero
    have hzero_restrict :
        ∀ᵐ s ∂(volume.restrict (lineFibre A w v)),
          G (w + s • v) = 0 := by
      rw [ae_restrict_iff' (measurableSet_lineFibre hA_meas w v)]
      filter_upwards [hw_good] with s hs_good hsA
      by_contra hne
      have hA_mem : w + s • v ∈ A := by
        simpa [lineFibre] using hsA
      exact hs_good ⟨hA_mem, by simpa using hne⟩
    exact hno ⟨w, hw_orth, measurableSet_lineFibre hA_meas w v, hw_pos, hzero_restrict⟩
  have hAline_compl :
      ∀ᵐ y ∂(volume : Measure (E d)),
        ∀ᵐ s ∂(volume : Measure ℝ),
          y + LinearMap.toSpanSingleton ℝ (E d) v s ∈ Aᶜ := by
    filter_upwards [hA_line_zero_ae] with y hy_zero
    rw [ae_iff]
    simpa using hy_zero
  have hA_compl_ae :
      ∀ᵐ y ∂(volume : Measure (E d)), y ∈ Aᶜ :=
    (MeasureTheory.ae_ae_add_linearMap_mem_iff
      (L := LinearMap.toSpanSingleton ℝ (E d) v)
      (μ := (volume : Measure ℝ)) (ν := (volume : Measure (E d)))
      hA_meas.compl).1 hAline_compl
  have hA_zero : volume A = 0 := by
    simpa using (ae_iff.mp hA_compl_ae)
  exact hA_pos.ne' hA_zero

theorem oneDim_exp_poly_zero_everywhere_of_posMeasure
    {m : ℕ}
    {beta : Fin m → ℝ}
    {a : Fin m → ℂ}
    {B : Set ℝ}
    (hB_meas : MeasurableSet B)
    (hB_pos : 0 < volume B)
    (hzero :
      ∀ᵐ s ∂(volume.restrict B),
        (Finset.univ.sum
          (fun j : Fin m => a j * exp2piI (beta j * s))) = 0) :
    ∀ z : ℂ,
      Finset.univ.sum
        (fun j : Fin m =>
          a j * Complex.exp ((((2 * Real.pi * beta j : ℝ) : ℂ) * Complex.I) * z)) = 0 := by
  classical
  let G : ℂ → ℂ := fun z =>
    ∑ j : Fin m,
      a j * Complex.exp (((((2 * Real.pi * beta j : ℝ) : ℂ) * Complex.I) * z))
  let g : ℝ → ℂ := fun t => ∑ j : Fin m, a j * exp2piI (beta j * t)
  have hg_cont : Continuous g := by
    simpa [g] using exp_sum_continuous beta a
  obtain ⟨x, hx⟩ := exists_accumulation_zero_of_ae_zero_on_pos_measure_mem
    hg_cont hB_meas hB_pos hzero
  have hxG : ∃ᶠ y in nhds x, y ≠ x ∧ G (Complex.ofReal y) = 0 := by
    refine hx.mono ?_
    intro y hy
    refine ⟨hy.1, ?_⟩
    have hGy : G (Complex.ofReal y) = g y := by
      simpa [G, g] using (real_complex_exponential_sum_eq beta a y)
    simpa [hGy] using hy.2.2
  have hfreq_complex :=
    frequently_complex_ofReal_zero_of_real_accumulation (G := G) hxG
  have hfreq_punct :
      ∃ᶠ z in nhdsWithin (Complex.ofReal x) {z | z ≠ Complex.ofReal x},
        G z = 0 := by
    rw [nhdsWithin, Filter.frequently_inf_principal]
    exact hfreq_complex
  have hG_an : AnalyticOnNhd ℂ G Set.univ := by
    simpa [G] using exp_sum_analytic beta a
  have hG_zero_on : Set.EqOn G 0 Set.univ :=
    hG_an.eqOn_zero_of_preconnected_of_frequently_eq_zero
      isPreconnected_univ (by simp) hfreq_punct
  intro z
  exact hG_zero_on (by simp)

theorem vandermonde_coefficients_zero_of_derivatives
    {m : ℕ} {beta : Fin m → ℝ}
    (hbeta : Function.Injective beta)
    {a : Fin m → ℂ}
    (hderiv :
      ∀ n : Fin m,
        Finset.univ.sum
          (fun j : Fin m =>
            a j * ((((2 * Real.pi * beta j : ℝ) : ℂ) * Complex.I) ^ (n : ℕ))) = 0) :
    ∀ j : Fin m, a j = 0 := by
  classical
  let alpha : Fin m → ℂ := fun j =>
    (((2 * Real.pi * beta j : ℝ) : ℂ) * Complex.I)
  have halpha : Function.Injective alpha := by
    intro i j hij
    have him :
        2 * Real.pi * beta i = 2 * Real.pi * beta j := by
      have := congrArg Complex.im hij
      simpa [alpha] using this
    have hbeta_eq : beta i = beta j := by
      exact mul_left_cancel₀ (show 2 * Real.pi ≠ 0 by positivity) him
    exact hbeta hbeta_eq
  have ha_zero : a = 0 := by
    apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero
      (R := ℂ) (f := alpha) (v := a) halpha
    intro n
    simpa [alpha] using hderiv n
  intro j
  rw [ha_zero]
  rfl

theorem oneDim_exp_poly_eq_zero_of_posMeasure
    {m : ℕ}
    {beta : Fin m → ℝ}
    (hbeta : Function.Injective beta)
    {a : Fin m → ℂ}
    {B : Set ℝ}
    (hB_meas : MeasurableSet B)
    (hB_pos : 0 < volume B)
    (hzero :
      ∀ᵐ s ∂(volume.restrict B),
        (Finset.univ.sum
          (fun j : Fin m => a j * exp2piI (beta j * s))) = 0) :
    ∀ j : Fin m, a j = 0 := by
  classical
  exact SpectralGapsPrelim.Theorem112.expFamily_linearIndependent_ae
    (ι := Fin m) hbeta hB_meas hB_pos (c := a) (by
      filter_upwards [hzero] with s hs
      simpa [SpectralGapsPrelim.HigherDim.exp2piI,
        SpectralGapsPrelim.Theorem112.exp2piI] using hs)

theorem exists_accumulation_zero_of_ae_zero_on_posMeasure
    {F : ℝ → ℂ} {B : Set ℝ}
    (hB_meas : MeasurableSet B) (hB_pos : 0 < volume B)
    (hF_cont : Continuous F)
    (hzero : ∀ᵐ s ∂(volume.restrict B), F s = 0) :
    ∃ s0 : ℝ, AccPt s0 (Filter.principal {s : ℝ | s ∈ B ∧ F s = 0}) := by
  obtain ⟨s0, hs0⟩ := exists_accumulation_zero_of_ae_zero_on_pos_measure_mem
    hF_cont hB_meas hB_pos hzero
  refine ⟨s0, ?_⟩
  rw [accPt_iff_frequently]
  exact hs0.mono fun s hs => ⟨hs.1, hs.2.1, hs.2.2⟩

theorem exp_sum_eq_zero_ae_of_coeffs_zero_hd {d : ℕ} (hd_pos : 0 < d)
    {A : Set (E d)}
    (hA_meas : MeasurableSet A)
    (hA_pos : 0 < volume A)
    {s : Finset (E d)}
    {c : E d → ℂ}
    (hzero :
      ∀ᵐ t ∂(volume.restrict A),
        (s.sum (fun h => c h * exp2piI (inner ℝ h t))) = 0) :
    ∀ h ∈ s, c h = 0 := by
  classical
  let G : E d → ℂ := fun t =>
    s.sum (fun h => c h * exp2piI (inner ℝ h t))
  have hG_cont : Continuous G := by
    unfold G exp2piI
    fun_prop
  obtain ⟨v, hv, hsep⟩ := exists_separating_direction hd_pos s
  obtain ⟨w, _hw_orth, hB_meas, hB_pos, hG_zero_fibre⟩ :=
    exists_positive_line_fibre (d := d) hd_pos (A := A) (v := v) hv
      hA_meas hA_pos hG_cont (G := G) (by
        simpa [G] using hzero)
  let B : Set ℝ := lineFibre A w v
  let beta : {h // h ∈ s} → ℝ := fun h => inner ℝ (h : E d) v
  let a : {h // h ∈ s} → ℂ := fun h =>
    c (h : E d) * exp2piI (inner ℝ (h : E d) w)
  have hbeta : Function.Injective beta := by
    intro h k hhk
    apply Subtype.ext
    by_contra hne
    exact hsep (h : E d) h.2 (k : E d) k.2 hne hhk
  have hline_zero :
      ∀ᵐ r ∂(volume.restrict B),
        (Finset.univ.sum
          (fun j : {h // h ∈ s} =>
            a j * SpectralGapsPrelim.Theorem112.exp2piI (beta j * r))) = 0 := by
    filter_upwards [hG_zero_fibre] with r hr
    have hsum :
        (Finset.univ.sum
          (fun j : {h // h ∈ s} =>
            a j * SpectralGapsPrelim.Theorem112.exp2piI (beta j * r))) =
          G (w + r • v) := by
      have hconvert :
          (Finset.univ.sum
            (fun j : {h // h ∈ s} =>
              a j * SpectralGapsPrelim.Theorem112.exp2piI (beta j * r))) =
            Finset.univ.sum
              (fun j : {h // h ∈ s} => a j * exp2piI (beta j * r)) := by
        apply Finset.sum_congr rfl
        intro j _hj
        simp [SpectralGapsPrelim.HigherDim.exp2piI,
          SpectralGapsPrelim.Theorem112.exp2piI]
      have hlocal :
          (Finset.univ.sum
            (fun j : {h // h ∈ s} => a j * exp2piI (beta j * r))) =
          G (w + r • v) := by
        have hterm (x : {h // h ∈ s}) :
            a x * exp2piI (beta x * r) =
              c (x : E d) * exp2piI (inner ℝ (x : E d) (w + r • v)) := by
          simp [a, beta, exp2piI_add, inner_add_right, real_inner_smul_right,
            mul_comm, mul_left_comm]
        calc
          (Finset.univ.sum
            (fun j : {h // h ∈ s} => a j * exp2piI (beta j * r))) =
              ∑ x ∈ s.attach, a x * exp2piI (beta x * r) := by
                rw [Finset.univ_eq_attach s]
          _ = ∑ x ∈ s.attach,
                c (x : E d) * exp2piI (inner ℝ (x : E d) (w + r • v)) := by
                apply Finset.sum_congr rfl
                intro x _hx
                exact hterm x
          _ = ∑ x ∈ s, c x * exp2piI (inner ℝ x (w + r • v)) := by
                simpa using
                  (Finset.sum_attach s
                    (fun x : E d => c x * exp2piI (inner ℝ x (w + r • v))))
          _ = G (w + r • v) := by
                simp [G]
      exact hconvert.trans hlocal
    exact hsum.trans hr
  have hacoeff : ∀ j : {h // h ∈ s}, a j = 0 :=
    SpectralGapsPrelim.Theorem112.expFamily_linearIndependent_ae
      (ι := {h // h ∈ s}) hbeta hB_meas hB_pos (c := a) hline_zero
  intro h hs
  have hh := hacoeff ⟨h, hs⟩
  exact (mul_eq_zero.mp hh).resolve_right (exp2piI_ne_zero (inner ℝ h w))

end SpectralGapsPrelim.HigherDim
