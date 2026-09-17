import Theorem14.Definitions

/-! # Theorem 1.4: triangular window -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace Theorem14.Internal

/- Proof idea: square box coefficients and calculate the zero coefficient as epsilon/2. -/
theorem windowCoeff_eq_sq_and_zero
    (epsilon : ℝ) (he0 : 0 < epsilon) (he1 : epsilon < 1) :
    (∀ k : ℤ, windowCoeff epsilon k = fourierCoeff (boxWindow epsilon) k ^ 2) ∧
      windowCoeff epsilon 0 = (epsilon : ℂ) ^ 2 / 4 ∧
      windowCoeff epsilon 0 ≠ 0 := by
  /- Proof idea: Apply the convolution coefficient theorem; compute the zero box coefficient as `epsilon/2`;
  square and use `epsilon>0`. -/
  classical
  let B : Set (AddCircle (1 : ℝ)) :=
    Theorem12.Generic.unitRep ⁻¹' Set.Icc 0 (epsilon / 2)
  have hunitMeas : Measurable Theorem12.Generic.unitRep :=
    (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable.subtype_val
  have hBmeas : MeasurableSet B := measurableSet_Icc.preimage hunitMeas
  have hbox : boxWindow epsilon = B.indicator (fun _ => (1 : ℂ)) := by
    funext x
    by_cases hx : Theorem12.Generic.unitRep x ∈ Set.Icc 0 (epsilon / 2)
    · have hxB : x ∈ B := hx
      rw [Set.indicator_of_mem hxB]
      simp [boxWindow, hx]
    · have hxB : x ∉ B := hx
      rw [Set.indicator_of_notMem hxB]
      simp [boxWindow, hx]
  have hboxInt : Integrable (boxWindow epsilon) AddCircle.haarAddCircle := by
    rw [hbox]
    exact (integrable_const (1 : ℂ)).indicator hBmeas
  have hboxMeas : Measurable (boxWindow epsilon) := by
    rw [hbox]
    exact measurable_const.indicator hBmeas
  have hsubset : Set.Icc 0 (epsilon / 2) ⊆ Set.Ico (0 : ℝ) 1 := by
    intro x hx
    exact ⟨hx.1, lt_of_le_of_lt hx.2 (by linarith)⟩
  have hBmeasure :
      AddCircle.haarAddCircle B = volume (Set.Icc 0 (epsilon / 2)) := by
    have h := Theorem12.Generic.measure_unitRep_preimage
      (Set.Icc 0 (epsilon / 2)) measurableSet_Icc
    rw [Set.inter_eq_left.mpr hsubset] at h
    exact h
  have hBmeasureReal : AddCircle.haarAddCircle.real B = epsilon / 2 := by
    calc
      AddCircle.haarAddCircle.real B =
          volume.real (Set.Icc 0 (epsilon / 2)) := by
            exact congrArg ENNReal.toReal hBmeasure
      _ = max (epsilon / 2 - 0) 0 := Real.volume_real_Icc
      _ = epsilon / 2 := by rw [sub_zero, max_eq_left (by linarith)]
  have hboxZero : fourierCoeff (boxWindow epsilon) 0 = (epsilon : ℂ) / 2 := by
    calc
      fourierCoeff (boxWindow epsilon) 0 =
          ∫ x, boxWindow epsilon x ∂AddCircle.haarAddCircle := by
            simp [fourierCoeff]
      _ = ∫ x, B.indicator (fun _ => (1 : ℂ)) x
          ∂AddCircle.haarAddCircle := by rw [hbox]
      _ = ((AddCircle.haarAddCircle.real B : ℝ) : ℂ) := by
        simpa using
          (MeasureTheory.integral_indicator_const
            (μ := AddCircle.haarAddCircle) (1 : ℂ) hBmeas)
      _ = (epsilon : ℂ) / 2 := by rw [hBmeasureReal]; norm_num
  have hconv : ∀ k : ℤ,
      windowCoeff epsilon k = fourierCoeff (boxWindow epsilon) k ^ 2 := by
    intro k
    let H : AddCircle (1 : ℝ) × AddCircle (1 : ℝ) → ℂ := fun z =>
      fourier (-k) z.1 * boxWindow epsilon z.2 *
        boxWindow epsilon (z.1 - z.2)
    have hboxNorm (x : AddCircle (1 : ℝ)) : ‖boxWindow epsilon x‖ ≤ 1 := by
      simp only [boxWindow]
      split_ifs <;> norm_num
    have hHMeas : Measurable H := by
      exact (((map_continuous (fourier (-k))).measurable.comp measurable_fst).mul
        (hboxMeas.comp measurable_snd)).mul
          (hboxMeas.comp (measurable_fst.sub measurable_snd))
    have hHInt : Integrable H
        (AddCircle.haarAddCircle.prod AddCircle.haarAddCircle) := by
      apply (integrable_const (1 : ℝ)).mono' hHMeas.aestronglyMeasurable
      filter_upwards
      intro z
      simp only [H, norm_mul, fourier_apply, Circle.norm_coe, one_mul]
      exact mul_le_one₀ (hboxNorm z.2) (norm_nonneg _) (hboxNorm (z.1 - z.2))
    have hinner (y : AddCircle (1 : ℝ)) :
        (∫ x, fourier (-k) x * boxWindow epsilon (x - y)
          ∂AddCircle.haarAddCircle) =
          fourier (-k) y * fourierCoeff (boxWindow epsilon) k := by
      let q : AddCircle (1 : ℝ) → ℂ := fun z =>
        fourier (-k) (z + y) * boxWindow epsilon z
      have hbase : Integrable
          (fun z => fourier (-k) z * boxWindow epsilon z)
          AddCircle.haarAddCircle := by
        simpa only [smul_eq_mul] using hboxInt.fourier_smul (-k)
      have hqEq : q = fun z =>
          fourier (-k) y * (fourier (-k) z * boxWindow epsilon z) := by
        funext z
        simp only [q, fourier_apply, zsmul_add,
          AddCircle.toCircle_add, Circle.coe_mul]
        ring
      have hqInt : Integrable q AddCircle.haarAddCircle := by
        rw [hqEq]
        exact hbase.const_mul _
      have hshift :
          (∫ x, q (x - y) ∂AddCircle.haarAddCircle) =
            ∫ z, q z ∂AddCircle.haarAddCircle :=
        Theorem12.Generic.integral_addCircle_sub q hqInt y
      calc
        (∫ x, fourier (-k) x * boxWindow epsilon (x - y)
            ∂AddCircle.haarAddCircle) =
            ∫ x, q (x - y) ∂AddCircle.haarAddCircle := by
              apply integral_congr_ae
              filter_upwards
              intro x
              dsimp only [q]
              rw [sub_add_cancel]
        _ = ∫ z, q z ∂AddCircle.haarAddCircle := hshift
        _ = ∫ z, fourier (-k) y *
              (fourier (-k) z * boxWindow epsilon z)
            ∂AddCircle.haarAddCircle := by rw [hqEq]
        _ = fourier (-k) y *
              ∫ z, fourier (-k) z * boxWindow epsilon z
                ∂AddCircle.haarAddCircle := by
              exact MeasureTheory.integral_const_mul _ _
        _ = fourier (-k) y * fourierCoeff (boxWindow epsilon) k := by
              rfl
    have hHinner (y : AddCircle (1 : ℝ)) :
        (∫ x, H (x, y) ∂AddCircle.haarAddCircle) =
          (fourier (-k) y * boxWindow epsilon y) *
            fourierCoeff (boxWindow epsilon) k := by
      calc
        (∫ x, H (x, y) ∂AddCircle.haarAddCircle) =
            ∫ x, boxWindow epsilon y *
              (fourier (-k) x * boxWindow epsilon (x - y))
                ∂AddCircle.haarAddCircle := by
              apply integral_congr_ae
              filter_upwards
              intro x
              dsimp only [H]
              ring
        _ = boxWindow epsilon y *
              ∫ x, fourier (-k) x * boxWindow epsilon (x - y)
                ∂AddCircle.haarAddCircle := by
              exact MeasureTheory.integral_const_mul _ _
        _ = boxWindow epsilon y *
              (fourier (-k) y * fourierCoeff (boxWindow epsilon) k) := by
              rw [hinner]
        _ = (fourier (-k) y * boxWindow epsilon y) *
              fourierCoeff (boxWindow epsilon) k := by ring
    simp only [windowCoeff, fourierCoeff, tentWindow, smul_eq_mul]
    calc
      (∫ x, fourier (-k) x *
          (∫ y, boxWindow epsilon y * boxWindow epsilon (x - y)
            ∂AddCircle.haarAddCircle) ∂AddCircle.haarAddCircle) =
          ∫ x, ∫ y, H (x, y) ∂AddCircle.haarAddCircle
            ∂AddCircle.haarAddCircle := by
              apply integral_congr_ae
              filter_upwards
              intro x
              rw [← MeasureTheory.integral_const_mul]
              apply integral_congr_ae
              filter_upwards
              intro y
              dsimp only [H]
              ring
      _ = ∫ y, ∫ x, H (x, y) ∂AddCircle.haarAddCircle
            ∂AddCircle.haarAddCircle :=
          MeasureTheory.integral_integral_swap hHInt
      _ = ∫ y, (fourier (-k) y * boxWindow epsilon y) *
            fourierCoeff (boxWindow epsilon) k
          ∂AddCircle.haarAddCircle := by
            apply integral_congr_ae
            filter_upwards
            intro y
            exact hHinner y
      _ = (∫ y, fourier (-k) y * boxWindow epsilon y
            ∂AddCircle.haarAddCircle) *
              fourierCoeff (boxWindow epsilon) k := by
            exact MeasureTheory.integral_mul_const _ _
      _ = (∫ y, fourier (-k) y * boxWindow epsilon y
            ∂AddCircle.haarAddCircle) ^ 2 := by
            rw [show fourierCoeff (boxWindow epsilon) k =
              (∫ y, fourier (-k) y * boxWindow epsilon y
                ∂AddCircle.haarAddCircle) from rfl]
            ring
  refine ⟨hconv, ?_, ?_⟩
  · rw [hconv 0, hboxZero]
    ring
  · rw [hconv 0, hboxZero]
    exact pow_ne_zero 2 (div_ne_zero (Complex.ofReal_ne_zero.mpr he0.ne') (by norm_num))

/- Proof idea: create the actual Lp 2 representative before applying Parseval. -/
private lemma hasSum_sq_fourierCoeff_boxWindow
    (epsilon : ℝ) (he0 : 0 < epsilon) (he1 : epsilon < 1) :
    HasSum (fun k : ℤ => ‖fourierCoeff (boxWindow epsilon) k‖ ^ 2)
      (epsilon / 2) := by
  /- Proof idea: Prove the bounded measurable box belongs to `MemLp ... 2`; form its `toLp` element; rewrite
  the Lp representative's coefficients to the raw `boxWindow` coefficients with `coeFn_toLp` and
  `fourierCoeff_congr_ae`; apply Parseval; compute the squared norm integral as the Haar mass of
  the half-width interval, namely `epsilon/2`. -/
  classical
  let B : Set (AddCircle (1 : ℝ)) :=
    Theorem12.Generic.unitRep ⁻¹' Set.Icc 0 (epsilon / 2)
  have hunitMeas : Measurable Theorem12.Generic.unitRep :=
    (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable.subtype_val
  have hBmeas : MeasurableSet B := measurableSet_Icc.preimage hunitMeas
  have hbox : boxWindow epsilon = B.indicator (fun _ => (1 : ℂ)) := by
    funext x
    by_cases hx : Theorem12.Generic.unitRep x ∈ Set.Icc 0 (epsilon / 2)
    · have hxB : x ∈ B := hx
      rw [Set.indicator_of_mem hxB]
      simp [boxWindow, hx]
    · have hxB : x ∉ B := hx
      rw [Set.indicator_of_notMem hxB]
      simp [boxWindow, hx]
  have hsubset : Set.Icc 0 (epsilon / 2) ⊆ Set.Ico (0 : ℝ) 1 := by
    intro x hx
    exact ⟨hx.1, lt_of_le_of_lt hx.2 (by linarith)⟩
  have hBmeasure :
      AddCircle.haarAddCircle B = volume (Set.Icc 0 (epsilon / 2)) := by
    have h := Theorem12.Generic.measure_unitRep_preimage
      (Set.Icc 0 (epsilon / 2)) measurableSet_Icc
    rw [Set.inter_eq_left.mpr hsubset] at h
    exact h
  have hBmeasureReal : AddCircle.haarAddCircle.real B = epsilon / 2 := by
    calc
      AddCircle.haarAddCircle.real B =
          volume.real (Set.Icc 0 (epsilon / 2)) := by
            exact congrArg ENNReal.toReal hBmeasure
      _ = max (epsilon / 2 - 0) 0 := Real.volume_real_Icc
      _ = epsilon / 2 := by rw [sub_zero, max_eq_left (by linarith)]
  have hmem : MemLp (boxWindow epsilon) 2 AddCircle.haarAddCircle := by
    rw [hbox]
    exact memLp_indicator_const 2 hBmeas (1 : ℂ) (Or.inr (by finiteness))
  let F : Lp ℂ 2 AddCircle.haarAddCircle := hmem.toLp (boxWindow epsilon)
  have hcoe : (⇑F : AddCircle (1 : ℝ) → ℂ) =ᵐ[AddCircle.haarAddCircle]
      boxWindow epsilon := by
    exact hmem.coeFn_toLp
  have hnormBox :
      (fun x : AddCircle (1 : ℝ) => ‖boxWindow epsilon x‖ ^ 2) =
        B.indicator (fun _ => (1 : ℝ)) := by
    funext x
    rw [hbox]
    by_cases hx : x ∈ B <;> simp [hx]
  have hintegralBox :
      (∫ x, ‖boxWindow epsilon x‖ ^ 2 ∂AddCircle.haarAddCircle) = epsilon / 2 := by
    rw [hnormBox]
    calc
      (∫ x, B.indicator (fun _ => (1 : ℝ)) x ∂AddCircle.haarAddCircle) =
          AddCircle.haarAddCircle.real B :=
        MeasureTheory.integral_indicator_one hBmeas
      _ = epsilon / 2 := hBmeasureReal
  have hintegralF :
      (∫ x, ‖F x‖ ^ 2 ∂AddCircle.haarAddCircle) = epsilon / 2 := by
    calc
      (∫ x, ‖F x‖ ^ 2 ∂AddCircle.haarAddCircle) =
          ∫ x, ‖boxWindow epsilon x‖ ^ 2 ∂AddCircle.haarAddCircle := by
            apply integral_congr_ae
            filter_upwards [hcoe] with x hx
            rw [hx]
      _ = epsilon / 2 := hintegralBox
  have hcoeff : fourierCoeff (⇑F) = fourierCoeff (boxWindow epsilon) :=
    fourierCoeff_congr_ae hcoe
  have hparseval := hasSum_sq_fourierCoeff F
  rw [hintegralF] at hparseval
  simpa only [hcoeff] using hparseval

/- Proof idea: rewrite as the Parseval square series. -/
theorem summable_windowCoeff_and_tsum_norm
    (epsilon : ℝ) (he0 : 0 < epsilon) (he1 : epsilon < 1) :
    Summable (fun k : ℤ => ‖windowCoeff epsilon k‖) ∧
      (∑' k : ℤ, ‖windowCoeff epsilon k‖) = epsilon / 2 := by
  /- Proof idea: Rewrite `windowCoeff` as the square of the box coefficient by `windowCoeff_eq_sq_and_zero`, identify its norm
  with the squared coefficient norm, and consume the exact `HasSum` from `hasSum_sq_fourierCoeff_boxWindow`. -/
  have hcoeff := (windowCoeff_eq_sq_and_zero epsilon he0 he1).1
  have hnorm (k : ℤ) :
      ‖windowCoeff epsilon k‖ =
        ‖fourierCoeff (boxWindow epsilon) k‖ ^ 2 := by
    rw [hcoeff k, norm_pow]
  have hfun :
      (fun k : ℤ => ‖windowCoeff epsilon k‖) =
        fun k : ℤ => ‖fourierCoeff (boxWindow epsilon) k‖ ^ 2 :=
    funext hnorm
  rw [hfun]
  have hsum := hasSum_sq_fourierCoeff_boxWindow epsilon he0 he1
  exact ⟨hsum.summable, hsum.tsum_eq⟩

/- Proof idea: change variables and normalize the phase to fourier (-k) a. -/
theorem fourierCoeff_tentWindowTranslate
    (epsilon : ℝ) (he0 : 0 < epsilon) (he1 : epsilon < 1)
    (a : AddCircle (1 : ℝ)) (k : ℤ) :
    fourierCoeff (tentWindowTranslate epsilon he0 he1 a) k =
      fourier (-k) a * windowCoeff epsilon k := by
  /- Proof idea: Change variables by Haar-preserving translation and factor the character; normalize the sign
  to `-k`. -/
  have htentCont : Continuous (tentWindow epsilon) := by
    have h := (tentWindowTranslate epsilon he0 he1 0).continuous
    change Continuous (fun x => tentWindow epsilon (x - 0)) at h
    simpa only [sub_zero] using h
  have htentInt : Integrable (tentWindow epsilon) AddCircle.haarAddCircle := by
    simpa [IntegrableOn] using
      htentCont.continuousOn.integrableOn_compact
        (μ := AddCircle.haarAddCircle) isCompact_univ
  let g : AddCircle (1 : ℝ) → ℂ := fun x =>
    fourier (-k) (x + a) * tentWindow epsilon x
  have hgCont : Continuous g := by
    exact ((map_continuous (fourier (-k))).comp
      (continuous_id.add continuous_const)).mul htentCont
  have hgInt : Integrable g AddCircle.haarAddCircle := by
    simpa [IntegrableOn] using
      hgCont.continuousOn.integrableOn_compact
        (μ := AddCircle.haarAddCircle) isCompact_univ
  have hshift :
      (∫ x, g (x - a) ∂AddCircle.haarAddCircle) =
        ∫ x, g x ∂AddCircle.haarAddCircle :=
    Theorem12.Generic.integral_addCircle_sub g hgInt a
  simp only [fourierCoeff, tentWindowTranslate, windowCoeff,
    ContinuousMap.coe_mk, smul_eq_mul]
  calc
    (∫ x, fourier (-k) x * tentWindow epsilon (x - a)
        ∂AddCircle.haarAddCircle) =
        ∫ x, g (x - a) ∂AddCircle.haarAddCircle := by
          apply integral_congr_ae
          filter_upwards
          intro x
          dsimp only [g]
          rw [sub_add_cancel]
    _ = ∫ x, g x ∂AddCircle.haarAddCircle := hshift
    _ = ∫ x, fourier (-k) a *
          (fourier (-k) x * tentWindow epsilon x)
        ∂AddCircle.haarAddCircle := by
          apply integral_congr_ae
          filter_upwards
          intro x
          simp only [g, fourier_apply, zsmul_add,
            AddCircle.toCircle_add, Circle.coe_mul]
          ring
    _ = fourier (-k) a *
          ∫ x, fourier (-k) x * tentWindow epsilon x
            ∂AddCircle.haarAddCircle := by
          exact MeasureTheory.integral_const_mul _ _

end Theorem14.Internal
