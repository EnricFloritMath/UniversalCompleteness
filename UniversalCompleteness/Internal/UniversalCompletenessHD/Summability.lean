import UniversalCompletenessHD.PoleCoordinates

/-!
# Weighted orbit summability and local finiteness

The shifted comparison constant and
ENNReal pole weight are centralized in `Definitions.lean`.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace UniversalCompletenessHD.Internal

/- Apply the generic shifted quadratic-weight inequality to the
explicit pole displacement bound. -/
theorem inv_one_add_pole_sq_leHD {d : Nat} (alpha beta : RealVec d)
    (x : Torus d) (j : IntVec d) (q : Int) :
    (1 + (poleCoordHD alpha beta x j q) ^ 2)⁻¹ ≤
      quadraticShiftConstantHD beta * (1 + (q : Real) ^ 2)⁻¹ := by
  let p : Real := poleCoordHD alpha beta x j q
  let C : Real := poleShiftConstantHD beta
  let Q : Real := quadraticShiftConstantHD beta
  have hC : 0 ≤ C := by
    dsimp only [C, poleShiftConstantHD]
    positivity
  have hdist : |p - (q : Real)| ≤ C := by
    exact abs_poleCoordHD_sub_q_le alpha beta x j q
  have hdistSq : (p - (q : Real)) ^ 2 ≤ C ^ 2 :=
    sq_le_sq.mpr (by simpa [abs_of_nonneg hC] using hdist)
  have hqSq : (q : Real) ^ 2 ≤ 2 * p ^ 2 + 2 * C ^ 2 := by
    nlinarith [sq_nonneg (p + (p - (q : Real)))]
  have hbase : 1 + (q : Real) ^ 2 ≤
      (2 * (1 + C ^ 2)) * (1 + p ^ 2) := by
    have hcross : 0 ≤ C ^ 2 * p ^ 2 := mul_nonneg (sq_nonneg C) (sq_nonneg p)
    nlinarith [sq_nonneg p, sq_nonneg C]
  have hconst : 2 * (1 + C ^ 2) ≤ Q := by
    dsimp only [Q, quadraticShiftConstantHD, C]
    nlinarith [sq_nonneg (1 + poleShiftConstantHD beta),
      sq_nonneg (poleShiftConstantHD beta)]
  have hden : 1 + (q : Real) ^ 2 ≤ Q * (1 + p ^ 2) :=
    hbase.trans (mul_le_mul_of_nonneg_right hconst (by positivity))
  have hdiv : (1 : Real) / (1 + p ^ 2) ≤
      Q / (1 + (q : Real) ^ 2) :=
    (div_le_div_iff₀ (by positivity : 0 < 1 + p ^ 2)
      (by positivity : 0 < 1 + (q : Real) ^ 2)).2 (by simpa using hden)
  simpa [p, Q, div_eq_mul_inv] using hdiv

/- Compose measurable torus translations, the fixed
representative, norm, denominator, and indicator operations. -/
theorem aemeasurable_poleWeightENNHD {d : Nat}
    {dataAlpha dataBeta : RealVec d} {S : Set (RealVec d)}
    {f : RealVec d → Complex} (data : PositiveInputDataHD dataAlpha dataBeta S f)
    (alpha beta : RealVec d) (a : IntVec d × Int) :
    AEMeasurable (fun x : Torus d ↦ poleWeightENNHD data alpha beta x a)
      volume := by
  classical
  have hrep : Measurable (torusToCubeHD : Torus d → RealVec d) := by
    change Measurable (fun z : Torus d ↦
      ((torusIocEquivHD d z).1 : RealVec d))
    exact measurable_subtype_coe.comp (torusIocEquivHD d).measurable
  have hu : Measurable (fun x : Torus d ↦
      uCoordHD alpha beta x a.1 a.2) := by
    unfold uCoordHD uOrbitHD
    fun_prop
  have hslice : Measurable (fun x : Torus d ↦
      cubeSlice data a.1 (uCoordHD alpha beta x a.1 a.2)) := by
    unfold cubeSlice intVecTranslate
    exact data.stronglyMeasurable_H0.measurable.comp
      (measurable_const.add (hrep.comp hu))
  have hraw : Measurable (fun x : Torus d ↦
      rawPhaseHD beta a.1 (uCoordHD alpha beta x a.1 a.2)) := by
    unfold rawPhaseHD dotReal
    fun_prop
  have hpole : Measurable (fun x : Torus d ↦
      poleCoordHD alpha beta x a.1 a.2) := by
    unfold poleCoordHD
    fun_prop
  have hres : Measurable (fun x : Torus d ↦
      residueCoordHD data alpha beta x a.1 a.2) := by
    unfold residueCoordHD
    fun_prop
  have hactive : Measurable (fun x : Torus d ↦
      if residueCoordHD data alpha beta x a.1 a.2 ≠ 0
        then (1 : ENNReal) else 0) := by
    apply Measurable.ite
    · convert (hres (measurableSet_singleton (0 : Complex))).compl using 1
      ext y
      simp
    · exact measurable_const
    · exact measurable_const
  exact ((hres.norm.ennreal_ofReal.add hactive).div
    ((measurable_const.add (hpole.pow_const 2)).ennreal_ofReal)).aemeasurable

/- Translate the orbit coordinate to a free torus variable,
bound residue norm and the total indicator by the corresponding slice terms,
and apply the quadratic comparison. -/
theorem lintegral_poleWeightENNHD_le {d : Nat}
    {dataAlpha dataBeta : RealVec d} {S : Set (RealVec d)}
    {f : RealVec d → Complex} (data : PositiveInputDataHD dataAlpha dataBeta S f)
    (alpha beta : RealVec d) (j : IntVec d) (q : Int) :
    (∫⁻ x : Torus d, poleWeightENNHD data alpha beta x (j, q) ∂volume) ≤
      ENNReal.ofReal
          (quadraticShiftConstantHD beta / (1 + (q : Real) ^ 2)) *
        (ENNReal.ofReal
            (∫ u : Torus d, ‖cubeSlice data j u‖ ∂volume) +
          volume (cubeSliceSupport data j)) := by
  classical
  let shift : Torus d :=
    ellIndexHD beta j q • alphaTorusHD alpha
  let A : Torus d → ENNReal := fun u ↦ ENNReal.ofReal ‖cubeSlice data j u‖
  let B : Torus d → ENNReal := fun u ↦
    if cubeSlice data j u ≠ 0 then 1 else 0
  let C : ENNReal := ENNReal.ofReal
    (quadraticShiftConstantHD beta / (1 + (q : Real) ^ 2))
  have hrep : Measurable (torusToCubeHD : Torus d → RealVec d) := by
    change Measurable (fun z : Torus d ↦
      ((torusIocEquivHD d z).1 : RealVec d))
    exact measurable_subtype_coe.comp (torusIocEquivHD d).measurable
  have hslice : Measurable (cubeSlice data j) := by
    unfold cubeSlice intVecTranslate
    exact data.stronglyMeasurable_H0.measurable.comp
      (measurable_const.add hrep)
  have hA : Measurable A := hslice.norm.ennreal_ofReal
  have hB : Measurable B := by
    apply Measurable.ite
    · convert (hslice (measurableSet_singleton (0 : Complex))).compl using 1
      ext u
      simp
    · exact measurable_const
    · exact measurable_const
  have hu : Measurable (fun x : Torus d ↦
      uCoordHD alpha beta x j q) := by
    unfold uCoordHD uOrbitHD
    fun_prop
  have hdenENN (x : Torus d) :
      (ENNReal.ofReal (1 + (poleCoordHD alpha beta x j q) ^ 2))⁻¹ ≤ C := by
    rw [← ENNReal.ofReal_inv_of_pos (by positivity :
      (0 : Real) < 1 + (poleCoordHD alpha beta x j q) ^ 2)]
    apply ENNReal.ofReal_le_ofReal
    simpa [C, div_eq_mul_inv] using
      inv_one_add_pole_sq_leHD alpha beta x j q
  have hresnorm (x : Torus d) :
      ‖residueCoordHD data alpha beta x j q‖ ≤
        ‖cubeSlice data j (uCoordHD alpha beta x j q)‖ := by
    have hsin :
        |Real.sin (Real.pi * rawPhaseHD beta j
          (uCoordHD alpha beta x j q))| ≤ 1 :=
      abs_le.2 ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
    have hpi : (1 : Real) ≤ |Real.pi| := by
      rw [abs_of_pos Real.pi_pos]
      linarith [Real.two_le_pi]
    have hratio :
        |Real.sin (Real.pi * rawPhaseHD beta j
          (uCoordHD alpha beta x j q))| / |Real.pi| ≤ 1 :=
      (div_le_one (abs_pos.mpr Real.pi_ne_zero)).2 (hsin.trans hpi)
    change ‖((Real.sin (Real.pi * rawPhaseHD beta j
        (uCoordHD alpha beta x j q)) : Real) : Complex) /
        (Real.pi : Complex) * cubeSlice data j
          (uCoordHD alpha beta x j q)‖ ≤ _
    rw [norm_mul, norm_div, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs]
    simpa [abs_of_pos Real.pi_pos] using
      (mul_le_mul_of_nonneg_right hratio
        (norm_nonneg (cubeSlice data j (uCoordHD alpha beta x j q))))
  have hpoint (x : Torus d) :
      poleWeightENNHD data alpha beta x (j, q) ≤
        C * (A (uCoordHD alpha beta x j q) +
          B (uCoordHD alpha beta x j q)) := by
    have hnum :
        ENNReal.ofReal ‖residueCoordHD data alpha beta x j q‖ +
            (if residueCoordHD data alpha beta x j q ≠ 0
              then 1 else 0) ≤
          A (uCoordHD alpha beta x j q) +
            B (uCoordHD alpha beta x j q) :=
      add_le_add (ENNReal.ofReal_le_ofReal (hresnorm x))
        (residue_indicator_le_slice_indicatorHD
          data alpha beta x j q)
    rw [poleWeightENNHD, div_eq_mul_inv]
    calc
      (ENNReal.ofReal ‖residueCoordHD data alpha beta x j q‖ +
          if residueCoordHD data alpha beta x j q ≠ 0 then 1 else 0) *
          (ENNReal.ofReal
            (1 + (poleCoordHD alpha beta x j q) ^ 2))⁻¹ ≤
        (A (uCoordHD alpha beta x j q) +
          B (uCoordHD alpha beta x j q)) * C :=
        mul_le_mul hnum (hdenENN x) bot_le bot_le
      _ = C * (A (uCoordHD alpha beta x j q) +
          B (uCoordHD alpha beta x j q)) := mul_comm _ _
  have hu_eq (x : Torus d) :
      uCoordHD alpha beta x j q = x - shift := by
    rfl
  have hlinA :
      (∫⁻ x : Torus d, A (uCoordHD alpha beta x j q) ∂volume) =
        ENNReal.ofReal (∫ u : Torus d, ‖cubeSlice data j u‖ ∂volume) := by
    let mu : Measure (Torus d) := volume
    change (∫⁻ x : Torus d, A (uCoordHD alpha beta x j q) ∂mu) =
      ENNReal.ofReal (∫ u : Torus d, ‖cubeSlice data j u‖ ∂mu)
    simp_rw [hu_eq]
    rw [(measurePreserving_sub_right volume shift).lintegral_comp hA]
    letI : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
    let nu : Measure (Torus d) := volume
    have hmunu : mu = nu := by
      dsimp [mu, nu]
      change Measure.pi
          (fun _ : Fin d ↦ @volume UnitAddCircle (AddCircle.measureSpace 1)) =
        Measure.pi (fun _ : Fin d ↦ AddCircle.haarAddCircle)
      congr 1
      funext i
      change ENNReal.ofReal 1 • Measure.addHaarMeasure ⊤ =
        Measure.addHaarMeasure ⊤
      simp
    have h := (ofReal_integral_eq_lintegral_ofReal
      (integrable_cubeSlice data j).norm
      (ae_of_all _ fun u ↦ norm_nonneg (cubeSlice data j u))).symm
    change (∫⁻ u : Torus d, ENNReal.ofReal ‖cubeSlice data j u‖ ∂nu) =
      ENNReal.ofReal (∫ u : Torus d, ‖cubeSlice data j u‖ ∂nu) at h
    rw [← hmunu] at h
    exact h
  have hlinB :
      (∫⁻ x : Torus d, B (uCoordHD alpha beta x j q) ∂volume) =
        volume (cubeSliceSupport data j) := by
    simp_rw [hu_eq]
    rw [(measurePreserving_sub_right volume shift).lintegral_comp hB]
    simpa [B, cubeSliceSupport, Set.indicator] using
      (lintegral_indicator_one (measurableSet_cubeSliceSupport data j) :
        (∫⁻ u : Torus d, (cubeSliceSupport data j).indicator 1 u
          ∂volume) = volume (cubeSliceSupport data j))
  calc
    (∫⁻ x : Torus d, poleWeightENNHD data alpha beta x (j, q)
        ∂volume) ≤
      ∫⁻ x : Torus d,
        C * (A (uCoordHD alpha beta x j q) +
          B (uCoordHD alpha beta x j q)) ∂volume := lintegral_mono hpoint
    _ = C * (∫⁻ x : Torus d,
        A (uCoordHD alpha beta x j q) +
          B (uCoordHD alpha beta x j q) ∂volume) :=
      lintegral_const_mul C ((hA.comp hu).add (hB.comp hu))
    _ = C * ((∫⁻ x : Torus d,
        A (uCoordHD alpha beta x j q) ∂volume) +
          ∫⁻ x : Torus d,
            B (uCoordHD alpha beta x j q) ∂volume) := by
      congr 1
      simpa only [Function.comp_apply] using
        (lintegral_add_left (hA.comp hu)
          (fun x : Torus d ↦ B (uCoordHD alpha beta x j q)))
    _ = C * (ENNReal.ofReal
        (∫ u : Torus d, ‖cubeSlice data j u‖ ∂volume) +
          volume (cubeSliceSupport data j)) := by rw [hlinA, hlinB]
    _ = ENNReal.ofReal
          (quadraticShiftConstantHD beta / (1 + (q : Real) ^ 2)) *
        (ENNReal.ofReal
            (∫ u : Torus d, ‖cubeSlice data j u‖ ∂volume) +
          volume (cubeSliceSupport data j)) := rfl

/- Apply Tonelli, sum first in the scalar row index and then in
the integer-vector layer, using both exact layer sums. -/
theorem lintegral_tsum_poleWeightENNHD_lt_top {d : Nat}
    {dataAlpha dataBeta : RealVec d} {S : Set (RealVec d)}
    {f : RealVec d → Complex} (data : PositiveInputDataHD dataAlpha dataBeta S f)
    (alpha beta : RealVec d) (hSupportFinite : supportMassENNHD data ≠ ∞) :
    (∫⁻ x : Torus d,
      ∑' a : IntVec d × Int, poleWeightENNHD data alpha beta x a ∂volume) < ∞ := by
  let Q : Real := quadraticShiftConstantHD beta
  let D : Int → ENNReal := fun q ↦
    ENNReal.ofReal (Q / (1 + (q : Real) ^ 2))
  let N : IntVec d → ENNReal := fun j ↦
    ENNReal.ofReal (∫ u : Torus d, ‖cubeSlice data j u‖ ∂volume)
  let M : IntVec d → ENNReal := fun j ↦ volume (cubeSliceSupport data j)
  let W : IntVec d → ENNReal := fun j ↦ N j + M j
  have hD_eq (q : Int) :
      D q = ENNReal.ofReal (Q * (1 + (q : Real) ^ 2)⁻¹) := by
    simp only [D, div_eq_mul_inv]
  have hDlt : (∑' q : Int, D q) < ∞ := by
    simp_rw [hD_eq]
    exact (summable_one_add_int_sq_inv.mul_left Q).tsum_ofReal_lt_top
  have hNlt : (∑' j : IntVec d, N j) < ∞ := by
    let mu : Measure (Torus d) := volume
    change (∑' j : IntVec d,
      ENNReal.ofReal (∫ u : Torus d, ‖cubeSlice data j u‖ ∂mu)) < ∞
    letI : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
    let nu : Measure (Torus d) := volume
    have hmunu : mu = nu := by
      dsimp [mu, nu]
      change Measure.pi
          (fun _ : Fin d ↦ @volume UnitAddCircle (AddCircle.measureSpace 1)) =
        Measure.pi (fun _ : Fin d ↦ AddCircle.haarAddCircle)
      congr 1
      funext i
      change ENNReal.ofReal 1 • Measure.addHaarMeasure ⊤ =
        Measure.addHaarMeasure ⊤
      simp
    have h := (hasSum_cubeSlice_L1_norm data).summable.tsum_ofReal_lt_top
    change (∑' j : IntVec d,
      ENNReal.ofReal (∫ u : Torus d, ‖cubeSlice data j u‖ ∂nu)) < ∞ at h
    rw [← hmunu] at h
    exact h
  have hMlt : (∑' j : IntVec d, M j) < ∞ := by
    let mu : Measure (Torus d) := volume
    letI : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
    let nu : Measure (Torus d) := volume
    have hmunu : mu = nu := by
      dsimp [mu, nu]
      change Measure.pi
          (fun _ : Fin d ↦ @volume UnitAddCircle (AddCircle.measureSpace 1)) =
        Measure.pi (fun _ : Fin d ↦ AddCircle.haarAddCircle)
      congr 1
      funext i
      change ENNReal.ofReal 1 • Measure.addHaarMeasure ⊤ =
        Measure.addHaarMeasure ⊤
      simp
    rw [show (∑' j : IntVec d, M j) = supportMassENNHD data by
      rw [supportMassENNHD]
      apply tsum_congr
      intro j
      dsimp only [M]
      exact congrArg (fun m : Measure (Torus d) ↦
        m (cubeSliceSupport data j)) hmunu]
    exact lt_top_iff_ne_top.mpr hSupportFinite
  have hWlt : (∑' j : IntVec d, W j) < ∞ := by
    rw [show (∑' j : IntVec d, W j) =
        (∑' j : IntVec d, N j) + ∑' j : IntVec d, M j by
      simpa [W] using (@ENNReal.tsum_add (IntVec d) N M)]
    exact ENNReal.add_lt_top.mpr ⟨hNlt, hMlt⟩
  have hmajor_eq :
      (∑' a : IntVec d × Int, D a.2 * W a.1) =
        (∑' q : Int, D q) * ∑' j : IntVec d, W j := by
    rw [ENNReal.tsum_prod']
    simp_rw [ENNReal.tsum_mul_right]
    rw [ENNReal.tsum_mul_left]
  have hmajor_lt :
      (∑' a : IntVec d × Int, D a.2 * W a.1) < ∞ := by
    rw [hmajor_eq]
    exact ENNReal.mul_lt_top hDlt hWlt
  rw [lintegral_tsum fun a ↦
    aemeasurable_poleWeightENNHD data alpha beta a]
  refine (ENNReal.tsum_le_tsum fun a ↦ ?_).trans_lt hmajor_lt
  simpa [Q, D, N, M, W] using
    lintegral_poleWeightENNHD_le data alpha beta a.1 a.2

/- A finite lintegral forces the nonnegative integrand to be
finite almost everywhere. -/
theorem poleWeight_tsum_lt_top_aeHD {d : Nat}
    {dataAlpha dataBeta : RealVec d} {S : Set (RealVec d)}
    {f : RealVec d → Complex} (data : PositiveInputDataHD dataAlpha dataBeta S f)
    (alpha beta : RealVec d) (hSupportFinite : supportMassENNHD data ≠ ∞) :
    ∀ᵐ x : Torus d ∂volume,
      (∑' a : IntVec d × Int, poleWeightENNHD data alpha beta x a) < ∞ := by
  apply ae_lt_top' (AEMeasurable.tsum fun a ↦
    aemeasurable_poleWeightENNHD data alpha beta a)
  exact (lintegral_tsum_poleWeightENNHD_lt_top data alpha beta
    hSupportFinite).ne

/- Compare the real residue family with the finite ENNReal
pole-weight total and convert summability. -/
theorem summable_residue_weightHD {d : Nat}
    {dataAlpha dataBeta : RealVec d} {S : Set (RealVec d)}
    {f : RealVec d → Complex} (data : PositiveInputDataHD dataAlpha dataBeta S f)
    (alpha beta : RealVec d) (x : Torus d)
    (hfinite :
      (∑' a : IntVec d × Int, poleWeightENNHD data alpha beta x a) < ∞) :
    Summable (fun a : IntVec d × Int ↦
      ‖residueCoordHD data alpha beta x a.1 a.2‖ /
        (1 + (poleCoordHD alpha beta x a.1 a.2) ^ 2)) := by
  classical
  let W : IntVec d × Int → Real := fun a ↦
    (poleWeightENNHD data alpha beta x a).toReal
  have hW : Summable W := ENNReal.summable_toReal hfinite.ne
  have hW_eq (a : IntVec d × Int) :
      W a = (‖residueCoordHD data alpha beta x a.1 a.2‖ +
          if residueCoordHD data alpha beta x a.1 a.2 ≠ 0
            then (1 : Real) else 0) /
        (1 + (poleCoordHD alpha beta x a.1 a.2) ^ 2) := by
    have hden : 0 ≤ 1 + (poleCoordHD alpha beta x a.1 a.2) ^ 2 := by
      positivity
    simp only [W, poleWeightENNHD, ENNReal.toReal_div]
    rw [ENNReal.toReal_ofReal hden]
    by_cases ha : residueCoordHD data alpha beta x a.1 a.2 ≠ 0
    · rw [ENNReal.toReal_add ENNReal.ofReal_ne_top (by simp [ha])]
      simp [ha]
    · simp [not_ne_iff.mp ha]
  refine Summable.of_nonneg_of_le (fun a ↦ by positivity) (fun a ↦ ?_) hW
  rw [hW_eq]
  apply div_le_div_of_nonneg_right
  · split_ifs <;> simp
  · positivity

/- Independently extract summability of the active-indicator
quadratic-weight family. -/
theorem summable_active_indicator_weightHD {d : Nat}
    {dataAlpha dataBeta : RealVec d} {S : Set (RealVec d)}
    {f : RealVec d → Complex} (data : PositiveInputDataHD dataAlpha dataBeta S f)
    (alpha beta : RealVec d) (x : Torus d)
    (hfinite :
      (∑' a : IntVec d × Int, poleWeightENNHD data alpha beta x a) < ∞) :
    Summable (fun a : IntVec d × Int ↦
      if residueCoordHD data alpha beta x a.1 a.2 ≠ 0 then
        (1 + (poleCoordHD alpha beta x a.1 a.2) ^ 2)⁻¹
      else 0) := by
  classical
  let W : IntVec d × Int → Real := fun a ↦
    (poleWeightENNHD data alpha beta x a).toReal
  have hW : Summable W := ENNReal.summable_toReal hfinite.ne
  have hW_eq (a : IntVec d × Int) :
      W a = (‖residueCoordHD data alpha beta x a.1 a.2‖ +
          if residueCoordHD data alpha beta x a.1 a.2 ≠ 0
            then (1 : Real) else 0) /
        (1 + (poleCoordHD alpha beta x a.1 a.2) ^ 2) := by
    have hden : 0 ≤ 1 + (poleCoordHD alpha beta x a.1 a.2) ^ 2 := by
      positivity
    simp only [W, poleWeightENNHD, ENNReal.toReal_div]
    rw [ENNReal.toReal_ofReal hden]
    by_cases ha : residueCoordHD data alpha beta x a.1 a.2 ≠ 0
    · rw [ENNReal.toReal_add ENNReal.ofReal_ne_top (by simp [ha])]
      simp [ha]
    · simp [not_ne_iff.mp ha]
  refine Summable.of_nonneg_of_le (fun a ↦ by
    split_ifs <;> positivity) (fun a ↦ ?_) hW
  rw [hW_eq]
  by_cases ha : residueCoordHD data alpha beta x a.1 a.2 ≠ 0
  · simp only [if_pos ha]
    rw [div_eq_mul_inv]
    nth_rewrite 1 [← one_mul
      (1 + (poleCoordHD alpha beta x a.1 a.2) ^ 2)⁻¹]
    apply mul_le_mul_of_nonneg_right
    · simp
    · positivity
  · simp only [if_neg ha]
    positivity

/- On a bounded pole interval each active term has a fixed
positive lower bound; summability therefore makes the active superlevel set
finite. -/
theorem finite_activePole_IccHD {d : Nat}
    {dataAlpha dataBeta : RealVec d} {S : Set (RealVec d)}
    {f : RealVec d → Complex} (data : PositiveInputDataHD dataAlpha dataBeta S f)
    (alpha beta : RealVec d) (x : Torus d)
    (hfinite :
      (∑' a : IntVec d × Int, poleWeightENNHD data alpha beta x a) < ∞)
    (R : Real) (hR : 0 ≤ R) :
    Set.Finite {a : IntVec d × Int |
      residueCoordHD data alpha beta x a.1 a.2 ≠ 0 ∧
        poleCoordHD alpha beta x a.1 a.2 ∈ Set.Icc (-R) R} := by
  classical
  let w : IntVec d × Int → Real := fun a ↦
    if residueCoordHD data alpha beta x a.1 a.2 ≠ 0 then
      (1 + (poleCoordHD alpha beta x a.1 a.2) ^ 2)⁻¹
    else 0
  have hw : Summable w := by
    simpa only [w] using
      summable_active_indicator_weightHD data alpha beta x hfinite
  have hsuper : Set.Finite {a : IntVec d × Int |
      (1 + R ^ 2)⁻¹ ≤ w a} :=
    Theorem12.Generic.Summable.finite_set_le_of_pos w (fun a ↦ by
      simp only [w]
      positivity) hw (by positivity)
  refine hsuper.subset ?_
  intro a ha
  rcases ha with ⟨haActive, haIcc⟩
  have habs : |poleCoordHD alpha beta x a.1 a.2| ≤ R :=
    abs_le.2 ⟨haIcc.1, haIcc.2⟩
  have hsq : (poleCoordHD alpha beta x a.1 a.2) ^ 2 ≤ R ^ 2 :=
    sq_le_sq.mpr (by simpa [abs_of_nonneg hR] using habs)
  have hinv : (1 + R ^ 2)⁻¹ ≤
      (1 + (poleCoordHD alpha beta x a.1 a.2) ^ 2)⁻¹ :=
    (inv_le_inv₀ (by positivity) (by positivity)).2 (by linarith)
  simpa [w, haActive] using hinv

end UniversalCompletenessHD.Internal
