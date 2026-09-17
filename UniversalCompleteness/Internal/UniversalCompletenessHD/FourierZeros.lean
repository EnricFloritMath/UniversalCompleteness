import UniversalCompletenessHD.MeromorphicSeries
import UniversalCompletenessHD.SincIdentity
import UniversalCompletenessHD.FourierUniqueness

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace UniversalCompletenessHD.Internal

/- Proof idea: unfold the good branch of `intEvalSummandHD`, substitute the exact
floor/parity and pole normal forms, prove both denominators nonzero, and normalize fields. -/
theorem intEvalSummandHD_eq_sourceKernel (P : Params) {S : Set (RealVec P.d)}
    {f : RealVec P.d → Complex}
    (data : PositiveInputDataHD P.alpha P.beta S f) (k : Int) (x : Torus P.d)
    (j : IntVec P.d) (q : Int) (hx : x ∉ sineBadHD P.alpha P.beta) :
    intEvalSummandHD data k x (j, q) =
      residueCoordHD data P.alpha P.beta x j q *
        (((k : Complex) - (poleCoordHD P.alpha P.beta x j q : Complex))⁻¹ +
          (poleCoordHD P.alpha P.beta x j q : Complex)⁻¹) := by
  have hkernel :
      (((reducedPhaseHD P.alpha P.beta x j q - (q : Real) + (k : Real) : Real) :
            Complex))⁻¹ -
          (((reducedPhaseHD P.alpha P.beta x j q - (q : Real) : Real) :
            Complex))⁻¹ =
        ((k : Complex) -
            (((q : Real) - reducedPhaseHD P.alpha P.beta x j q : Real) : Complex))⁻¹ +
          ((((q : Real) - reducedPhaseHD P.alpha P.beta x j q : Real) :
            Complex))⁻¹ := by
    have hfirst :
        (((reducedPhaseHD P.alpha P.beta x j q - (q : Real) + (k : Real) : Real) :
            Complex)) =
          (k : Complex) -
            (((q : Real) - reducedPhaseHD P.alpha P.beta x j q : Real) : Complex) := by
      push_cast
      ring
    have hsecond :
        (((reducedPhaseHD P.alpha P.beta x j q - (q : Real) : Real) : Complex)) =
          -((((q : Real) - reducedPhaseHD P.alpha P.beta x j q : Real) : Complex)) := by
      push_cast
      ring
    rw [hfirst, hsecond, inv_neg, sub_neg_eq_add]
  unfold intEvalSummandHD
  rw [if_neg hx]
  unfold sincShiftCoeffHD Theorem12.Generic.sincShiftCoeff residueCoordHD
  rw [sin_rawPhaseHD_eq_intParity_mul_sin_reducedPhaseHD,
    poleCoordHD_eq_q_sub_reducedPhaseHD]
  rw [hkernel]
  ring

/- Proof idea: close the guarded raw expression under measurable arithmetic and inversion;
the bad set and the fixed canonical slice representative are measurable. -/
theorem aemeasurable_intEvalSummandHD (P : Params) {S : Set (RealVec P.d)}
    {f : RealVec P.d → Complex}
    (data : PositiveInputDataHD P.alpha P.beta S f) (k : Int)
    (a : IntVec P.d × Int) :
    AEMeasurable (fun x : Torus P.d => intEvalSummandHD data k x a) volume := by
  have hrep : Measurable (torusToCubeHD : Torus P.d → RealVec P.d) := by
    change Measurable (fun z : Torus P.d ↦
      ((torusIocEquivHD P.d z).1 : RealVec P.d))
    exact measurable_subtype_coe.comp (torusIocEquivHD P.d).measurable
  have hu : Measurable (fun x : Torus P.d ↦
      uCoordHD P.alpha P.beta x a.1 a.2) := by
    unfold uCoordHD uOrbitHD
    fun_prop
  have hslice : Measurable (fun x : Torus P.d ↦
      cubeSlice data a.1 (uCoordHD P.alpha P.beta x a.1 a.2)) := by
    unfold cubeSlice intVecTranslate
    exact data.stronglyMeasurable_H0.measurable.comp
      (measurable_const.add (hrep.comp hu))
  have hphase : Measurable (fun x : Torus P.d ↦
      reducedPhaseHD P.alpha P.beta x a.1 a.2) := by
    unfold reducedPhaseHD dotReal
    fun_prop
  have hgood : Measurable (fun x : Torus P.d ↦
      intParityHD (floorBetaDot P.beta a.1) *
        cubeSlice data a.1 (uCoordHD P.alpha P.beta x a.1 a.2) *
        sincShiftCoeffHD k (reducedPhaseHD P.alpha P.beta x a.1 a.2) a.2) := by
    unfold sincShiftCoeffHD Theorem12.Generic.sincShiftCoeff
    fun_prop
  have hoff : ∀ᵐ x : Torus P.d ∂volume,
      x ∉ sineBadHD P.alpha P.beta :=
    measure_eq_zero_iff_ae_notMem.mp (sineBadHD_null P)
  exact hgood.aemeasurable.congr <| hoff.mono fun x hx ↦ by
    simp only [intEvalSummandHD, hx, if_false]

/- Proof idea: change variables to `uCoordHD`, apply the phase-uniform shifted-sinc
`l1` certificate pointwise in the integer row, then use Tonelli and the layer L1 sum. -/
theorem summable_integral_norm_intEvalSummandHD (P : Params)
    {S : Set (RealVec P.d)} {f : RealVec P.d → Complex}
    (data : PositiveInputDataHD P.alpha P.beta S f) (k : Int) :
    Summable (fun a : IntVec P.d × Int =>
      ∫ x : Torus P.d, ‖intEvalSummandHD data k x a‖ ∂volume) := by
  classical
  obtain ⟨Ck, hCk, hsinc⟩ := sincShiftCoeff_uniform_l1 k
  have hvolume : (volume : Measure (Torus P.d)) =
      Measure.pi (fun _ : Fin P.d ↦ AddCircle.haarAddCircle) := by
    rw [volume_pi]
    congr 1
    funext i
    simpa using
      (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : Real)))
  have hsliceInt (j : IntVec P.d) : Integrable (cubeSlice data j) volume := by
    rw [hvolume]
    change Integrable (cubeSlice data j)
      (Measure.pi (fun _ : Fin P.d ↦ AddCircle.haarAddCircle))
    exact integrable_cubeSlice data j
  have hsinc_all (t : Real) :
      Summable (fun q : Int ↦ ‖sincShiftCoeffHD k t q‖) ∧
        (∑' q : Int, ‖sincShiftCoeffHD k t q‖) ≤ Ck := by
    by_cases ht : ∀ r : Int, t ≠ (r : Real)
    · exact hsinc t ht
    · have ht' : ∃ r : Int, t = (r : Real) := by
        simpa only [not_forall, not_ne_iff] using ht
      obtain ⟨r, rfl⟩ := ht'
      have hzero (q : Int) : sincShiftCoeffHD k (r : Real) q = 0 := by
        unfold sincShiftCoeffHD Theorem12.Generic.sincShiftCoeff
        rw [mul_comm Real.pi (r : Real)]
        rw [Real.sin_int_mul_pi]
        simp
      constructor
      · simp [hzero]
      · simp [hzero, hCk]
  have hrep : Measurable (torusToCubeHD : Torus P.d → RealVec P.d) := by
    change Measurable (fun z : Torus P.d ↦
      ((torusIocEquivHD P.d z).1 : RealVec P.d))
    exact measurable_subtype_coe.comp (torusIocEquivHD P.d).measurable
  have hphase (j : IntVec P.d) : Measurable
      (translatedPhaseHD P.beta j : Torus P.d → Real) := by
    unfold translatedPhaseHD dotReal
    fun_prop
  let U : IntVec P.d → Int → Torus P.d → Real := fun j q u ↦
    ‖cubeSlice data j u‖ *
      ‖sincShiftCoeffHD k (translatedPhaseHD P.beta j u) q‖
  have hcoeff_le (j : IntVec P.d) (q : Int) (u : Torus P.d) :
      ‖sincShiftCoeffHD k (translatedPhaseHD P.beta j u) q‖ ≤ Ck := by
    have h := hsinc_all (translatedPhaseHD P.beta j u)
    calc
      ‖sincShiftCoeffHD k (translatedPhaseHD P.beta j u) q‖ ≤
          ∑' r : Int, ‖sincShiftCoeffHD k (translatedPhaseHD P.beta j u) r‖ := by
        simpa using h.1.sum_le_tsum {q} (fun r _ ↦ norm_nonneg _)
      _ ≤ Ck := h.2
  have hUint (j : IntVec P.d) (q : Int) :
      Integrable (U j q) volume := by
    have hsincMeas : Measurable (fun u : Torus P.d ↦
        ‖sincShiftCoeffHD k (translatedPhaseHD P.beta j u) q‖) := by
      unfold sincShiftCoeffHD Theorem12.Generic.sincShiftCoeff
      fun_prop
    have hUmeas : AEStronglyMeasurable (U j q) volume := by
      exact (hsliceInt j).norm.aestronglyMeasurable.mul
        hsincMeas.aestronglyMeasurable
    refine Integrable.mono'
      ((hsliceInt j).norm.const_mul Ck) hUmeas ?_
    filter_upwards with u
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · simpa only [U, mul_comm] using
        mul_le_mul_of_nonneg_left (hcoeff_le j q u)
          (norm_nonneg (cubeSlice data j u))
    · exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
  let B : IntVec P.d → Int → Real := fun j q ↦ ∫ u : Torus P.d, U j q u ∂volume
  have hB_nonneg (j : IntVec P.d) (q : Int) : 0 ≤ B j q := by
    exact integral_nonneg fun _ ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hB_finset (j : IntVec P.d) (s : Finset Int) :
      ∑ q ∈ s, B j q ≤
        (∫ u : Torus P.d, ‖cubeSlice data j u‖ ∂volume) * Ck := by
    rw [← integral_finsetSum s (fun q _ ↦ hUint j q)]
    have hupper : Integrable (fun u : Torus P.d ↦
        ‖cubeSlice data j u‖ * Ck) volume :=
      (hsliceInt j).norm.mul_const Ck
    calc
      (∫ u : Torus P.d, ∑ q ∈ s, U j q u ∂volume) ≤
          ∫ u : Torus P.d, ‖cubeSlice data j u‖ * Ck ∂volume := by
        apply integral_mono_of_nonneg
        · filter_upwards with u
          exact Finset.sum_nonneg fun q _ ↦
            mul_nonneg (norm_nonneg _) (norm_nonneg _)
        · exact hupper
        · filter_upwards with u
          change ∑ q ∈ s,
              ‖cubeSlice data j u‖ *
                ‖sincShiftCoeffHD k (translatedPhaseHD P.beta j u) q‖ ≤
            ‖cubeSlice data j u‖ * Ck
          rw [← Finset.mul_sum]
          exact mul_le_mul_of_nonneg_left
            ((hsinc_all (translatedPhaseHD P.beta j u)).1.sum_le_tsum s
              (fun q _ ↦ norm_nonneg _)
              |>.trans (hsinc_all (translatedPhaseHD P.beta j u)).2)
            (norm_nonneg _)
      _ = (∫ u : Torus P.d, ‖cubeSlice data j u‖ ∂volume) * Ck := by
        rw [integral_mul_const]
  have hBsum (j : IntVec P.d) : Summable (B j) :=
    summable_of_sum_le (hB_nonneg j) (hB_finset j)
  have hphase_eq (x : Torus P.d) (j : IntVec P.d) (q : Int) :
      reducedPhaseHD P.alpha P.beta x j q =
        translatedPhaseHD P.beta j (uCoordHD P.alpha P.beta x j q) := by
    have h := rawPhaseHD_eq_floor_add_reducedPhaseHD
      P.alpha P.beta x j q
    rw [translatedPhaseHD]
    change reducedPhaseHD P.alpha P.beta x j q =
      rawPhaseHD P.beta j (uCoordHD P.alpha P.beta x j q) -
        (floorBetaDot P.beta j : Real)
    linarith
  let G : IntVec P.d → Int → Real := fun j q ↦
    ∫ x : Torus P.d, ‖intEvalSummandHD data k x (j, q)‖ ∂volume
  have hG_nonneg (j : IntVec P.d) (q : Int) : 0 ≤ G j q :=
    integral_nonneg fun _ ↦ norm_nonneg _
  have hG_le_B (j : IntVec P.d) (q : Int) : G j q ≤ B j q := by
    let shift : Torus P.d :=
      ellIndexHD P.beta j q • alphaTorusHD P.alpha
    have hpoint (x : Torus P.d) :
        ‖intEvalSummandHD data k x (j, q)‖ ≤
          U j q (uCoordHD P.alpha P.beta x j q) := by
      by_cases hx : x ∈ sineBadHD P.alpha P.beta
      · simp only [intEvalSummandHD, hx, if_pos, norm_zero]
        exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
      · simp only [intEvalSummandHD, hx, if_false, norm_mul]
        rw [show ‖intParityHD (floorBetaDot P.beta j)‖ = 1 by
          simp [intParityHD], one_mul, hphase_eq]
    calc
      G j q ≤ ∫ x : Torus P.d,
          U j q (uCoordHD P.alpha P.beta x j q) ∂volume :=
        integral_mono_of_nonneg (ae_of_all _ fun x ↦ norm_nonneg _)
          ((hUint j q).comp_sub_right shift)
          (ae_of_all _ hpoint)
      _ = B j q := by
        change (∫ x : Torus P.d, U j q (x - shift) ∂volume) = _
        exact MeasureTheory.integral_sub_right_eq_self (U j q) shift
  have hGrow (j : IntVec P.d) : Summable (G j) :=
    Summable.of_nonneg_of_le (hG_nonneg j) (hG_le_B j) (hBsum j)
  have hGrow_bound (j : IntVec P.d) :
      (∑' q : Int, G j q) ≤
        (∫ u : Torus P.d, ‖cubeSlice data j u‖ ∂volume) * Ck := by
    exact (hGrow j).tsum_le_tsum (hG_le_B j) (hBsum j)
      |>.trans ((hBsum j).tsum_le_of_sum_le (hB_finset j))
  have hsliceSum : Summable (fun j : IntVec P.d ↦
      ∫ u : Torus P.d, ‖cubeSlice data j u‖ ∂volume) :=
    by
      rw [hvolume]
      change Summable (fun j : IntVec P.d ↦
        ∫ u : Torus P.d, ‖cubeSlice data j u‖
          ∂(Measure.pi (fun _ : Fin P.d ↦ AddCircle.haarAddCircle)))
      exact (hasSum_cubeSlice_L1_norm data).summable
  have hrowTotal : Summable (fun j : IntVec P.d ↦ ∑' q : Int, G j q) := by
    apply Summable.of_nonneg_of_le
      (fun j ↦ tsum_nonneg (hG_nonneg j)) hGrow_bound
    exact hsliceSum.mul_right Ck
  change Summable (fun a : IntVec P.d × Int ↦ G a.1 a.2)
  exact (summable_prod_of_nonneg (fun a ↦ hG_nonneg a.1 a.2)).2
    ⟨hGrow, hrowTotal⟩

private theorem integrable_intEvalSummandHD_term (P : Params)
    {S : Set (RealVec P.d)} {f : RealVec P.d → Complex}
    (data : PositiveInputDataHD P.alpha P.beta S f) (k : Int)
    (a : IntVec P.d × Int) :
    Integrable (fun x : Torus P.d ↦ intEvalSummandHD data k x a) volume := by
  classical
  obtain ⟨Ck, hCk, hsinc⟩ := sincShiftCoeff_uniform_l1 k
  have hsinc_all (t : Real) :
      Summable (fun q : Int ↦ ‖sincShiftCoeffHD k t q‖) ∧
        (∑' q : Int, ‖sincShiftCoeffHD k t q‖) ≤ Ck := by
    by_cases ht : ∀ r : Int, t ≠ (r : Real)
    · exact hsinc t ht
    · have ht' : ∃ r : Int, t = (r : Real) := by
        simpa only [not_forall, not_ne_iff] using ht
      obtain ⟨r, rfl⟩ := ht'
      have hzero (q : Int) : sincShiftCoeffHD k (r : Real) q = 0 := by
        unfold sincShiftCoeffHD Theorem12.Generic.sincShiftCoeff
        rw [mul_comm Real.pi (r : Real), Real.sin_int_mul_pi]
        simp
      constructor
      · simp [hzero]
      · simp [hzero, hCk]
  have hcoeff (t : Real) (q : Int) :
      ‖sincShiftCoeffHD k t q‖ ≤ Ck := by
    have h := hsinc_all t
    calc
      ‖sincShiftCoeffHD k t q‖ ≤
          ∑' r : Int, ‖sincShiftCoeffHD k t r‖ := by
        simpa using h.1.sum_le_tsum {q} (fun r _ ↦ norm_nonneg _)
      _ ≤ Ck := h.2
  have hvolume : (volume : Measure (Torus P.d)) =
      Measure.pi (fun _ : Fin P.d ↦ AddCircle.haarAddCircle) := by
    rw [volume_pi]
    congr 1
    funext i
    simpa using AddCircle.volume_eq_smul_haarAddCircle (T := (1 : Real))
  have hslice : Integrable (cubeSlice data a.1) volume := by
    rw [hvolume]
    change Integrable (cubeSlice data a.1)
      (Measure.pi (fun _ : Fin P.d ↦ AddCircle.haarAddCircle))
    exact integrable_cubeSlice data a.1
  let shift : Torus P.d :=
    ellIndexHD P.beta a.1 a.2 • alphaTorusHD P.alpha
  have hupper : Integrable (fun x : Torus P.d ↦
      ‖cubeSlice data a.1 (uCoordHD P.alpha P.beta x a.1 a.2)‖ * Ck)
      volume := by
    change Integrable (fun x : Torus P.d ↦
      ‖cubeSlice data a.1 (x - shift)‖ * Ck) volume
    exact (hslice.norm.comp_sub_right shift).mul_const Ck
  refine hupper.mono'
    (aemeasurable_intEvalSummandHD P data k a).aestronglyMeasurable ?_
  filter_upwards with x
  by_cases hx : x ∈ sineBadHD P.alpha P.beta
  · simp only [intEvalSummandHD, hx, if_pos, norm_zero]
    exact mul_nonneg (norm_nonneg _) hCk
  · simp only [intEvalSummandHD, hx, if_false, norm_mul]
    rw [show ‖intParityHD (floorBetaDot P.beta a.1)‖ = 1 by
      simp [intParityHD], one_mul]
    exact mul_le_mul_of_nonneg_left
      (hcoeff (reducedPhaseHD P.alpha P.beta x a.1 a.2) a.2)
      (norm_nonneg _)

/- Proof idea: combine AE measurability with norm-summability of the Bochner series. -/
theorem integrable_intEvaluatorHD (P : Params) {S : Set (RealVec P.d)}
    {f : RealVec P.d → Complex}
    (data : PositiveInputDataHD P.alpha P.beta S f) (k : Int) :
    Integrable (intEvaluatorHD data k) volume := by
  classical
  have htermInt (a : IntVec P.d × Int) :=
    integrable_intEvalSummandHD_term P data k a
  have hsum := summable_integral_norm_intEvalSummandHD P data k
  have hmeas (a : IntVec P.d × Int) :
      AEMeasurable (fun x : Torus P.d ↦ intEvalSummandHD data k x a) volume :=
    aemeasurable_intEvalSummandHD P data k a
  have hlin_ne :
      (∑' a : IntVec P.d × Int, ∫⁻ x : Torus P.d,
        ‖intEvalSummandHD data k x a‖ₑ ∂volume) ≠ ∞ := by
    have hlin (a : IntVec P.d × Int) :
        (∫⁻ x : Torus P.d, ‖intEvalSummandHD data k x a‖ₑ ∂volume) =
          ENNReal.ofReal
            (∫ x : Torus P.d, ‖intEvalSummandHD data k x a‖ ∂volume) := by
      exact (ofReal_integral_norm_eq_lintegral_enorm (htermInt a)).symm
    rw [funext hlin]
    exact hsum.tsum_ofReal_ne_top
  refine ⟨(AEMeasurable.tsum hmeas).aestronglyMeasurable, ?_⟩
  change (∫⁻ x : Torus P.d,
    ‖∑' a : IntVec P.d × Int, intEvalSummandHD data k x a‖ₑ ∂volume) < ∞
  calc
    (∫⁻ x : Torus P.d,
      ‖∑' a : IntVec P.d × Int, intEvalSummandHD data k x a‖ₑ ∂volume) ≤
        ∫⁻ x : Torus P.d,
          ∑' a : IntVec P.d × Int, ‖intEvalSummandHD data k x a‖ₑ ∂volume :=
      lintegral_mono fun x ↦ enorm_tsum_le_tsum_enorm
    _ = ∑' a : IntVec P.d × Int, ∫⁻ x : Torus P.d,
          ‖intEvalSummandHD data k x a‖ₑ ∂volume := by
      rw [lintegral_tsum fun a ↦ (hmeas a).enorm]
    _ < ∞ := lt_top_iff_ne_top.mpr hlin_ne

/- Proof idea: multiply the absolutely summable evaluator series by the norm-one native
character and apply the Bochner integral/tsum interchange. -/
theorem integral_intEvaluator_mul_mFourier_eq_tsum (P : Params)
    {S : Set (RealVec P.d)} {f : RealVec P.d → Complex}
    (data : PositiveInputDataHD P.alpha P.beta S f) (k : Int) (n : IntVec P.d) :
    (∫ x : Torus P.d,
        intEvaluatorHD data k x * UnitAddTorus.mFourier n x ∂volume) =
      ∑' a : IntVec P.d × Int,
        ∫ x : Torus P.d,
          intEvalSummandHD data k x a * UnitAddTorus.mFourier n x ∂volume := by
  classical
  have htermInt (a : IntVec P.d × Int) :=
    integrable_intEvalSummandHD_term P data k a
  have hproductInt (a : IntVec P.d × Int) : Integrable
      (fun x : Torus P.d ↦
        intEvalSummandHD data k x a * UnitAddTorus.mFourier n x) volume := by
    apply (htermInt a).mul_bdd (c := 1)
    · exact (UnitAddTorus.mFourier n).continuous.aestronglyMeasurable
    · filter_upwards with x
      simp [UnitAddTorus.mFourier, fourier_apply]
  have hproductSum : Summable (fun a : IntVec P.d × Int ↦
      ∫ x : Torus P.d,
        ‖intEvalSummandHD data k x a * UnitAddTorus.mFourier n x‖ ∂volume) := by
    simpa only [norm_mul, UnitAddTorus.mFourier, ContinuousMap.coe_mk,
      norm_prod, fourier_apply, Circle.norm_coe, Finset.prod_const_one,
      mul_one] using summable_integral_norm_intEvalSummandHD P data k
  have hinterchange :=
    integral_tsum_of_summable_integral_norm hproductInt hproductSum
  change (∫ x : Torus P.d,
      (∑' a : IntVec P.d × Int, intEvalSummandHD data k x a) *
        UnitAddTorus.mFourier n x ∂volume) = _
  simp_rw [← tsum_mul_right]
  exact hinterchange.symm

/- Proof idea: intersect the countable translated complements of `sineBadHD`, then derive
all translated-phase nonintegrality statements on the same conull set. -/
private theorem rowGoodHD_ae (P : Params) (j : IntVec P.d) :
    ∀ᵐ u : Torus P.d ∂volume,
      rowGoodHD P j u ∧
        ∀ r : Int, translatedPhaseHD P.beta j u ≠ (r : Real) := by
  let mu : Measure (Torus P.d) := volume
  change ∀ᵐ u : Torus P.d ∂mu,
    rowGoodHD P j u ∧
      ∀ r : Int, translatedPhaseHD P.beta j u ≠ (r : Real)
  letI : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
  let nu : Measure (Torus P.d) := volume
  have hmunu : mu = nu := by
    dsimp [mu, nu]
    change Measure.pi
        (fun _ : Fin P.d ↦ @volume UnitAddCircle (AddCircle.measureSpace 1)) =
      Measure.pi (fun _ : Fin P.d ↦ AddCircle.haarAddCircle)
    congr 1
    funext i
    change ENNReal.ofReal 1 • Measure.addHaarMeasure ⊤ =
      Measure.addHaarMeasure ⊤
    simp
  have hnullNu : nu (sineBadHD P.alpha P.beta) = 0 := by
    rw [← hmunu]
    exact sineBadHD_null P
  have hallNu : ∀ᵐ u : Torus P.d ∂nu, rowGoodHD P j u := by
    apply ae_all_iff.mpr
    intro q
    let shift : Torus P.d :=
      ellIndexHD P.beta j q • alphaTorusHD P.alpha
    have hpre : nu
        ((fun u : Torus P.d ↦ u + shift) ⁻¹'
          sineBadHD P.alpha P.beta) = 0 := by
      rw [(measurePreserving_torus_add shift).measure_preimage
        (NullMeasurableSet.of_null hnullNu), hnullNu]
    exact measure_eq_zero_iff_ae_notMem.mp hpre
  have hall : ∀ᵐ u : Torus P.d ∂mu, rowGoodHD P j u := by
    rw [hmunu]
    exact hallNu
  filter_upwards [hall] with u hu
  refine ⟨hu, ?_⟩
  intro r hr
  apply hu 0
  refine ⟨j, ellIndexHD P.beta j 0, -r, ?_⟩
  have hucoord := uCoordHD_add_ellIndex_smul
    P.alpha P.beta u j 0
  change (ellIndexHD P.beta j 0 : Real) -
      rawPhaseHD P.beta j
        (uOrbitHD P.alpha
          (u + ellIndexHD P.beta j 0 • alphaTorusHD P.alpha)
          (ellIndexHD P.beta j 0)) = (-r : Int)
  change uOrbitHD P.alpha
      (u + ellIndexHD P.beta j 0 • alphaTorusHD P.alpha)
      (ellIndexHD P.beta j 0) = u at hucoord
  rw [hucoord]
  unfold translatedPhaseHD at hr
  unfold ellIndexHD rawPhaseHD
  push_cast
  linarith

/- Proof idea: use the row-good guard, reduce the translated orbit coordinate to `u`, and
normalize the floor, parity, phase, and multitorus character factors. -/
private theorem translatedRowSummandHD_eq_ae (P : Params)
    {S : Set (RealVec P.d)} {f : RealVec P.d → Complex}
    (data : PositiveInputDataHD P.alpha P.beta S f) (k : Int) (n j : IntVec P.d) :
    ∀ᵐ u : Torus P.d ∂volume, ∀ q : Int,
      translatedRowSummandHD data k n j q u =
        rowSincSummandHD data k n j u q := by
  filter_upwards [rowGoodHD_ae P j] with u hu
  intro q
  have hphase : reducedPhaseHD P.alpha P.beta
      (u + ellIndexHD P.beta j q • alphaTorusHD P.alpha) j q =
      translatedPhaseHD P.beta j u := by
    have hraw := rawPhaseHD_eq_floor_add_reducedPhaseHD
      P.alpha P.beta
        (u + ellIndexHD P.beta j q • alphaTorusHD P.alpha) j q
    rw [uCoordHD_add_ellIndex_smul] at hraw
    unfold translatedPhaseHD rawPhaseHD at *
    linarith
  unfold translatedRowSummandHD rowSincSummandHD intEvalSummandHD
  rw [if_neg (hu.1 q), uCoordHD_add_ellIndex_smul, hphase]
  rfl

private theorem mFourier_zsmul_alphaTorusHD {d : Nat}
    (alpha : RealVec d) (n : IntVec d) (q : Int) :
    UnitAddTorus.mFourier n (q • alphaTorusHD alpha) =
      fourier q (rotationPointHD alpha n) := by
  simp only [UnitAddTorus.mFourier, alphaTorusHD, rotationPointHD,
    ContinuousMap.coe_mk, Pi.smul_apply, ← QuotientAddGroup.mk_zsmul,
    fourier_coe_apply, ← Complex.exp_sum, dotIntReal, Complex.ofReal_sum,
    Complex.ofReal_mul, Complex.ofReal_intCast]
  congr 1
  push_cast
  rw [Finset.mul_sum]
  simp only [div_one, zsmul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/- Proof idea: factor the q-independent terms, rewrite the q-character as the scalar
`AddCircle.fourier`, and apply the centered/reindexed noninteger sinc `HasSum` theorem. -/
private theorem hasSum_rowSincSummandHD (P : Params) {S : Set (RealVec P.d)}
    {f : RealVec P.d → Complex}
    (data : PositiveInputDataHD P.alpha P.beta S f) (k : Int) (n j : IntVec P.d)
    (u : Torus P.d) (hu : rowGoodHD P j u)
    (ht : ∀ r : Int, translatedPhaseHD P.beta j u ≠ (r : Real)) :
    HasSum (fun q : Int => rowSincSummandHD data k n j u q)
      (collapsedRowIntegrandHD data k n j u) := by
  let m : Int := floorBetaDot P.beta j
  let t : Real := translatedPhaseHD P.beta j u
  let y : AddCircle (1 : Real) := rotationPointHD P.alpha n
  have htranslate (q : Int) :
      UnitAddTorus.mFourier n
          (u + (m + q) • alphaTorusHD P.alpha) =
        UnitAddTorus.mFourier n
            (u + m • alphaTorusHD P.alpha) * fourier q y := by
    calc
      UnitAddTorus.mFourier n
          (u + (m + q) • alphaTorusHD P.alpha) =
          UnitAddTorus.mFourier n
            ((u + m • alphaTorusHD P.alpha) +
              q • alphaTorusHD P.alpha) := by
            rw [add_smul]
            congr 1
            abel
      _ = UnitAddTorus.mFourier n
            (u + m • alphaTorusHD P.alpha) *
          UnitAddTorus.mFourier n (q • alphaTorusHD P.alpha) := by
            simp only [UnitAddTorus.mFourier, Pi.add_apply,
              ContinuousMap.coe_mk, ← Finset.prod_mul_distrib]
            apply Finset.prod_congr rfl
            intro i hi
            simp only [fourier_apply, smul_add, AddCircle.toCircle_add,
              Circle.coe_mul]
      _ = UnitAddTorus.mFourier n
            (u + m • alphaTorusHD P.alpha) * fourier q y := by
            rw [mFourier_zsmul_alphaTorusHD]
  have hbase := sinc_shift_identity_arbitrary k t (by simpa [t] using ht) y
  let common : Complex := intParityHD m * cubeSlice data j u *
    UnitAddTorus.mFourier n (u + m • alphaTorusHD P.alpha)
  have hmul := hbase.mul_left common
  have hterm (q : Int) :
      rowSincSummandHD data k n j u q =
        common * (sincShiftCoeffHD k t q * fourier q y) := by
    simp only [rowSincSummandHD]
    rw [htranslate]
    dsimp only [common, m, t, y]
    ring
  have hlimit :
      collapsedRowIntegrandHD data k n j u =
        common * shiftedCenteredExpHD k t y := by
    simp only [collapsedRowIntegrandHD]
    dsimp only [common, m, t, y]
  rw [hlimit]
  exact hmul.congr_fun hterm

/- Proof idea: use Haar invariance under translation by the exact signed
`ellIndexHD beta j q • alphaTorusHD alpha`. -/
private theorem integral_intEvalSummandHD_eq_translatedRowSummandHD
    (P : Params) {S : Set (RealVec P.d)} {f : RealVec P.d → Complex}
    (data : PositiveInputDataHD P.alpha P.beta S f) (k : Int) (n j : IntVec P.d)
    (q : Int) :
    (∫ x : Torus P.d,
        intEvalSummandHD data k x (j, q) * UnitAddTorus.mFourier n x ∂volume) =
      ∫ u : Torus P.d, translatedRowSummandHD data k n j q u ∂volume := by
  let shift : Torus P.d :=
    ellIndexHD P.beta j q • alphaTorusHD P.alpha
  let integrand : Torus P.d → Complex := fun x ↦
    intEvalSummandHD data k x (j, q) * UnitAddTorus.mFourier n x
  let mu : Measure (Torus P.d) := volume
  change (∫ x : Torus P.d, integrand x ∂mu) = _
  have htranslate := (measurePreserving_add_right mu shift).integral_comp
    (Homeomorph.addRight shift).isClosedEmbedding.measurableEmbedding integrand
  symm
  simpa only [translatedRowSummandHD, shift, integrand] using htranslate

/- Proof idea: translate term integrals, use the one AE/all-q row equality, apply the
pointwise sinc `HasSum`, and justify `integral_tsum` with the inherited norm certificate. -/
private theorem sum_q_integral_intEvalSummandHD (P : Params)
    {S : Set (RealVec P.d)} {f : RealVec P.d → Complex}
    (data : PositiveInputDataHD P.alpha P.beta S f) (k : Int) (n j : IntVec P.d) :
    (∑' q : Int,
        ∫ x : Torus P.d,
          intEvalSummandHD data k x (j, q) * UnitAddTorus.mFourier n x ∂volume) =
      ∫ u : Torus P.d, collapsedRowIntegrandHD data k n j u ∂volume := by
  have hproductInt (q : Int) : Integrable (fun x : Torus P.d ↦
      intEvalSummandHD data k x (j, q) * UnitAddTorus.mFourier n x) volume := by
    apply (integrable_intEvalSummandHD_term P data k (j, q)).mul_bdd (c := 1)
    · exact (UnitAddTorus.mFourier n).continuous.aestronglyMeasurable
    · filter_upwards with x
      simp [UnitAddTorus.mFourier, fourier_apply]
  have htranslatedInt (q : Int) : Integrable (fun u : Torus P.d ↦
      translatedRowSummandHD data k n j q u) volume := by
    let shift : Torus P.d :=
      ellIndexHD P.beta j q • alphaTorusHD P.alpha
    simpa only [translatedRowSummandHD, shift] using
      (hproductInt q).comp_add_right shift
  have hnormEq (q : Int) :
      (∫ u : Torus P.d, ‖translatedRowSummandHD data k n j q u‖ ∂volume) =
        ∫ x : Torus P.d, ‖intEvalSummandHD data k x (j, q)‖ ∂volume := by
    let shift : Torus P.d :=
      ellIndexHD P.beta j q • alphaTorusHD P.alpha
    let g : Torus P.d → Real := fun x ↦
      ‖intEvalSummandHD data k x (j, q) * UnitAddTorus.mFourier n x‖
    let mu : Measure (Torus P.d) := volume
    have htranslate := (measurePreserving_add_right mu shift).integral_comp
      (Homeomorph.addRight shift).isClosedEmbedding.measurableEmbedding g
    simpa only [translatedRowSummandHD, shift, g, norm_mul,
      UnitAddTorus.mFourier, ContinuousMap.coe_mk, norm_prod, fourier_apply,
      Circle.norm_coe, Finset.prod_const_one, mul_one] using htranslate
  have hsumNorm : Summable (fun q : Int ↦
      ∫ u : Torus P.d, ‖translatedRowSummandHD data k n j q u‖ ∂volume) := by
    simpa only [hnormEq] using
      (summable_integral_norm_intEvalSummandHD P data k).prod_factor j
  have hinterchange :=
    integral_tsum_of_summable_integral_norm htranslatedInt hsumNorm
  calc
    (∑' q : Int, ∫ x : Torus P.d,
        intEvalSummandHD data k x (j, q) * UnitAddTorus.mFourier n x ∂volume) =
        ∑' q : Int, ∫ u : Torus P.d,
          translatedRowSummandHD data k n j q u ∂volume := by
      apply tsum_congr
      intro q
      exact integral_intEvalSummandHD_eq_translatedRowSummandHD P data k n j q
    _ = ∫ u : Torus P.d,
        ∑' q : Int, translatedRowSummandHD data k n j q u ∂volume :=
      hinterchange
    _ = ∫ u : Torus P.d, collapsedRowIntegrandHD data k n j u ∂volume := by
      apply integral_congr_ae
      filter_upwards [translatedRowSummandHD_eq_ae P data k n j,
        rowGoodHD_ae P j] with u htranslate hgood
      rw [tsum_congr htranslate]
      exact (hasSum_rowSincSummandHD P data k n j u hgood.1 hgood.2).tsum_eq

/- Proof idea: expand the finite dot products, cancel the integer layer phase, substitute
`orbitThetaHD = fract - 1/2`, and normalize the complex exponential products. -/
private theorem collapsedRow_phase_identityHD {d : Nat}
    (alpha beta : RealVec d) (j n : IntVec d) (k : Int) (u : Torus d) :
    let m : Int := floorBetaDot beta j
    let t : Real := translatedPhaseHD beta j u
    let y := rotationPointHD alpha n
    intParityHD m *
        UnitAddTorus.mFourier n (u + m • alphaTorusHD alpha) *
        shiftedCenteredExpHD k t y =
      (Complex.exp
          (((2 * Real.pi : Real) : Complex) * Complex.I *
            (k : Complex) * (dotIntReal n alpha : Complex)) - 1) *
        UnitAddTorus.mFourier n u *
        fourierCharHD (modulatedDeltaHD alpha beta n)
          (torusToCubeHD u + intCast j) := by
  simp only
  let m : Int := floorBetaDot beta j
  let t : Real := translatedPhaseHD beta j u
  let y : AddCircle (1 : Real) := rotationPointHD alpha n
  let D : Real := dotIntReal n alpha
  let z : Real := Int.fract D
  let A : Complex := ((2 * Real.pi : Real) : Complex) * Complex.I
  let X : RealVec d := torusToCubeHD u + intCast j
  have hyrep : Theorem12.Generic.unitRep y = z := by
    dsimp [y, rotationPointHD, z, D]
    exact Theorem12.Generic.unitRep_coe_eq_fract _
  have hshift :
      UnitAddTorus.mFourier n (u + m • alphaTorusHD alpha) =
        UnitAddTorus.mFourier n u * fourier m y := by
    calc
      UnitAddTorus.mFourier n (u + m • alphaTorusHD alpha) =
          UnitAddTorus.mFourier n u *
            UnitAddTorus.mFourier n (m • alphaTorusHD alpha) := by
        simp only [UnitAddTorus.mFourier, Pi.add_apply,
          ContinuousMap.coe_mk, ← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro i hi
        simp only [fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]
      _ = UnitAddTorus.mFourier n u * fourier m y := by
        rw [mFourier_zsmul_alphaTorusHD]
  have hfourierY : fourier m y =
      Complex.exp (A * (m : Complex) * (z : Complex)) := by
    calc
      fourier m y = fourier m
          ((Theorem12.Generic.unitRep y : Real) : AddCircle (1 : Real)) := by
        rw [Theorem12.Generic.coe_unitRep]
      _ = Complex.exp (A * (m : Complex) *
          (Theorem12.Generic.unitRep y : Complex)) := by
        rw [fourier_coe_apply]
        dsimp [A]
        push_cast
        congr 1
        ring
      _ = Complex.exp (A * (m : Complex) * (z : Complex)) := by
        rw [hyrep]
  have hD : (Int.floor D : Real) + z = D := by
    exact Int.floor_add_fract D
  have hkarg :
      A * (k : Complex) * (D : Complex) =
        ((k * Int.floor D : Int) : Complex) *
            (2 * (Real.pi : Complex) * Complex.I) +
          A * (k : Complex) * (z : Complex) := by
    have hDC : (((Int.floor D : Real) : Complex) + (z : Complex)) =
        (D : Complex) := by
      exact_mod_cast hD
    conv_lhs => rw [← hDC]
    dsimp [A]
    push_cast
    ring
  have hk : Complex.exp (A * (k : Complex) * (D : Complex)) =
      Complex.exp (A * (k : Complex) * (z : Complex)) := by
    rw [hkarg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I,
      one_mul]
  have hdot : dotReal (modulatedDeltaHD alpha beta n) X =
      (z - 1 / 2) * dotReal beta X := by
    simp only [modulatedDeltaHD, orbitThetaHD, dotReal]
    change (∑ i, (z - 1 / 2) * beta i * X i) =
      (z - 1 / 2) * ∑ i, beta i * X i
    simp_rw [mul_assoc]
    rw [Finset.mul_sum]
  have harg :
      (m : Complex) * ((Real.pi : Complex) * Complex.I) +
          A * (m : Complex) * (z : Complex) +
          A * (t : Complex) * ((z - 1 / 2 : Real) : Complex) =
        (m : Complex) * (2 * (Real.pi : Complex) * Complex.I) +
          A * (dotReal (modulatedDeltaHD alpha beta n) X : Complex) := by
    rw [hdot]
    dsimp [t, translatedPhaseHD, X, A]
    push_cast
    ring
  have hphase :
      intParityHD m * Complex.exp (A * (m : Complex) * (z : Complex)) *
          Complex.exp (A * (t : Complex) * ((z - 1 / 2 : Real) : Complex)) =
        fourierCharHD (modulatedDeltaHD alpha beta n) X := by
    unfold fourierCharHD
    rw [intParityHD, ← Complex.exp_pi_mul_I, ← Complex.exp_int_mul,
      ← Complex.exp_add, ← Complex.exp_add]
    change Complex.exp
        ((m : Complex) * ((Real.pi : Complex) * Complex.I) +
          A * (m : Complex) * (z : Complex) +
          A * (t : Complex) * ((z - 1 / 2 : Real) : Complex)) = _
    rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I,
      one_mul]
  rw [hshift, hfourierY]
  simp only [shiftedCenteredExpHD, Theorem12.Generic.shiftedCenteredExp,
    Theorem12.Generic.centeredExp]
  rw [hyrep]
  change intParityHD m *
      (UnitAddTorus.mFourier n u *
        Complex.exp (A * (m : Complex) * (z : Complex))) *
      ((Complex.exp (A * (k : Complex) * (z : Complex)) - 1) *
        Complex.exp (A * (t : Complex) * ((z - 1 / 2 : Real) : Complex))) =
    (Complex.exp (A * (k : Complex) * (D : Complex)) - 1) *
      UnitAddTorus.mFourier n u *
        fourierCharHD (modulatedDeltaHD alpha beta n) X
  rw [hk, ← hphase]
  ring

/- Proof idea: dominate each collapsed row by twice the corresponding layer L1 norm. -/
theorem summable_integral_norm_collapsedRowHD (P : Params)
    {S : Set (RealVec P.d)} {f : RealVec P.d → Complex}
    (data : PositiveInputDataHD P.alpha P.beta S f) (k : Int) (n : IntVec P.d) :
    Summable (fun j : IntVec P.d =>
      ∫ u : Torus P.d, ‖collapsedRowIntegrandHD data k n j u‖ ∂volume) := by
  have hvolume : (volume : Measure (Torus P.d)) =
      Measure.pi (fun _ : Fin P.d ↦ AddCircle.haarAddCircle) := by
    rw [volume_pi]
    congr 1
    funext i
    simpa using AddCircle.volume_eq_smul_haarAddCircle (T := (1 : Real))
  have hsliceInt (j : IntVec P.d) : Integrable (cubeSlice data j) volume := by
    rw [hvolume]
    change Integrable (cubeSlice data j)
      (Measure.pi (fun _ : Fin P.d ↦ AddCircle.haarAddCircle))
    exact integrable_cubeSlice data j
  have hsliceSum : Summable (fun j : IntVec P.d ↦
      2 * ∫ u : Torus P.d, ‖cubeSlice data j u‖ ∂volume) := by
    apply Summable.mul_left
    rw [hvolume]
    change Summable (fun j : IntVec P.d ↦
      ∫ u : Torus P.d, ‖cubeSlice data j u‖
        ∂(Measure.pi (fun _ : Fin P.d ↦ AddCircle.haarAddCircle)))
    exact (hasSum_cubeSlice_L1_norm data).summable
  refine Summable.of_nonneg_of_le
    (fun j ↦ integral_nonneg fun u ↦ norm_nonneg _) ?_ hsliceSum
  intro j
  have hpoint (u : Torus P.d) :
      ‖collapsedRowIntegrandHD data k n j u‖ ≤
        2 * ‖cubeSlice data j u‖ := by
    have hshift : ‖shiftedCenteredExpHD k
        (translatedPhaseHD P.beta j u) (rotationPointHD P.alpha n)‖ ≤ 2 := by
      unfold shiftedCenteredExpHD Theorem12.Generic.shiftedCenteredExp
        Theorem12.Generic.centeredExp
      rw [norm_mul]
      have hdiff : ‖Complex.exp
          (((2 * Real.pi : Real) : Complex) * Complex.I * (k : Complex) *
            (Theorem12.Generic.unitRep (rotationPointHD P.alpha n) : Complex)) - 1‖ ≤ 2 := by
        calc
          _ ≤ ‖Complex.exp
              (((2 * Real.pi : Real) : Complex) * Complex.I * (k : Complex) *
                (Theorem12.Generic.unitRep (rotationPointHD P.alpha n) : Complex))‖ +
                ‖(1 : Complex)‖ := norm_sub_le _ _
          _ = 2 := by rw [Complex.norm_exp]; norm_num
      have hcenter : ‖Complex.exp
          (((2 * Real.pi : Real) : Complex) * Complex.I *
            (translatedPhaseHD P.beta j u : Complex) *
              ((Theorem12.Generic.unitRep (rotationPointHD P.alpha n) - 1 / 2 : Real) :
                Complex))‖ = 1 := by
        rw [Complex.norm_exp]
        norm_num
      rw [hcenter, mul_one]
      exact hdiff
    unfold collapsedRowIntegrandHD
    simp only [norm_mul, intParityHD, norm_zpow, norm_neg, norm_one,
      one_zpow, one_mul, UnitAddTorus.mFourier, ContinuousMap.coe_mk,
      norm_prod, fourier_apply, Circle.norm_coe, Finset.prod_const_one]
    simpa [mul_assoc, mul_comm] using
      mul_le_mul_of_nonneg_left hshift (norm_nonneg (cubeSlice data j u))
  have hupper : Integrable (fun u : Torus P.d ↦
      2 * ‖cubeSlice data j u‖) volume :=
    (hsliceInt j).norm.const_mul 2
  calc
    (∫ u : Torus P.d, ‖collapsedRowIntegrandHD data k n j u‖ ∂volume) ≤
        ∫ u : Torus P.d, 2 * ‖cubeSlice data j u‖ ∂volume :=
      integral_mono_of_nonneg (ae_of_all _ fun u ↦ norm_nonneg _)
        hupper (ae_of_all _ hpoint)
    _ = 2 * ∫ u : Torus P.d, ‖cubeSlice data j u‖ ∂volume :=
      integral_const_mul 2 _

/- Proof idea: reassociate the product-index `tsum`, replace every q-row by
`sum_q_integral_intEvalSummandHD`, then recombine only after the outer norm-summability theorem. -/
theorem integral_intEvaluator_mul_character_eq_collapsedRowsHD (P : Params)
    {S : Set (RealVec P.d)} {f : RealVec P.d → Complex}
    (data : PositiveInputDataHD P.alpha P.beta S f) (k : Int) (n : IntVec P.d) :
    (∫ x : Torus P.d,
        intEvaluatorHD data k x * UnitAddTorus.mFourier n x ∂volume) =
      ∑' j : IntVec P.d,
        ∫ u : Torus P.d, collapsedRowIntegrandHD data k n j u ∂volume := by
  have hproductSum : Summable (fun a : IntVec P.d × Int ↦
      ∫ x : Torus P.d,
        ‖intEvalSummandHD data k x a * UnitAddTorus.mFourier n x‖ ∂volume) := by
    simpa only [norm_mul, UnitAddTorus.mFourier, ContinuousMap.coe_mk,
      norm_prod, fourier_apply, Circle.norm_coe, Finset.prod_const_one,
      mul_one] using summable_integral_norm_intEvalSummandHD P data k
  have hcomplexSum : Summable (fun a : IntVec P.d × Int ↦
      ∫ x : Torus P.d,
        intEvalSummandHD data k x a * UnitAddTorus.mFourier n x ∂volume) := by
    apply hproductSum.of_norm_bounded
    intro a
    exact norm_integral_le_integral_norm _
  calc
    (∫ x : Torus P.d,
        intEvaluatorHD data k x * UnitAddTorus.mFourier n x ∂volume) =
        ∑' a : IntVec P.d × Int,
          ∫ x : Torus P.d,
            intEvalSummandHD data k x a * UnitAddTorus.mFourier n x ∂volume :=
      integral_intEvaluator_mul_mFourier_eq_tsum P data k n
    _ = ∑' j : IntVec P.d, ∑' q : Int,
          ∫ x : Torus P.d,
            intEvalSummandHD data k x (j, q) *
              UnitAddTorus.mFourier n x ∂volume := hcomplexSum.tsum_prod
    _ = ∑' j : IntVec P.d,
          ∫ u : Torus P.d, collapsedRowIntegrandHD data k n j u ∂volume := by
      apply tsum_congr
      intro j
      exact sum_q_integral_intEvalSummandHD P data k n j

/- Proof idea: rewrite each collapsed row by `collapsedRow_phase_identityHD` and identify the resulting
sum of cube-layer integrals with the positive sample. -/
theorem integral_intEvaluator_mul_character_eq_sampleHD (P : Params)
    {S : Set (RealVec P.d)} {f : RealVec P.d → Complex}
    (data : PositiveInputDataHD P.alpha P.beta S f) (k : Int) (n : IntVec P.d) :
    (∫ x : Torus P.d,
        intEvaluatorHD data k x * UnitAddTorus.mFourier n x ∂volume) =
      (Complex.exp
          (((2 * Real.pi : Real) : Complex) * Complex.I * (k : Complex) *
            (dotIntReal n P.alpha : Complex)) - 1) *
        positiveFourierSampleOnHD S data.H0
          (modulatedLambdaHD P.alpha P.beta n) := by
  let C : Complex :=
    Complex.exp
        (((2 * Real.pi : Real) : Complex) * Complex.I * (k : Complex) *
          (dotIntReal n P.alpha : Complex)) - 1
  have hcharacter (u : Torus P.d) :
      UnitAddTorus.mFourier n u =
        fourierCharHD (fun i ↦ (n i : Real)) (torusToCubeHD u) := by
    calc
      UnitAddTorus.mFourier n u =
          UnitAddTorus.mFourier n
            (IntegerFrequenciesHD.Internal.cubeToTorusHD (torusToCubeHD u)) := by
        congr 1
        exact
          (IntegerFrequenciesHD.Internal.cubeToTorusHD_torusToCubeHD u).symm
      _ = fourierCharHD (fun i ↦ (n i : Real)) (torusToCubeHD u) := by
        unfold fourierCharHD dotReal
        simp only [UnitAddTorus.mFourier,
          IntegerFrequenciesHD.Internal.cubeToTorusHD,
          ContinuousMap.coe_mk, fourier_coe_apply]
        rw [← Complex.exp_sum]
        congr 1
        push_cast
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
  have hrow (j : IntVec P.d) (u : Torus P.d) :
      collapsedRowIntegrandHD data k n j u =
        C * sampleLayerIntegrand data n j u := by
    have hphase := collapsedRow_phase_identityHD
      P.alpha P.beta j n k u
    simp only at hphase
    have hdelta :
        dotReal (modulatedDeltaHD P.alpha P.beta n)
            (torusToCubeHD u + intCast j) =
          dotReal P.beta (intVecTranslate j u) * orbitThetaHD P.alpha n := by
      unfold modulatedDeltaHD intVecTranslate dotReal
      change
        (∑ i, orbitThetaHD P.alpha n * P.beta i *
            (torusToCubeHD u i + intCast j i)) =
          (∑ i, P.beta i * (intCast j i + torusToCubeHD u i)) *
            orbitThetaHD P.alpha n
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    have hlayerPhase :
        UnitAddTorus.mFourier n u *
            fourierCharHD (modulatedDeltaHD P.alpha P.beta n)
              (torusToCubeHD u + intCast j) =
          Complex.exp ((((2 * Real.pi : Real) : Complex) * Complex.I) *
              ((dotReal P.beta (intVecTranslate j u) *
                orbitThetaHD P.alpha n : Real) : Complex)) *
            fourierCharHD (fun i ↦ (n i : Real)) (torusToCubeHD u) := by
      rw [hcharacter]
      unfold fourierCharHD
      rw [hdelta]
      ring
    simp only [collapsedRowIntegrandHD, sampleLayerIntegrand]
    calc
      intParityHD (floorBetaDot P.beta j) * cubeSlice data j u *
            UnitAddTorus.mFourier n
              (u + floorBetaDot P.beta j • alphaTorusHD P.alpha) *
            shiftedCenteredExpHD k (translatedPhaseHD P.beta j u)
              (rotationPointHD P.alpha n) =
          cubeSlice data j u *
            (intParityHD (floorBetaDot P.beta j) *
              UnitAddTorus.mFourier n
                (u + floorBetaDot P.beta j • alphaTorusHD P.alpha) *
              shiftedCenteredExpHD k (translatedPhaseHD P.beta j u)
                (rotationPointHD P.alpha n)) := by ring
      _ = cubeSlice data j u *
            (C * UnitAddTorus.mFourier n u *
              fourierCharHD (modulatedDeltaHD P.alpha P.beta n)
                (torusToCubeHD u + intCast j)) := by
          rw [hphase]
      _ = C * (cubeSlice data j u *
            (UnitAddTorus.mFourier n u *
              fourierCharHD (modulatedDeltaHD P.alpha P.beta n)
                (torusToCubeHD u + intCast j))) := by ring
      _ = C * (cubeSlice data j u *
            (Complex.exp ((((2 * Real.pi : Real) : Complex) * Complex.I) *
                ((dotReal P.beta (intVecTranslate j u) *
                  orbitThetaHD P.alpha n : Real) : Complex)) *
              fourierCharHD (fun i ↦ (n i : Real)) (torusToCubeHD u))) := by
          rw [hlayerPhase]
      _ = C * (cubeSlice data j u *
            Complex.exp ((((2 * Real.pi : Real) : Complex) * Complex.I) *
              ((dotReal P.beta (intVecTranslate j u) *
                orbitThetaHD P.alpha n : Real) : Complex)) *
            fourierCharHD (fun i ↦ (n i : Real)) (torusToCubeHD u)) := by
          ring
  have hintegral (j : IntVec P.d) :
      (∫ u : Torus P.d, collapsedRowIntegrandHD data k n j u ∂volume) =
        C * ∫ u : Torus P.d, sampleLayerIntegrand data n j u ∂volume := by
    rw [integral_congr_ae (ae_of_all _ (hrow j)), integral_const_mul]
  have hcarrier :
      positiveFourierSampleOnHD S data.H0
          (modulatedLambdaHD P.alpha P.beta n) =
        positiveFourierSampleOnHD Set.univ data.H0
          (modulatedLambdaHD P.alpha P.beta n) := by
    unfold positiveFourierSampleOnHD
    rw [Measure.restrict_univ]
    exact setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      rw [data.zero_off x hx, zero_mul]
  have hvolume : (volume : Measure (Torus P.d)) =
      Measure.pi (fun _ : Fin P.d ↦ AddCircle.haarAddCircle) := by
    rw [volume_pi]
    congr 1
    funext i
    simpa using AddCircle.volume_eq_smul_haarAddCircle (T := (1 : Real))
  rw [integral_intEvaluator_mul_character_eq_collapsedRowsHD]
  calc
    (∑' j : IntVec P.d,
        ∫ u : Torus P.d, collapsedRowIntegrandHD data k n j u ∂volume) =
        ∑' j : IntVec P.d,
          C * ∫ u : Torus P.d, sampleLayerIntegrand data n j u ∂volume :=
      tsum_congr hintegral
    _ = C * ∑' j : IntVec P.d,
          ∫ u : Torus P.d, sampleLayerIntegrand data n j u ∂volume := by
      rw [tsum_mul_left]
    _ = C * ∫ u : Torus P.d, sampleLayerSeries data n u ∂volume := by
      congr 1
      rw [hvolume]
      exact (integral_sampleLayerSeries_eq_tsum data n).symm
    _ = C * positiveFourierSampleOnHD Set.univ data.H0
          (modulatedLambdaHD P.alpha P.beta n) := by
      congr 1
      rw [hvolume]
      exact (positive_sample_eq_cube_sampling_identity data n).symm
    _ = C * positiveFourierSampleOnHD S data.H0
          (modulatedLambdaHD P.alpha P.beta n) := by
      rw [hcarrier]
    _ = _ := rfl

/- Proof idea: rewrite by `integral_intEvaluator_mul_character_eq_sampleHD` and use the positive-sample zero stored in the
single canonical input-data record. -/
theorem integral_intEvaluator_mul_character_eq_zeroHD (P : Params)
    {S : Set (RealVec P.d)} {f : RealVec P.d → Complex}
    (data : PositiveInputDataHD P.alpha P.beta S f) (k : Int) (n : IntVec P.d) :
    (∫ x : Torus P.d,
      intEvaluatorHD data k x * UnitAddTorus.mFourier n x ∂volume) = 0 := by
  have hsample : positiveFourierSampleOnHD S data.H0
      (modulatedLambdaHD P.alpha P.beta n) = 0 := by
    calc
      positiveFourierSampleOnHD S data.H0
          (modulatedLambdaHD P.alpha P.beta n) =
          positiveFourierSampleOnHD Set.univ data.H0
            (modulatedLambdaHD P.alpha P.beta n) := by
        unfold positiveFourierSampleOnHD
        rw [Measure.restrict_univ]
        exact setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
          rw [data.zero_off x hx, zero_mul]
      _ = 0 := data.positiveSamples n
  rw [integral_intEvaluator_mul_character_eq_sampleHD P data k n,
    hsample, mul_zero]

/- Proof idea: unfold the Mathlib coefficient convention and rewrite the conjugate
native character as the character with negative index.  This is the sole sign bridge. -/
theorem mFourierCoeffHD_eq_positivePairing_neg {d : Nat}
    (F : Torus d → Complex) (hF : Integrable F volume) (n : IntVec d) :
    mFourierCoeffHD F n =
      ∫ x : Torus d, F x * UnitAddTorus.mFourier (-n) x ∂volume := by
  let mu : Measure (Torus d) := volume
  change UnitAddTorus.mFourierCoeff F n =
    ∫ x : Torus d, F x * UnitAddTorus.mFourier (-n) x ∂mu
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
  rw [UnitAddTorus.mFourierCoeff]
  change (∫ x : Torus d,
      UnitAddTorus.mFourier (-n) x • F x ∂nu) = _
  rw [← hmunu]
  simp only [smul_eq_mul, mul_comm]

/- Proof idea: apply `integral_intEvaluator_mul_character_eq_zeroHD` at `-n` after the exact coefficient sign bridge. -/
theorem mFourierCoeff_intEvaluatorHD_eq_zero (P : Params)
    {S : Set (RealVec P.d)} {f : RealVec P.d → Complex}
    (data : PositiveInputDataHD P.alpha P.beta S f) (k : Int) (n : IntVec P.d) :
    mFourierCoeffHD (intEvaluatorHD data k) n = 0 := by
  rw [mFourierCoeffHD_eq_positivePairing_neg _
    (integrable_intEvaluatorHD P data k) n]
  exact integral_intEvaluator_mul_character_eq_zeroHD P data k (-n)

/- Proof idea: apply the proved multitorus L1 Fourier-uniqueness theorem to the
integrable evaluator and its zero coefficient family. -/
theorem intEvaluatorHD_ae_eq_zero (P : Params)
    {S : Set (RealVec P.d)} {f : RealVec P.d → Complex}
    (data : PositiveInputDataHD P.alpha P.beta S f) (k : Int) :
    intEvaluatorHD data k =ᵐ[volume] 0 := by
  let mu : Measure (Torus P.d) := volume
  have hInt : Integrable (intEvaluatorHD data k) mu :=
    integrable_intEvaluatorHD P data k
  change intEvaluatorHD data k =ᵐ[mu] (fun _ ↦ 0)
  letI : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
  let nu : Measure (Torus P.d) := volume
  have hmunu : mu = nu := by
    dsimp [mu, nu]
    change Measure.pi
        (fun _ : Fin P.d ↦ @volume UnitAddCircle (AddCircle.measureSpace 1)) =
      Measure.pi (fun _ : Fin P.d ↦ AddCircle.haarAddCircle)
    congr 1
    funext i
    change ENNReal.ofReal 1 • Measure.addHaarMeasure ⊤ =
      Measure.addHaarMeasure ⊤
    simp
  rw [hmunu]
  apply ae_zero_of_mFourierCoeff_zero_L1
  · change Integrable (intEvaluatorHD data k) nu
    rw [← hmunu]
    exact hInt
  · exact mFourierCoeff_intEvaluatorHD_eq_zero P data k

/- Proof idea: take the countable intersection over all signed integer evaluator modes. -/
theorem intEvaluatorHD_all_int_ae (P : Params)
    {S : Set (RealVec P.d)} {f : RealVec P.d → Complex}
    (data : PositiveInputDataHD P.alpha P.beta S f) :
    ∀ᵐ x : Torus P.d ∂volume, ∀ k : Int, intEvaluatorHD data k x = 0 := by
  exact ae_all_iff.mpr fun k ↦ intEvaluatorHD_ae_eq_zero P data k

/- Proof idea: establish full-index absolute summability, use `intEvalSummandHD_eq_sourceKernel` termwise,
and filter zero residues to the active subtype without a conditional rearrangement. -/
theorem intEvaluatorHD_eq_activeMHD_int (P : Params)
    {S : Set (RealVec P.d)} {f : RealVec P.d → Complex}
    (data : PositiveInputDataHD P.alpha P.beta S f) (x : Torus P.d)
    (hx : AnalyticParameterHD data x) (k : Int) :
    intEvaluatorHD data k x = activeMHD data x (k : Complex) := by
  classical
  change (∑' a : IntVec P.d × Int, intEvalSummandHD data k x a) =
    ∑' a : ActiveIndexHD data x, activeTermHD data x a (k : Complex)
  calc
    (∑' a : IntVec P.d × Int, intEvalSummandHD data k x a) =
        ∑' a : IntVec P.d × Int,
          residueCoordHD data P.alpha P.beta x a.1 a.2 *
            regularizedKernelHD
              (poleCoordHD P.alpha P.beta x a.1 a.2) (k : Complex) := by
      apply tsum_congr
      rintro ⟨j, q⟩
      simpa [regularizedKernelHD, one_div] using
        (intEvalSummandHD_eq_sourceKernel P data k x j q hx.offBad)
    _ = ∑' a : ActiveIndexHD data x, activeTermHD data x a (k : Complex) := by
      change (∑' a : IntVec P.d × Int,
          residueCoordHD data P.alpha P.beta x a.1 a.2 *
            regularizedKernelHD
              (poleCoordHD P.alpha P.beta x a.1 a.2) (k : Complex)) =
        ∑' a : {a : IntVec P.d × Int //
            residueCoordHD data P.alpha P.beta x a.1 a.2 ≠ 0},
          residueCoordHD data P.alpha P.beta x a.1.1 a.1.2 *
            regularizedKernelHD
              (poleCoordHD P.alpha P.beta x a.1.1 a.1.2) (k : Complex)
      symm
      calc
        (∑' a : {a : IntVec P.d × Int //
              residueCoordHD data P.alpha P.beta x a.1 a.2 ≠ 0},
            residueCoordHD data P.alpha P.beta x a.1.1 a.1.2 *
              regularizedKernelHD
                (poleCoordHD P.alpha P.beta x a.1.1 a.1.2) (k : Complex)) =
            ∑' a : IntVec P.d × Int,
              {a : IntVec P.d × Int |
                  residueCoordHD data P.alpha P.beta x a.1 a.2 ≠ 0}.indicator
                (fun b : IntVec P.d × Int =>
                  residueCoordHD data P.alpha P.beta x b.1 b.2 *
                    regularizedKernelHD
                      (poleCoordHD P.alpha P.beta x b.1 b.2) (k : Complex)) a :=
          tsum_subtype
            {a : IntVec P.d × Int |
              residueCoordHD data P.alpha P.beta x a.1 a.2 ≠ 0}
            (fun a : IntVec P.d × Int =>
              residueCoordHD data P.alpha P.beta x a.1 a.2 *
                regularizedKernelHD
                  (poleCoordHD P.alpha P.beta x a.1 a.2) (k : Complex))
        _ = ∑' a : IntVec P.d × Int,
            residueCoordHD data P.alpha P.beta x a.1 a.2 *
              regularizedKernelHD
                (poleCoordHD P.alpha P.beta x a.1 a.2) (k : Complex) := by
          apply tsum_congr
          intro a
          by_cases ha : residueCoordHD data P.alpha P.beta x a.1 a.2 ≠ 0
          · have hamem : a ∈
                {b : IntVec P.d × Int |
                  residueCoordHD data P.alpha P.beta x b.1 b.2 ≠ 0} := ha
            simp only [Set.indicator_of_mem hamem]
          · have hanmem : a ∉
                {b : IntVec P.d × Int |
                  residueCoordHD data P.alpha P.beta x b.1 b.2 ≠ 0} := ha
            have hz : residueCoordHD data P.alpha P.beta x a.1 a.2 = 0 :=
              not_ne_iff.mp ha
            simp only [Set.indicator_of_notMem hanmem, hz, zero_mul]

/- Proof idea: intersect the off-bad, finite-weight, pole-injective, and all-integer-zero
conull properties and construct the one common Fourier-good record. -/
theorem fourierGoodParameterHD_ae (P : Params)
    {S : Set (RealVec P.d)} {f : RealVec P.d → Complex}
    (data : PositiveInputDataHD P.alpha P.beta S f) (hSlt : volume S < 1) :
    ∀ᵐ x : Torus P.d ∂volume, FourierGoodParameterHD data x := by
  have hoff : ∀ᵐ x : Torus P.d ∂volume,
      x ∉ sineBadHD P.alpha P.beta :=
    measure_eq_zero_iff_ae_notMem.mp (sineBadHD_null P)
  have hSlt' : volume S < ENNReal.ofReal 1 := by simpa using hSlt
  obtain ⟨_, hSupportFinite⟩ := supportMassENNHD_lt_one data hSlt'
  have hfinite := poleWeight_tsum_lt_top_aeHD data P.alpha P.beta hSupportFinite
  filter_upwards [hoff, hfinite, intEvaluatorHD_all_int_ae P data]
    with x hxBad hxFinite hxZero
  exact ⟨⟨hxBad, poleCoordHD_injective P x, hxFinite⟩, hxZero⟩

/- Proof idea: rewrite the active series at the integer using `intEvaluatorHD_eq_activeMHD_int` and apply the
stored evaluator equality from the same Fourier-good parameter. -/
theorem activeMHD_int_eq_zero (P : Params)
    {S : Set (RealVec P.d)} {f : RealVec P.d → Complex}
    (data : PositiveInputDataHD P.alpha P.beta S f) (x : Torus P.d)
    (hx : FourierGoodParameterHD data x) (k : Int) :
    activeMHD data x (k : Complex) = 0 := by
  rw [← intEvaluatorHD_eq_activeMHD_int P data x hx.analytic k]
  exact hx.evaluatorZero k

end UniversalCompletenessHD.Internal
