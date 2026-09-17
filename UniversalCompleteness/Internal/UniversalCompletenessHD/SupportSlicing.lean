import UniversalCompletenessHD.GenericAuxiliary

/-!
# Canonical representative, cube layers, and sampling identity

The canonical data structure and all
transparent layer definitions are centralized in `Definitions.lean`.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators ComplexConjugate ENNReal Topology

namespace UniversalCompletenessHD.Internal

local instance sliceMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance sliceIsAddHaarMeasureUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance sliceIsProbabilityMeasureUnitAddCircle :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

private theorem measurable_torusToCubeHD {d : Nat} :
    Measurable (torusToCubeHD : Torus d → RealVec d) := by
  change Measurable (fun u : Torus d ↦
    ((torusIocEquivHD d u).1 : RealVec d))
  exact measurable_subtype_coe.comp (torusIocEquivHD d).measurable

private theorem measurable_intVecTranslate {d : Nat} (j : IntVec d) :
    Measurable (intVecTranslate j : Torus d → RealVec d) := by
  exact (measurable_torusToCubeHD (d := d)).const_add (intCast j)

/- Choose one strongly measurable representative of the
unconjugated zero extension, transfer integrability and every positive sample,
and record pointwise support and recovery. -/
theorem exists_positiveInputDataHD {d : Nat} (alpha beta : RealVec d)
    (S : Set (RealVec d)) (hSmeas : MeasurableSet S)
    (f : RealVec d → Complex) (hf : Integrable f (volume.restrict S))
    (hsample : ∀ n : IntVec d,
      positiveFourierSampleOnHD S f (modulatedLambdaHD alpha beta n) = 0) :
    Nonempty (PositiveInputDataHD alpha beta S f) := by
  let raw : RealVec d → Complex := zeroExtensionHD S f
  have hraw : Integrable raw volume := by
    simpa only [raw, zeroExtensionHD] using
      (integrable_indicator_iff hSmeas).2 hf
  let g : RealVec d → Complex := hraw.aestronglyMeasurable.mk raw
  have hraw_g : raw =ᵐ[volume] g :=
    hraw.aestronglyMeasurable.ae_eq_mk
  let H0 : RealVec d → Complex := S.indicator g
  have hg : Integrable g volume := hraw.congr hraw_g
  have hH0 : Integrable H0 volume := by
    simpa only [H0] using hg.indicator hSmeas
  have hH0_raw : H0 =ᵐ[volume] raw := by
    filter_upwards [hraw_g] with x hx
    by_cases hxS : x ∈ S
    · simp [H0, raw, zeroExtensionHD, hxS, ← hx]
    · simp [H0, raw, zeroExtensionHD, hxS]
  refine ⟨{
    H0 := H0
    stronglyMeasurable_H0 := ?_
    integrable_H0 := hH0
    zero_off := ?_
    ae_eq_zeroExtension := ?_
    positiveSamples := ?_
    recovery := ?_ }⟩
  · exact hraw.aestronglyMeasurable.stronglyMeasurable_mk.indicator hSmeas
  · intro x hx
    exact Set.indicator_of_notMem hx _
  · exact hH0_raw
  · intro n
    calc
      positiveFourierSampleOnHD Set.univ H0
          (modulatedLambdaHD alpha beta n) =
          positiveFourierSampleOnHD S f
            (modulatedLambdaHD alpha beta n) := by
        unfold positiveFourierSampleOnHD
        rw [Measure.restrict_univ, ← integral_indicator hSmeas]
        apply integral_congr_ae
        filter_upwards [hH0_raw] with x hx
        by_cases hxS : x ∈ S
        · simp [raw, zeroExtensionHD, hxS, hx]
        · rw [hx]
          simp [raw, zeroExtensionHD, hxS]
      _ = 0 := hsample n
  · intro hzero
    have hrawzero : raw =ᵐ[volume] (fun _ ↦ 0) :=
      hH0_raw.symm.trans hzero
    have hrawzeroS : raw =ᵐ[volume.restrict S] (fun _ ↦ 0) :=
      ae_mono Measure.restrict_le_self hrawzero
    have hind : zeroExtensionHD S f =ᵐ[volume.restrict S] f :=
      indicator_ae_eq_restrict hSmeas
    filter_upwards [hrawzeroS, hind] with x hxraw hxind
    simpa only [raw, hxind] using hxraw

/- Apply the vector cube-tiling integrability adapter to the
fixed whole-space representative. -/
theorem integrable_cubeSlice {d : Nat} {alpha beta : RealVec d}
    {S : Set (RealVec d)} {f : RealVec d → Complex}
    (data : PositiveInputDataHD alpha beta S f) (j : IntVec d) :
    Integrable (cubeSlice data j) volume := by
  have hshift : Integrable
      (fun x : RealVec d ↦ data.H0 (intCast j + x)) volume :=
    data.integrable_H0.comp_add_left (intCast j)
  have hcell : Integrable
      (fun x : RealVec d ↦ data.H0 (intCast j + x))
        (volume.restrict (iocUnitCubeHD d)) :=
    hshift.mono_measure Measure.restrict_le_self
  change Integrable
    ((fun x : RealVec d ↦ data.H0 (intCast j + x)) ∘ torusToCubeHD)
      volume
  exact ((measurePreserving_torusToCubeHD_ambient d).integrable_comp
    hcell.aestronglyMeasurable).2 hcell

/- Compose the strongly measurable fixed representative with
the measurable cell map and take the nonzero preimage. -/
theorem measurableSet_cubeSliceSupport {d : Nat} {alpha beta : RealVec d}
    {S : Set (RealVec d)} {f : RealVec d → Complex}
    (data : PositiveInputDataHD alpha beta S f) (j : IntVec d) :
    MeasurableSet (cubeSliceSupport data j) := by
  have hs : StronglyMeasurable (cubeSlice data j) := by
    exact data.stronglyMeasurable_H0.comp_measurable
      (measurable_intVecTranslate j)
  exact (measurableSet_singleton (0 : Complex)).compl.preimage hs.measurable

/- Apply Bochner tiling to `‖data.H0‖`, preserving the exact
`HasSum` equality. -/
theorem hasSum_cubeSlice_L1_norm {d : Nat} {alpha beta : RealVec d}
    {S : Set (RealVec d)} {f : RealVec d → Complex}
    (data : PositiveInputDataHD alpha beta S f) :
    HasSum
      (fun j : IntVec d ↦ ∫ u : Torus d, ‖cubeSlice data j u‖ ∂volume)
      (∫ x : RealVec d, ‖data.H0 x‖ ∂volume) := by
  simpa only [cubeSlice] using
    hasSum_integral_intVec_tiling (fun x : RealVec d ↦ ‖data.H0 x‖)
      data.integrable_H0.norm

/- Tile the measurable pointwise nonzero indicator of the
fixed representative. -/
theorem supportMassENNHD_eq_support_volume {d : Nat}
    {alpha beta : RealVec d} {S : Set (RealVec d)}
    {f : RealVec d → Complex} (data : PositiveInputDataHD alpha beta S f) :
    supportMassENNHD data = volume {x : RealVec d | data.H0 x ≠ 0} := by
  let A : Set (RealVec d) := {x | data.H0 x ≠ 0}
  have hA : MeasurableSet A :=
    (measurableSet_singleton (0 : Complex)).compl.preimage
      data.stronglyMeasurable_H0.measurable
  have htile := lintegral_intVec_tiling
    (A.indicator (1 : RealVec d → ENNReal))
    (measurable_const.indicator hA).aemeasurable
  rw [lintegral_indicator_one hA] at htile
  have hcell (j : IntVec d) :
      (∫⁻ u : Torus d,
        A.indicator (1 : RealVec d → ENNReal) (intVecTranslate j u)
          ∂volume) = volume (cubeSliceSupport data j) := by
    rw [← lintegral_indicator_one (measurableSet_cubeSliceSupport data j)]
    apply lintegral_congr
    intro u
    by_cases h : data.H0 (intVecTranslate j u) ≠ 0
    · simp [A, cubeSliceSupport, cubeSlice, h]
    · simp [A, cubeSliceSupport, cubeSlice, h]
  calc
    supportMassENNHD data =
        ∑' j : IntVec d, ∫⁻ u : Torus d,
          A.indicator (1 : RealVec d → ENNReal) (intVecTranslate j u)
            ∂volume := by
      unfold supportMassENNHD
      apply tsum_congr
      intro j
      exact (hcell j).symm
    _ = volume A := htile.symm
    _ = volume {x : RealVec d | data.H0 x ≠ 0} := rfl

/- The pointwise nonzero carrier is contained in `S` by the
stored zero-off-carrier field. -/
theorem supportMassENNHD_le_volume {d : Nat} {alpha beta : RealVec d}
    {S : Set (RealVec d)} {f : RealVec d → Complex}
    (data : PositiveInputDataHD alpha beta S f) :
    supportMassENNHD data ≤ volume S := by
  rw [supportMassENNHD_eq_support_volume data]
  apply measure_mono
  intro x hx
  by_contra hxS
  exact hx (data.zero_off x hxS)

/- Compare with the strict carrier threshold before any
`toReal` conversion. -/
theorem supportMassENNHD_lt_one {d : Nat} {alpha beta : RealVec d}
    {S : Set (RealVec d)} {f : RealVec d → Complex}
    (data : PositiveInputDataHD alpha beta S f)
    (hSlt : volume S < ENNReal.ofReal 1) :
    supportMassENNHD data < ENNReal.ofReal 1 ∧ supportMassENNHD data ≠ ∞ := by
  have hlt := lt_of_le_of_lt (supportMassENNHD_le_volume data) hSlt
  refine ⟨hlt, ?_⟩
  intro htop
  rw [htop] at hlt
  exact (not_lt_of_ge le_top) hlt

/- Use `ENNReal.ofReal_toReal` under an explicit non-top
certificate. -/
theorem ofReal_supportMassHD {d : Nat} {alpha beta : RealVec d}
    {S : Set (RealVec d)} {f : RealVec d → Complex}
    (data : PositiveInputDataHD alpha beta S f)
    (hfinite : supportMassENNHD data ≠ ∞) :
    ENNReal.ofReal (supportMassHD data) = supportMassENNHD data := by
  exact ENNReal.ofReal_toReal hfinite

/- Nonnegativity of `ENNReal.toReal`. -/
theorem supportMassHD_nonneg {d : Nat} {alpha beta : RealVec d}
    {S : Set (RealVec d)} {f : RealVec d → Complex}
    (data : PositiveInputDataHD alpha beta S f) :
    0 ≤ supportMassHD data := by
  exact ENNReal.toReal_nonneg

/- Convert the strict ENNReal support bound using the
non-top certificate supplied before conversion. -/
theorem supportMassHD_lt_one {d : Nat} {alpha beta : RealVec d}
    {S : Set (RealVec d)} {f : RealVec d → Complex}
    (data : PositiveInputDataHD alpha beta S f)
    (hSlt : volume S < ENNReal.ofReal 1) :
    supportMassHD data < 1 := by
  have h := supportMassENNHD_lt_one data hSlt
  rw [supportMassHD, ← ENNReal.toReal_one,
    ENNReal.toReal_lt_toReal h.2 ENNReal.one_ne_top]
  simpa using h.1

private theorem stronglyMeasurable_sampleLayerIntegrand {d : Nat}
    {alpha beta : RealVec d} {S : Set (RealVec d)}
    {f : RealVec d → Complex} (data : PositiveInputDataHD alpha beta S f)
    (n j : IntVec d) :
    StronglyMeasurable (sampleLayerIntegrand data n j) := by
  have htranslate : Measurable (intVecTranslate j : Torus d → RealVec d) :=
    measurable_intVecTranslate j
  have hcube : StronglyMeasurable (cubeSlice data j) :=
    data.stronglyMeasurable_H0.comp_measurable htranslate
  have hphase : StronglyMeasurable (fun u : Torus d ↦
      Complex.exp ((((2 * Real.pi : Real) : Complex) * Complex.I) *
        ((dotReal beta (intVecTranslate j u) * orbitThetaHD alpha n : Real) :
          Complex))) := by
    have hdot : Measurable
        (fun u : Torus d ↦ dotReal beta (intVecTranslate j u)) := by
      unfold dotReal
      simpa only [Function.comp_apply, Finset.sum_filter, Finset.mem_univ,
        and_self] using
        Finset.measurable_sum Finset.univ (fun i _ ↦
          measurable_const.mul ((measurable_pi_apply i).comp htranslate))
    have hreal := hdot.mul (measurable_const : Measurable
      (fun _ : Torus d ↦ orbitThetaHD alpha n))
    exact ((Complex.measurable_ofReal.comp hreal).const_mul
      (((2 * Real.pi : Real) : Complex) * Complex.I)).cexp.stronglyMeasurable
  have hchar : StronglyMeasurable (fun u : Torus d ↦
      fourierCharHD (fun i ↦ (n i : Real)) (torusToCubeHD u)) := by
    have hrep := measurable_torusToCubeHD (d := d)
    have hdot : Measurable (fun u : Torus d ↦
        dotReal (fun i ↦ (n i : Real)) (torusToCubeHD u)) := by
      unfold dotReal
      simpa only [Function.comp_apply, Finset.sum_filter, Finset.mem_univ,
        and_self] using
        Finset.measurable_sum Finset.univ (fun i _ ↦
          measurable_const.mul ((measurable_pi_apply i).comp hrep))
    exact ((Complex.measurable_ofReal.comp hdot).const_mul
      (((2 * Real.pi : Real) : Complex) * Complex.I)).cexp.stronglyMeasurable
  exact (hcube.mul hphase).mul hchar

private theorem integrable_sampleLayerIntegrand {d : Nat}
    {alpha beta : RealVec d} {S : Set (RealVec d)}
    {f : RealVec d → Complex} (data : PositiveInputDataHD alpha beta S f)
    (n j : IntVec d) :
    Integrable (sampleLayerIntegrand data n j) volume := by
  refine Integrable.mono' (integrable_cubeSlice data j).norm
    (stronglyMeasurable_sampleLayerIntegrand data n j).aestronglyMeasurable ?_
  filter_upwards with u
  simp [sampleLayerIntegrand, fourierCharHD, Complex.norm_exp]

/- Character factors have norm one, so the integral-norm
family is dominated by the exact summable slice-norm family. -/
theorem summable_integral_norm_sampleLayerIntegrand {d : Nat}
    {alpha beta : RealVec d} {S : Set (RealVec d)}
    {f : RealVec d → Complex} (data : PositiveInputDataHD alpha beta S f)
    (n : IntVec d) :
    Summable (fun j : IntVec d ↦
      ∫ u : Torus d, ‖sampleLayerIntegrand data n j u‖ ∂volume) := by
  have hbase := (hasSum_cubeSlice_L1_norm data).summable
  convert hbase using 1
  ext j
  apply integral_congr_ae
  filter_upwards with u
  simp [sampleLayerIntegrand, fourierCharHD, Complex.norm_exp]

/- Dominate the pointwise series by the summable family of
slice norms. -/
theorem integrable_sampleLayerSeries {d : Nat} {alpha beta : RealVec d}
    {S : Set (RealVec d)} {f : RealVec d → Complex}
    (data : PositiveInputDataHD alpha beta S f) (n : IntVec d) :
    Integrable (sampleLayerSeries data n) volume := by
  have hsum := summable_integral_norm_sampleLayerIntegrand data n
  have hne : (∑' j : IntVec d,
      ∫⁻ u : Torus d, ‖sampleLayerIntegrand data n j u‖ₑ ∂volume) ≠ ∞ := by
    calc
      (∑' j : IntVec d,
          ∫⁻ u : Torus d, ‖sampleLayerIntegrand data n j u‖ₑ ∂volume) =
          ∑' j : IntVec d, ENNReal.ofReal
            (∫ u : Torus d, ‖sampleLayerIntegrand data n j u‖ ∂volume) := by
        apply tsum_congr
        intro j
        exact (MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm
          (integrable_sampleLayerIntegrand data n j)).symm
      _ ≠ ∞ := hsum.tsum_ofReal_ne_top
  constructor
  · unfold sampleLayerSeries
    exact AEStronglyMeasurable.tsum (fun j ↦
      (stronglyMeasurable_sampleLayerIntegrand data n j).aestronglyMeasurable)
  · rw [hasFiniteIntegral_iff_enorm]
    refine lt_of_le_of_lt (lintegral_mono (fun u ↦
      enorm_tsum_le_tsum_enorm)) ?_
    rw [MeasureTheory.lintegral_tsum (fun j ↦
      (stronglyMeasurable_sampleLayerIntegrand data n j).enorm.aemeasurable)]
    exact lt_top_iff_ne_top.mpr hne

/- Consume the separate norm-summability certificate before
applying the Bochner `integral_tsum` theorem. -/
theorem integral_sampleLayerSeries_eq_tsum {d : Nat}
    {alpha beta : RealVec d} {S : Set (RealVec d)}
    {f : RealVec d → Complex} (data : PositiveInputDataHD alpha beta S f)
    (n : IntVec d) :
    (∫ u : Torus d, sampleLayerSeries data n u ∂volume) =
      ∑' j : IntVec d,
        ∫ u : Torus d, sampleLayerIntegrand data n j u ∂volume := by
  unfold sampleLayerSeries
  exact (MeasureTheory.integral_tsum_of_summable_integral_norm
    (fun j ↦ integrable_sampleLayerIntegrand data n j)
    (summable_integral_norm_sampleLayerIntegrand data n)).symm

private theorem fourierChar_modulated_intVecTranslate {d : Nat}
    (alpha beta : RealVec d) (n j : IntVec d) (u : Torus d) :
    fourierCharHD (modulatedLambdaHD alpha beta n)
        (intVecTranslate j u) =
      Complex.exp ((((2 * Real.pi : Real) : Complex) * Complex.I) *
        ((dotReal beta (intVecTranslate j u) * orbitThetaHD alpha n : Real) :
          Complex)) *
        fourierCharHD (fun i ↦ (n i : Real)) (torusToCubeHD u) := by
  let k : Int := ∑ i, n i * j i
  have harg :
      (((2 * Real.pi : Real) : Complex) * Complex.I) *
          (dotReal (modulatedLambdaHD alpha beta n)
            (intVecTranslate j u) : Complex) =
        (k : Complex) * (2 * (Real.pi : Complex) * Complex.I) +
          ((((2 * Real.pi : Real) : Complex) * Complex.I) *
              ((dotReal beta (intVecTranslate j u) *
                orbitThetaHD alpha n : Real) : Complex) +
            (((2 * Real.pi : Real) : Complex) * Complex.I) *
              (dotReal (fun i ↦ (n i : Real)) (torusToCubeHD u) :
                Complex)) := by
    simp only [modulatedLambdaHD, modulatedDeltaHD, intVecTranslate,
      intCast, dotReal, Pi.add_apply]
    simp_rw [add_mul, mul_add]
    rw [Finset.sum_add_distrib]
    simp_rw [Finset.sum_add_distrib]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    dsimp only [k]
    push_cast
    ring
  unfold fourierCharHD
  rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul,
    Complex.exp_add]

/- Split the whole-space positive sample into integer-vector
cube layers, cancel the integer character, and recombine. -/
theorem positive_sample_eq_cube_sampling_identity {d : Nat}
    {alpha beta : RealVec d} {S : Set (RealVec d)}
    {f : RealVec d → Complex} (data : PositiveInputDataHD alpha beta S f)
    (n : IntVec d) :
    positiveFourierSampleOnHD Set.univ data.H0
        (modulatedLambdaHD alpha beta n) =
      ∫ u : Torus d, sampleLayerSeries data n u ∂volume := by
  let F : RealVec d → Complex := fun x ↦
    data.H0 x * fourierCharHD (modulatedLambdaHD alpha beta n) x
  have hchar : StronglyMeasurable (fun x : RealVec d ↦
      fourierCharHD (modulatedLambdaHD alpha beta n) x) := by
    apply Measurable.stronglyMeasurable
    unfold fourierCharHD dotReal
    fun_prop
  have hF : Integrable F volume := by
    refine Integrable.mono' data.integrable_H0.norm
      (data.stronglyMeasurable_H0.mul hchar).aestronglyMeasurable ?_
    filter_upwards with x
    simp [F, fourierCharHD, Complex.norm_exp]
  have htile := hasSum_integral_intVec_tiling F hF
  have hcell (j : IntVec d) :
      (∫ u : Torus d, F (intVecTranslate j u) ∂volume) =
        ∫ u : Torus d, sampleLayerIntegrand data n j u ∂volume := by
    apply integral_congr_ae
    filter_upwards with u
    unfold F sampleLayerIntegrand cubeSlice
    rw [fourierChar_modulated_intVecTranslate alpha beta n j u]
    ring
  unfold positiveFourierSampleOnHD
  rw [Measure.restrict_univ]
  change (∫ x : RealVec d, F x ∂volume) = _
  calc
    (∫ x : RealVec d, F x ∂volume) =
        ∑' j : IntVec d, ∫ u : Torus d,
          F (intVecTranslate j u) ∂volume := htile.tsum_eq.symm
    _ = ∑' j : IntVec d, ∫ u : Torus d,
          sampleLayerIntegrand data n j u ∂volume := tsum_congr hcell
    _ = ∫ u : Torus d, sampleLayerSeries data n u ∂volume :=
      (integral_sampleLayerSeries_eq_tsum data n).symm

/- Rewrite the cube-sampling integral by the whole-space
sample and use the sample-zero field stored in the fixed data. -/
theorem cube_sampling_identity_eq_zero {d : Nat}
    {alpha beta : RealVec d} {S : Set (RealVec d)}
    {f : RealVec d → Complex} (data : PositiveInputDataHD alpha beta S f)
    (n : IntVec d) :
    (∫ u : Torus d, sampleLayerSeries data n u ∂volume) = 0 := by
  rw [← positive_sample_eq_cube_sampling_identity data n]
  exact data.positiveSamples n

/- Conjugate the integrand and integral at the same carrier
and frequency; no reflection of `S` or negation of `xi` occurs. -/
theorem positive_sample_conj_eq_conj_negative_sampleHD {d : Nat}
    (S : Set (RealVec d)) (hSmeas : MeasurableSet S)
    (f : RealVec d → Complex) (hf : Integrable f (volume.restrict S))
    (xi : RealVec d) :
    positiveFourierSampleOnHD S (fun x ↦ starRingEnd Complex (f x)) xi =
      starRingEnd Complex (negativeFourierSampleOnHD S f xi) := by
  unfold positiveFourierSampleOnHD negativeFourierSampleOnHD
  calc
    (∫ x in S, starRingEnd Complex (f x) * fourierCharHD xi x
        ∂volume) =
        ∫ x in S, starRingEnd Complex
          (f x * starRingEnd Complex (fourierCharHD xi x)) ∂volume := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [map_mul, starRingEnd_self_apply]
    _ = starRingEnd Complex
        (∫ x in S, f x * starRingEnd Complex (fourierCharHD xi x)
          ∂volume) := integral_conj

/- Complex conjugation is involutive and preserves zero,
filterwise under the same restricted measure. -/
theorem restricted_ae_zero_conj_iffHD {d : Nat} (S : Set (RealVec d))
    (f : RealVec d → Complex) :
    (fun x ↦ starRingEnd Complex (f x)) =ᵐ[volume.restrict S]
        (fun _ ↦ 0) ↔
      f =ᵐ[volume.restrict S] (fun _ ↦ 0) := by
  constructor
  · intro h
    filter_upwards [h] with x hx
    have hx' := congrArg (starRingEnd Complex) hx
    simpa using hx'
  · intro h
    filter_upwards [h] with x hx
    simp [hx]

end UniversalCompletenessHD.Internal
