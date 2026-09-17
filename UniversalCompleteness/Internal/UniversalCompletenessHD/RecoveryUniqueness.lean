import UniversalCompletenessHD.GenericAuxiliary
import UniversalCompletenessHD.SupportSlicing
import UniversalCompletenessHD.PoleCoordinates
import UniversalCompletenessHD.PoleDensity
import UniversalCompletenessHD.JensenContradiction

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace UniversalCompletenessHD.Internal

/- An empty active subtype forces every residue to vanish. -/
private theorem residueCoordHD_eq_zero_of_isEmpty_active {d : Nat}
    {alpha beta : RealVec d} {S : Set (RealVec d)} {f : RealVec d → Complex}
    (data : PositiveInputDataHD alpha beta S f) (x : Torus d)
    (hEmpty : IsEmpty (ActiveIndexHD data x)) (j : IntVec d) (q : Int) :
    residueCoordHD data alpha beta x j q = 0 := by
  by_contra hres
  exact (@IsEmpty.false (ActiveIndexHD data x) hEmpty)
    (⟨(j, q), hres⟩ : ActiveIndexHD data x)

/- Recover a slice by choosing `q = -floorBetaDot beta j`. -/
private theorem cubeSlice_eq_zero_of_isEmpty_activeHD {d : Nat}
    {alpha beta : RealVec d} {S : Set (RealVec d)} {f : RealVec d → Complex}
    (data : PositiveInputDataHD alpha beta S f) (x : Torus d)
    (hxBad : x ∉ sineBadHD alpha beta)
    (hEmpty : IsEmpty (ActiveIndexHD data x)) (j : IntVec d) :
    cubeSlice data j x = 0 := by
  let q : Int := -floorBetaDot beta j
  have hu : uCoordHD alpha beta x j q = x := by
    simp [q, uCoordHD, uOrbitHD, ellIndexHD]
  by_contra hslice
  have hslice' : cubeSlice data j (uCoordHD alpha beta x j q) ≠ 0 := by
    simpa only [hu] using hslice
  have hres : residueCoordHD data alpha beta x j q ≠ 0 :=
    (residueCoordHD_ne_zero_iff data x hxBad j q).mpr hslice'
  exact hres
    (residueCoordHD_eq_zero_of_isEmpty_active data x hEmpty j q)

/- One common conull set makes every integer-vector layer zero. -/
private theorem cubeSlice_all_eq_zero_aeHD (P : Params) {S : Set (RealVec P.d)}
    {f : RealVec P.d → Complex}
    (data : PositiveInputDataHD P.alpha P.beta S f)
    (hSlt : volume S < ENNReal.ofReal 1) :
    ∀ᵐ x : Torus P.d ∂volume, ∀ j : IntVec P.d, cubeSlice data j x = 0 := by
  have hmass : supportMassHD data < 1 := supportMassHD_lt_one data hSlt
  have hSlt' : volume S < 1 := by simpa using hSlt
  filter_upwards [poleGoodParameterHD_ae P data hSlt'] with x hx
  intro j
  exact cubeSlice_eq_zero_of_isEmpty_activeHD data x
    hx.fourierGood.analytic.offBad
    (activeIndexHD_isEmpty P data x hmass hx) j

/- Reconstruct the whole-space representative from its cube layers. -/
private theorem positiveRepresentativeHD_ae_eq_zero (P : Params)
    {S : Set (RealVec P.d)} {f : RealVec P.d → Complex}
    (data : PositiveInputDataHD P.alpha P.beta S f)
    (hSlt : volume S < ENNReal.ofReal 1) :
    data.H0 =ᵐ[volume] (fun _ ↦ 0) := by
  have hall := cubeSlice_all_eq_zero_aeHD P data hSlt
  have hvolume : (volume : Measure (Torus P.d)) =
      Measure.pi (fun _ : Fin P.d ↦ AddCircle.haarAddCircle) := by
    rw [volume_pi]
    congr 1
    funext i
    simpa using
      (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : Real)))
  apply ae_of_ae_all_intVec_slices data.H0 data.stronglyMeasurable_H0
  intro j
  change (fun u : Torus P.d ↦ data.H0 (intVecTranslate j u))
      =ᵐ[Measure.pi (fun _ : Fin P.d ↦ AddCircle.haarAddCircle)]
        (fun _ ↦ 0)
  rw [← hvolume]
  exact hall.mono fun x hx ↦ hx j

/- Transfer representative vanishing back to the original input. -/
private theorem positiveOriginalInputHD_ae_eq_zero (P : Params)
    {S : Set (RealVec P.d)} {f : RealVec P.d → Complex}
    (data : PositiveInputDataHD P.alpha P.beta S f)
    (hSlt : volume S < ENNReal.ofReal 1) :
    f =ᵐ[volume.restrict S] (fun _ ↦ 0) := by
  exact data.recovery (positiveRepresentativeHD_ae_eq_zero P data hSlt)

/- Fixed-input positive-sign `L1` uniqueness. -/
private theorem l1_uniqueness_positive_fixedHD (P : Params)
    (S : Set (RealVec P.d)) (hSmeas : MeasurableSet S)
    (hSlt : volume S < ENNReal.ofReal 1) (f : RealVec P.d → Complex)
    (hf : Integrable f (volume.restrict S))
    (hsample : ∀ n : IntVec P.d,
      positiveFourierSampleOnHD S f (modulatedLambdaHD P.alpha P.beta n) = 0) :
    f =ᵐ[volume.restrict S] (fun _ ↦ 0) := by
  let data := Classical.choice
    (exists_positiveInputDataHD P.alpha P.beta S hSmeas f hf hsample)
  exact positiveOriginalInputHD_ae_eq_zero P data hSlt

/- Fixed-input article-sign `L1` uniqueness. -/
theorem l1_uniqueness_negative_fixedHD (P : Params)
    (S : Set (RealVec P.d)) (hSmeas : MeasurableSet S)
    (hSlt : volume S < ENNReal.ofReal 1) (f : RealVec P.d → Complex)
    (hf : Integrable f (volume.restrict S))
    (hsample : ∀ n : IntVec P.d,
      negativeFourierSampleOnHD S f (modulatedLambdaHD P.alpha P.beta n) = 0) :
    f =ᵐ[volume.restrict S] (fun _ ↦ 0) := by
  have hfconj : Integrable (fun x ↦ starRingEnd Complex (f x))
      (volume.restrict S) := by
    exact Complex.conjCLE.toContinuousLinearMap.integrable_comp hf
  have hpositive : ∀ n : IntVec P.d,
      positiveFourierSampleOnHD S (fun x ↦ starRingEnd Complex (f x))
        (modulatedLambdaHD P.alpha P.beta n) = 0 := by
    intro n
    rw [positive_sample_conj_eq_conj_negative_sampleHD S hSmeas f hf]
    rw [hsample n]
    simp
  have hconjzero := l1_uniqueness_positive_fixedHD P S hSmeas hSlt
    (fun x ↦ starRingEnd Complex (f x)) hfconj hpositive
  exact (restricted_ae_zero_conj_iffHD S f).mp hconjzero

end UniversalCompletenessHD.Internal

namespace UniversalCompletenessHD

/- Universal negative-sign `L1` uniqueness for the range set. -/
theorem modulatedLambdaSetHD_universalL1
    (d : Nat) (hd : 0 < d) (alpha beta : RealVec d)
    (hAlpha : RationallyIndependentWithOneHD alpha)
    (hPole : PoleNonresonant alpha beta)
    (hBeta : euclideanNormHD beta < 1 / 2) :
    UniversalL1UniquenessNegHD (modulatedLambdaSetHD alpha beta) := by
  let P : Params := {
    d := d
    hd := hd
    alpha := alpha
    beta := beta
    alpha_independent := hAlpha
    pole_nonresonant := hPole
    beta_small := hBeta }
  intro S hSmeas hSlt f hf hsample
  apply Internal.l1_uniqueness_negative_fixedHD P S hSmeas hSlt f hf
  intro n
  exact hsample (modulatedLambdaHD alpha beta n) ⟨n, rfl⟩

end UniversalCompletenessHD
