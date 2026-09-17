import IntegerFrequenciesHD.CubeTorusBridge
import IntegerFrequenciesHD.ProductFejerApproximation
import IntegerFrequenciesHD.TorusRotationErgodic
import Theorem12.GenericAuxiliary
import Theorem12.GenericLpDuality
import Theorem12.SincIdentity

/-!
# Universal completeness in arbitrary dimension: centralized definitions

This file centralizes the transparent definitions and proposition-valued data
used in the higher-dimensional completeness theorem.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace UniversalCompletenessHD

/- Coordinate model for real vectors. -/
abbrev RealVec (d : Nat) := Fin d → Real

/- Coordinate model for integer vectors. -/
abbrev IntVec (d : Nat) := Fin d → Int

namespace Internal

/- Native normalized product torus. -/
abbrev Torus (d : Nat) := UnitAddTorus (Fin d)

end Internal

local instance : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/- Explicit source Euclidean norm, not the Pi sup norm. -/
def euclideanNormHD {d : Nat} (x : RealVec d) : Real :=
  Real.sqrt (∑ i, (x i) ^ 2)

/- Real coordinate dot product. -/
def dotReal {d : Nat} (x y : RealVec d) : Real :=
  ∑ i, x i * y i

/- Integer-real coordinate pairing. -/
def dotIntReal {d : Nat} (n : IntVec d) (alpha : RealVec d) : Real :=
  ∑ i, (n i : Real) * alpha i

/- Rational independence of one and all alpha coordinates. -/
def RationallyIndependentWithOneHD {d : Nat} (alpha : RealVec d) : Prop :=
  ∀ (q0 : Rat) (q : Fin d → Rat),
    (q0 : Real) + ∑ i, (q i : Real) * alpha i = 0 →
      q0 = 0 ∧ ∀ i, q i = 0

/- Rational independence of `1 + alpha·beta` and beta. -/
def PoleNonresonant {d : Nat} (alpha beta : RealVec d) : Prop :=
  ∀ (q0 : Rat) (q : Fin d → Rat),
    (q0 : Real) * (1 + dotReal alpha beta) +
        ∑ i, (q i : Real) * beta i = 0 →
      q0 = 0 ∧ ∀ i, q i = 0

/- Exactly the hypotheses in the article statement. -/
structure Params where
  d : Nat
  hd : 0 < d
  alpha : RealVec d
  beta : RealVec d
  alpha_independent : RationallyIndependentWithOneHD alpha
  pole_nonresonant : PoleNonresonant alpha beta
  beta_small : euclideanNormHD beta < 1 / 2

/- Centered orbit phase. -/
def orbitThetaHD {d : Nat} (alpha : RealVec d) (n : IntVec d) : Real :=
  Int.fract (dotIntReal n alpha) - 1 / 2

/- Rank-one modulation displacement. -/
def modulatedDeltaHD {d : Nat} (alpha beta : RealVec d)
    (n : IntVec d) : RealVec d :=
  fun i ↦ orbitThetaHD alpha n * beta i

/- Modulated frequency. -/
def modulatedLambdaHD {d : Nat} (alpha beta : RealVec d)
    (n : IntVec d) : RealVec d :=
  fun i ↦ (n i : Real) + modulatedDeltaHD alpha beta n i

/- Set of modulated frequencies. -/
def modulatedLambdaSetHD {d : Nat} (alpha beta : RealVec d) : Set (RealVec d) :=
  Set.range (modulatedLambdaHD alpha beta)

/- Half-open translated cube. -/
def realCubeHD {d : Nat} (x : RealVec d) (R : Real) : Set (RealVec d) :=
  {y | ∀ i, x i ≤ y i ∧ y i < x i + R}

/- Cardinality of real frequencies in a half-open cube. -/
def realFrequencyCubeCountHD {d : Nat} (Lambda : Set (RealVec d))
    (x : RealVec d) (R : Real) : Nat :=
  Set.ncard (Lambda ∩ realCubeHD x R)

/- Euclidean uniform discreteness. -/
def IsUniformlyDiscreteHD {d : Nat} (Lambda : Set (RealVec d)) : Prop :=
  ∃ rho : Real, 0 < rho ∧
    ∀ x ∈ Lambda, ∀ y ∈ Lambda, x ≠ y →
      rho ≤ euclideanNormHD (fun i ↦ x i - y i)

/- Coordinate displacement buffer. -/
def cubeBufferHD {d : Nat} (beta : RealVec d) : Real :=
  euclideanNormHD beta / 2

/- One-dimensional lattice count error per coordinate. -/
def cubeCoordinateErrorHD {d : Nat} (beta : RealVec d) : Real :=
  1 + 2 * cubeBufferHD beta

/- Explicit `d,beta`-only count constant. -/
def cubeCountConstantHD (d : Nat) (beta : RealVec d) : Real :=
  let D := cubeCoordinateErrorHD beta
  (d : Real) * D * (1 + D) ^ (d - 1)

/- Quantitative uniform cubical count estimate. -/
structure HasCubicalCountEstimateOneHD {d : Nat}
    (Lambda : Set (RealVec d)) (C : Real) : Prop where
  constant_nonneg : 0 ≤ C
  finite_count : ∀ (x : RealVec d) (R : Real), 1 ≤ R →
    (Lambda ∩ realCubeHD x R).Finite
  uniform_error : ∀ (x : RealVec d) (R : Real), 1 ≤ R →
    |((realFrequencyCubeCountHD Lambda x R : Nat) : Real) - R ^ d| ≤
      C * (R ^ (d - 1) + 1)

/- Literal uniform cubical density-one predicate. -/
structure HasUniformCubicalDensityOneHD {d : Nat}
    (Lambda : Set (RealVec d)) : Prop where
  finite_count : ∀ (x : RealVec d) (R : Real), 0 ≤ R →
    (Lambda ∩ realCubeHD x R).Finite
  uniform_limit : ∀ epsilon : Real, 0 < epsilon →
    ∃ R0 : Real, 0 < R0 ∧ ∀ (x : RealVec d) (R : Real), R0 ≤ R →
      |((realFrequencyCubeCountHD Lambda x R : Nat) : Real) / R ^ d - 1| < epsilon

/- Positive Fourier character. -/
def fourierCharHD {d : Nat} (xi x : RealVec d) : Complex :=
  Complex.exp
    (((2 * Real.pi : Real) : Complex) * Complex.I * (dotReal xi x : Complex))

/- Article sample with negative/conjugated Fourier sign. -/
def negativeFourierSampleOnHD {d : Nat} (S : Set (RealVec d))
    (f : RealVec d → Complex) (xi : RealVec d) : Complex :=
  ∫ x in S, f x * starRingEnd Complex (fourierCharHD xi x)

namespace Internal

/- Internal positive-sign Fourier sample. -/
def positiveFourierSampleOnHD {d : Nat} (S : Set (RealVec d))
    (f : RealVec d → Complex) (xi : RealVec d) : Complex :=
  ∫ x in S, f x * fourierCharHD xi x

end Internal

/- Universal negative-sign `L1` uniqueness. -/
def UniversalL1UniquenessNegHD {d : Nat} (Lambda : Set (RealVec d)) : Prop :=
  ∀ (S : Set (RealVec d)), MeasurableSet S → volume S < ENNReal.ofReal 1 →
    ∀ (f : RealVec d → Complex), Integrable f (volume.restrict S) →
      (∀ xi ∈ Lambda, negativeFourierSampleOnHD S f xi = 0) →
        f =ᵐ[volume.restrict S] (fun _ ↦ 0)

namespace Internal

/- Prove continuity, norm one, and finite
measure membership, then call `MemLp.of_bound`. -/
theorem memLp_fourierCharHD_restrict {d : Nat}
    (S : Set (RealVec d)) (hSmeas : MeasurableSet S)
    (hSfinite : volume S ≠ ∞) (p : ENNReal) (hp : 1 ≤ p)
    (xi : RealVec d) :
    MemLp (fun x ↦ fourierCharHD xi x) p (volume.restrict S) := by
  letI : IsFiniteMeasure (volume.restrict S) :=
    ⟨by
      simpa [Measure.restrict_apply_univ, hSmeas] using
        (lt_top_iff_ne_top.mpr hSfinite)⟩
  apply MemLp.of_bound (C := 1)
  · apply Continuous.aestronglyMeasurable
    unfold fourierCharHD dotReal
    fun_prop
  · filter_upwards with x
    rw [fourierCharHD, Complex.norm_exp]
    simp

end Internal

/- Positive character as an actual restricted `Lp` element. -/
def positiveExponentialLpHD {d : Nat}
    (S : Set (RealVec d)) (hSmeas : MeasurableSet S)
    (p : ENNReal) (hp : 1 ≤ p) (hSfinite : volume S ≠ ∞)
    (xi : RealVec d) : Lp Complex p (volume.restrict S) := by
  letI : Fact (1 ≤ p) := ⟨hp⟩
  exact (Internal.memLp_fourierCharHD_restrict
    S hSmeas hSfinite p hp xi).toLp (fun x ↦ fourierCharHD xi x)

/- Dense span of the positive exponentials in actual `Lp`. -/
def ExponentialCompleteInLpHD {d : Nat}
    (Lambda : Set (RealVec d)) (S : Set (RealVec d))
    (hSmeas : MeasurableSet S) (p : ENNReal) (hp : 1 ≤ p)
    (hSfinite : volume S ≠ ∞) : Prop := by
  letI : Fact (1 ≤ p) := ⟨hp⟩
  letI : IsFiniteMeasure (volume.restrict S) :=
    isFiniteMeasure_restrict.mpr hSfinite
  exact Dense (↑(Submodule.span Complex
    (Set.range (fun xi : {xi : RealVec d // xi ∈ Lambda} ↦
      positiveExponentialLpHD S hSmeas p hp hSfinite xi.1))) :
        Set (Lp Complex p (volume.restrict S)))

/- Universal completeness for every finite `p`, including one. -/
def UniversalFiniteLpCompletenessHD {d : Nat}
    (Lambda : Set (RealVec d)) : Prop :=
  ∀ (S : Set (RealVec d)) (hSmeas : MeasurableSet S)
    (hSlt : volume S < ENNReal.ofReal 1)
    (p : ENNReal) (hp : 1 ≤ p) (hpTop : p ≠ ∞),
      ExponentialCompleteInLpHD Lambda S hSmeas p hp
        (ne_of_lt (lt_of_lt_of_le hSlt le_top))

/- The five protected article conclusions. -/
structure UniversalCompletenessHDConclusion
    (d : Nat) (alpha beta : RealVec d) : Prop where
  uniformlyDiscrete : IsUniformlyDiscreteHD (modulatedLambdaSetHD alpha beta)
  countEstimate : HasCubicalCountEstimateOneHD
    (modulatedLambdaSetHD alpha beta) (cubeCountConstantHD d beta)
  uniformDensity : HasUniformCubicalDensityOneHD (modulatedLambdaSetHD alpha beta)
  universalL1 : UniversalL1UniquenessNegHD (modulatedLambdaSetHD alpha beta)
  completeLp : UniversalFiniteLpCompletenessHD (modulatedLambdaSetHD alpha beta)

namespace Internal

/- Coordinatewise coercion used by the later definitions. -/
def intCast {d : Nat} (j : IntVec d) : RealVec d :=
  fun i ↦ (j i : Real)

/- Transparent aliases of the `IntegerFrequenciesHD` native-cell API. -/
def iocUnitCubeHD (d : Nat) : Set (RealVec d) :=
  IntegerFrequenciesHD.Internal.iocUnitCubeHD d

noncomputable def torusIocEquivHD (d : Nat) :
    Torus d ≃ᵐ {x : RealVec d // x ∈ iocUnitCubeHD d} :=
  IntegerFrequenciesHD.Internal.torusIocEquivHD d

/- Native `(0,1]^d` representative. -/
def torusToCubeHD {d : Nat} (u : Torus d) : RealVec d :=
  (torusIocEquivHD d u).1

/- Integer translate of the native representative. -/
def intVecTranslate {d : Nat} (j : IntVec d) (u : Torus d) : RealVec d :=
  intCast j + torusToCubeHD u

/- Native multitorus Fourier coefficient convention. -/
def mFourierCoeffHD {d : Nat} (F : Torus d → Complex) (n : IntVec d) : Complex :=
  UnitAddTorus.mFourierCoeff F n

/- Coordinate-preserving map into Euclidean space. -/
def toEuclideanSpaceHD {d : Nat}
    (x : RealVec d) : EuclideanSpace Real (Fin d) :=
  WithLp.toLp 2 x

/- Indexed preimage of a frequency cube. -/
def frequencyIndexCubeHD {d : Nat} (alpha beta x : RealVec d) (R : Real) :
    Set (IntVec d) :=
  {n | modulatedLambdaHD alpha beta n ∈ realCubeHD x R}

/- Coordinatewise inner lattice cube. -/
def innerLatticeCubeHD {d : Nat} (beta x : RealVec d) (R : Real) :
    Set (IntVec d) :=
  {n | ∀ i, x i + cubeBufferHD beta ≤ (n i : Real) ∧
    (n i : Real) < x i + R - cubeBufferHD beta}

/- Coordinatewise outer lattice cube. -/
def outerLatticeCubeHD {d : Nat} (beta x : RealVec d) (R : Real) :
    Set (IntVec d) :=
  {n | ∀ i, x i - cubeBufferHD beta ≤ (n i : Real) ∧
    (n i : Real) < x i + R + cubeBufferHD beta}

/- Whole-space zero extension. -/
def zeroExtensionHD {d : Nat} (S : Set (RealVec d))
    (f : RealVec d → Complex) : RealVec d → Complex :=
  S.indicator f

/- One fixed strongly measurable representative of the
unconjugated zero extension for the positive-sign analytic route. -/
structure PositiveInputDataHD {d : Nat} (alpha beta : RealVec d)
    (S : Set (RealVec d)) (f : RealVec d → Complex) where
  H0 : RealVec d → Complex
  stronglyMeasurable_H0 : StronglyMeasurable H0
  integrable_H0 : Integrable H0 volume
  zero_off : ∀ x, x ∉ S → H0 x = 0
  ae_eq_zeroExtension :
    H0 =ᵐ[volume] zeroExtensionHD S f
  positiveSamples : ∀ n : IntVec d,
    positiveFourierSampleOnHD Set.univ H0 (modulatedLambdaHD alpha beta n) = 0
  recovery : H0 =ᵐ[volume] (fun _ ↦ 0) →
    f =ᵐ[volume.restrict S] (fun _ ↦ 0)

/- Integer-cell slice of the fixed representative. -/
def cubeSlice {d : Nat} {alpha beta : RealVec d} {S : Set (RealVec d)}
    {f : RealVec d → Complex} (data : PositiveInputDataHD alpha beta S f)
    (j : IntVec d) (u : Torus d) : Complex :=
  data.H0 (intVecTranslate j u)

/- Pointwise nonzero carrier of a slice. -/
def cubeSliceSupport {d : Nat} {alpha beta : RealVec d} {S : Set (RealVec d)}
    {f : RealVec d → Complex} (data : PositiveInputDataHD alpha beta S f)
    (j : IntVec d) : Set (Torus d) :=
  {u | cubeSlice data j u ≠ 0}

/- Raw ENNReal support mass. -/
def supportMassENNHD {d : Nat} {alpha beta : RealVec d} {S : Set (RealVec d)}
    {f : RealVec d → Complex} (data : PositiveInputDataHD alpha beta S f) : ENNReal :=
  ∑' j : IntVec d, volume (cubeSliceSupport data j)

/- Real support mass after total conversion. -/
def supportMassHD {d : Nat} {alpha beta : RealVec d} {S : Set (RealVec d)}
    {f : RealVec d → Complex} (data : PositiveInputDataHD alpha beta S f) : Real :=
  (supportMassENNHD data).toReal

/- Exact positive sampling-layer integrand. -/
def sampleLayerIntegrand {d : Nat} {alpha beta : RealVec d}
    {S : Set (RealVec d)} {f : RealVec d → Complex}
    (data : PositiveInputDataHD alpha beta S f) (n j : IntVec d) (u : Torus d) : Complex :=
  cubeSlice data j u *
    Complex.exp ((((2 * Real.pi : Real) : Complex) * Complex.I) *
      ((dotReal beta (intVecTranslate j u) * orbitThetaHD alpha n : Real) : Complex)) *
    fourierCharHD (fun i ↦ (n i : Real)) (torusToCubeHD u)

/- Pointwise sum of the sampling layers. -/
def sampleLayerSeries {d : Nat} {alpha beta : RealVec d}
    {S : Set (RealVec d)} {f : RealVec d → Complex}
    (data : PositiveInputDataHD alpha beta S f) (n : IntVec d) (u : Torus d) : Complex :=
  ∑' j : IntVec d, sampleLayerIntegrand data n j u

/- Coordinatewise quotient of alpha in the multitorus. -/
def alphaTorusHD {d : Nat} (alpha : RealVec d) : Torus d :=
  fun i ↦ (alpha i : UnitAddCircle)

/- Signed subtraction orbit. -/
def uOrbitHD {d : Nat} (alpha : RealVec d) (x : Torus d) (ell : Int) : Torus d :=
  x - ell • alphaTorusHD alpha

/- Floor of beta dotted with the integer layer. -/
def floorBetaDot {d : Nat} (beta : RealVec d) (j : IntVec d) : Int :=
  ⌊dotReal beta (intCast j)⌋

/- Complex integer parity. -/
def intParityHD (m : Int) : Complex :=
  (-1 : Complex) ^ m

/- Row reindexing. -/
def ellIndexHD {d : Nat} (beta : RealVec d) (j : IntVec d) (q : Int) : Int :=
  floorBetaDot beta j + q

/- Exact signed integer translation equivalence. -/
def ellIndexEquivHD {d : Nat} (beta : RealVec d) (j : IntVec d) : Int ≃ Int where
  toFun := ellIndexHD beta j
  invFun := fun ell ↦ ell - floorBetaDot beta j
  left_inv := by intro q; simp [ellIndexHD]
  right_inv := by intro ell; simp [ellIndexHD]

/- Torus coordinate for a layer and row. -/
def uCoordHD {d : Nat} (alpha beta : RealVec d) (x : Torus d)
    (j : IntVec d) (q : Int) : Torus d :=
  uOrbitHD alpha x (ellIndexHD beta j q)

/- Unreduced source phase. -/
def rawPhaseHD {d : Nat} (beta : RealVec d) (j : IntVec d) (u : Torus d) : Real :=
  dotReal beta (torusToCubeHD u + intCast j)

/- Floor-reduced phase. -/
def reducedPhaseHD {d : Nat} (alpha beta : RealVec d) (x : Torus d)
    (j : IntVec d) (q : Int) : Real :=
  Int.fract (dotReal beta (intCast j)) +
    dotReal beta (torusToCubeHD (uCoordHD alpha beta x j q))

/- Scalar real pole coordinate. -/
def poleCoordHD {d : Nat} (alpha beta : RealVec d) (x : Torus d)
    (j : IntVec d) (q : Int) : Real :=
  (ellIndexHD beta j q : Real) - rawPhaseHD beta j (uCoordHD alpha beta x j q)

/- Exact source residue. -/
def residueCoordHD {d : Nat} {dataAlpha dataBeta : RealVec d}
    {S : Set (RealVec d)} {f : RealVec d → Complex}
    (data : PositiveInputDataHD dataAlpha dataBeta S f)
    (alpha beta : RealVec d) (x : Torus d) (j : IntVec d) (q : Int) : Complex :=
  ((Real.sin (Real.pi * rawPhaseHD beta j (uCoordHD alpha beta x j q)) : Real) : Complex) /
      (Real.pi : Complex) *
    cubeSlice data j (uCoordHD alpha beta x j q)

/- Explicit beta-dependent pole displacement bound. -/
def poleShiftConstantHD {d : Nat} (beta : RealVec d) : Real :=
  1 + ∑ i, |beta i|

/- Continuous functional `u ↦ beta·u`. -/
noncomputable def betaLinearMapHD {d : Nat} (beta : RealVec d) :
    RealVec d →L[Real] Real :=
  ∑ i, (beta i) •
    (ContinuousLinearMap.proj i : RealVec d →L[Real] Real)

/- Affine beta level hyperplane. -/
noncomputable def affineBetaHyperplaneHD {d : Nat}
    (beta : RealVec d) (hbeta : beta ≠ 0) (c : Real) :
    AffineSubspace Real (RealVec d) := by
  classical
  have hex : ∃ i, beta i ≠ 0 := by
    by_contra h
    push_neg at h
    apply hbeta
    funext i
    exact h i
  let i : Fin d := Classical.choose hex
  let u0 : RealVec d := fun k ↦ if k = i then c / beta i else 0
  exact AffineSubspace.mk' u0 (LinearMap.ker (betaLinearMapHD beta).toLinearMap)

/- Countable exceptional integer-pole locus. -/
def sineBadHD {d : Nat} (alpha beta : RealVec d) : Set (Torus d) :=
  {x | ∃ (j : IntVec d) (ell k : Int),
    (ell : Real) - rawPhaseHD beta j (uOrbitHD alpha x ell) = (k : Real)}

/- Explicit shifted-quadratic comparison constant. -/
def quadraticShiftConstantHD {d : Nat} (beta : RealVec d) : Real :=
  2 * (1 + (1 + poleShiftConstantHD beta) ^ 2)

/- Residue norm plus active indicator, divided by pole weight. -/
def poleWeightENNHD {d : Nat} {dataAlpha dataBeta : RealVec d}
    {S : Set (RealVec d)} {f : RealVec d → Complex}
    (data : PositiveInputDataHD dataAlpha dataBeta S f)
    (alpha beta : RealVec d) (x : Torus d) (a : IntVec d × Int) : ENNReal :=
  open Classical in
  (ENNReal.ofReal ‖residueCoordHD data alpha beta x a.1 a.2‖ +
      if residueCoordHD data alpha beta x a.1 a.2 ≠ 0 then 1 else 0) /
    ENNReal.ofReal (1 + (poleCoordHD alpha beta x a.1 a.2) ^ 2)

/- Exact proved raw shifted-sinc coefficient. -/
def sincShiftCoeffHD (k : Int) (t : Real) (q : Int) : Complex :=
  Theorem12.Generic.sincShiftCoeff k t q

/- Integer center chosen by floor. -/
def sincCenterIndex (t : Real) : Int :=
  ⌊t + 1 / 2⌋

/- Phase centered in `[-1/2,1/2)`. -/
def sincCenteredPhase (t : Real) : Real :=
  t - (sincCenterIndex t : Real)

/- Exact descended scalar-circle function. -/
def shiftedCenteredExpHD (k : Int) (t : Real) (y : AddCircle (1 : Real)) : Complex :=
  Theorem12.Generic.shiftedCenteredExp k t y

/- A fixed parameter with all preliminary analytic certificates. -/
structure AnalyticParameterHD {d : Nat} {alpha beta : RealVec d}
    {S : Set (RealVec d)} {f : RealVec d → Complex}
    (data : PositiveInputDataHD alpha beta S f) (x : Torus d) : Prop where
  offBad : x ∉ sineBadHD alpha beta
  poleInjective : Function.Injective
    (fun a : IntVec d × Int ↦ poleCoordHD alpha beta x a.1 a.2)
  poleWeightFinite :
    (∑' a : IntVec d × Int, poleWeightENNHD data alpha beta x a) < ∞

/- Subtype of actual nonzero residues. -/
def ActiveIndexHD {d : Nat} {alpha beta : RealVec d}
    {S : Set (RealVec d)} {f : RealVec d → Complex}
    (data : PositiveInputDataHD alpha beta S f) (x : Torus d) :=
  {a : IntVec d × Int // residueCoordHD data alpha beta x a.1 a.2 ≠ 0}

/- Set of distinct real pole locations. -/
def realPoleSetHD {d : Nat} {alpha beta : RealVec d}
    {S : Set (RealVec d)} {f : RealVec d → Complex}
    (data : PositiveInputDataHD alpha beta S f) (x : Torus d) : Set Real :=
  Set.range (fun a : ActiveIndexHD data x ↦
    poleCoordHD alpha beta x a.1.1 a.1.2)

/- Complex embeddings of the real poles. -/
def complexPoleSetHD {d : Nat} {alpha beta : RealVec d}
    {S : Set (RealVec d)} {f : RealVec d → Complex}
    (data : PositiveInputDataHD alpha beta S f) (x : Torus d) : Set Complex :=
  Complex.ofReal '' realPoleSetHD data x

/- Source regularized Cauchy kernel. -/
def regularizedKernelHD (p : Real) (z : Complex) : Complex :=
  1 / (z - (p : Complex)) + 1 / (p : Complex)

/- One active meromorphic summand. -/
def activeTermHD {d : Nat} {alpha beta : RealVec d}
    {S : Set (RealVec d)} {f : RealVec d → Complex}
    (data : PositiveInputDataHD alpha beta S f) (x : Torus d)
    (a : ActiveIndexHD data x) (z : Complex) : Complex :=
  residueCoordHD data alpha beta x a.1.1 a.1.2 *
    regularizedKernelHD (poleCoordHD alpha beta x a.1.1 a.1.2) z

/- Fixed-parameter active meromorphic series. -/
def activeMHD {d : Nat} {alpha beta : RealVec d}
    {S : Set (RealVec d)} {f : RealVec d → Complex}
    (data : PositiveInputDataHD alpha beta S f) (x : Torus d) (z : Complex) : Complex :=
  ∑' a : ActiveIndexHD data x, activeTermHD data x a z

/- Guarded fixed-index integer evaluator summand. -/
def intEvalSummandHD {P : Params} {S : Set (RealVec P.d)}
    {f : RealVec P.d → Complex}
    (data : PositiveInputDataHD P.alpha P.beta S f) (k : Int) (x : Torus P.d)
    (a : IntVec P.d × Int) : Complex := open Classical in
  if x ∈ sineBadHD P.alpha P.beta then 0
  else
    intParityHD (floorBetaDot P.beta a.1) *
      cubeSlice data a.1 (uCoordHD P.alpha P.beta x a.1 a.2) *
      sincShiftCoeffHD k (reducedPhaseHD P.alpha P.beta x a.1 a.2) a.2

/- Fixed-index evaluator before active-subtype restriction. -/
def intEvaluatorHD {P : Params} {S : Set (RealVec P.d)}
    {f : RealVec P.d → Complex}
    (data : PositiveInputDataHD P.alpha P.beta S f) (k : Int)
    (x : Torus P.d) : Complex :=
  ∑' a : IntVec P.d × Int, intEvalSummandHD data k x a

/- Floor-translated row phase. -/
def translatedPhaseHD {d : Nat} (beta : RealVec d) (j : IntVec d)
    (u : Torus d) : Real :=
  dotReal beta (torusToCubeHD u + intCast j) -
    (floorBetaDot beta j : Real)

/- Scalar-circle rotation represented by `n·alpha`. -/
def rotationPointHD {d : Nat} (alpha : RealVec d) (n : IntVec d) :
    AddCircle (1 : Real) :=
  (dotIntReal n alpha : AddCircle (1 : Real))

/- Exact translated row summand. -/
def translatedRowSummandHD {P : Params} {S : Set (RealVec P.d)}
    {f : RealVec P.d → Complex}
    (data : PositiveInputDataHD P.alpha P.beta S f) (k : Int) (n : IntVec P.d)
    (j : IntVec P.d) (q : Int) (u : Torus P.d) : Complex :=
  intEvalSummandHD data k
      (u + ellIndexHD P.beta j q • alphaTorusHD P.alpha) (j, q) *
    UnitAddTorus.mFourier n
      (u + ellIndexHD P.beta j q • alphaTorusHD P.alpha)

/- One row-good predicate controlling every signed q. -/
def rowGoodHD (P : Params) (j : IntVec P.d) (u : Torus P.d) : Prop :=
  ∀ q : Int, u + ellIndexHD P.beta j q • alphaTorusHD P.alpha ∉
    sineBadHD P.alpha P.beta

/- Literal good-branch shifted-sinc row term. -/
def rowSincSummandHD {P : Params} {S : Set (RealVec P.d)}
    {f : RealVec P.d → Complex}
    (data : PositiveInputDataHD P.alpha P.beta S f) (k : Int) (n : IntVec P.d)
    (j : IntVec P.d) (u : Torus P.d) (q : Int) : Complex :=
  let m := floorBetaDot P.beta j
  let t := translatedPhaseHD P.beta j u
  intParityHD m * cubeSlice data j u * sincShiftCoeffHD k t q *
    UnitAddTorus.mFourier n (u + (m + q) • alphaTorusHD P.alpha)

/- Exact four-factor collapsed row integrand. -/
def collapsedRowIntegrandHD {d : Nat} {alpha beta : RealVec d}
    {S : Set (RealVec d)} {f : RealVec d → Complex}
    (data : PositiveInputDataHD alpha beta S f) (k : Int) (n j : IntVec d)
    (u : Torus d) : Complex :=
  let m : Int := floorBetaDot beta j
  let t : Real := translatedPhaseHD beta j u
  intParityHD m * cubeSlice data j u *
    UnitAddTorus.mFourier n (u + m • alphaTorusHD alpha) *
    shiftedCenteredExpHD k t (rotationPointHD alpha n)

/- One common analytic/Fourier-good parameter. -/
structure FourierGoodParameterHD {P : Params} {S : Set (RealVec P.d)}
    {f : RealVec P.d → Complex}
    (data : PositiveInputDataHD P.alpha P.beta S f) (x : Torus P.d) : Prop where
  analytic : AnalyticParameterHD data x
  evaluatorZero : ∀ k : Int, intEvaluatorHD data k x = 0

/- Torus multiplicity observable in ENNReal. -/
def multiplicityENNHD {d : Nat} {alpha beta : RealVec d}
    {S : Set (RealVec d)} {f : RealVec d → Complex}
    (data : PositiveInputDataHD alpha beta S f) (y : Torus d) : ENNReal :=
  ∑' j : IntVec d,
    (cubeSliceSupport data j).indicator (fun _ ↦ (1 : ENNReal))
      (y - floorBetaDot beta j • alphaTorusHD alpha)

/- Real conversion of the multiplicity observable. -/
def multiplicityHD {d : Nat} {alpha beta : RealVec d}
    {S : Set (RealVec d)} {f : RealVec d → Complex}
    (data : PositiveInputDataHD alpha beta S f) (y : Torus d) : Real :=
  (multiplicityENNHD data y).toReal

/- Analytic and Birkhoff facts at the same torus point. -/
structure PoleAveragePointDataHD {P : Params} {S : Set (RealVec P.d)}
    {f : RealVec P.d → Complex}
    (data : PositiveInputDataHD P.alpha P.beta S f) (x : Torus P.d) : Prop where
  fourierGood : FourierGoodParameterHD data x
  orbitFinite : ∀ q : Int,
    multiplicityENNHD data (uOrbitHD P.alpha x q) < ∞
  averageTendsto : Tendsto
    (fun N : Nat ↦ (2 * (N : Real) + 1)⁻¹ *
      ∑ q ∈ Finset.Icc (-(N : Int)) (N : Int),
        multiplicityHD data (uOrbitHD P.alpha x q))
    atTop (nhds (supportMassHD data))

/- Closed symmetric real pole count. -/
def realPoleCountHD {d : Nat} {alpha beta : RealVec d}
    {S : Set (RealVec d)} {f : RealVec d → Complex}
    (data : PositiveInputDataHD alpha beta S f) (x : Torus d) (R : Real) : Nat :=
  Set.ncard (realPoleSetHD data x ∩ Set.Icc (-R) R)

/- Open complex-disk pole count. -/
def complexOpenPoleCountHD {d : Nat} {alpha beta : RealVec d}
    {S : Set (RealVec d)} {f : RealVec d → Complex}
    (data : PositiveInputDataHD alpha beta S f) (x : Torus d) (R : Real) : Nat :=
  Set.ncard (complexPoleSetHD data x ∩ Metric.ball 0 R)

/- One common point carrying every pre-Jensen conclusion. -/
structure PoleGoodParameterHD {P : Params} {S : Set (RealVec P.d)}
    {f : RealVec P.d → Complex}
    (data : PositiveInputDataHD P.alpha P.beta S f) (x : Torus P.d) : Prop where
  fourierGood : FourierGoodParameterHD data x
  orbitFinite : ∀ q : Int, multiplicityENNHD data (uOrbitHD P.alpha x q) < ∞
  realPoleDensity : Tendsto
    (fun R : Real ↦ (realPoleCountHD data x R : Real) / (2 * R))
    atTop (nhds (supportMassHD data))
  complexPoleDensity : Tendsto
    (fun R : Real ↦ (complexOpenPoleCountHD data x R : Real) / (2 * R))
    atTop (nhds (supportMassHD data))

/- Total logarithmic sine majorant. -/
def logSineMajorant (t : Real) : Real :=
  if Real.sin t = 0 then 0 else Real.log (1 + |Real.sin t|⁻¹)

/- Normalized positive-log circle mean. -/
def circlePosLogMeanHD (F : Complex → Complex) (R : Real) : Real :=
  (2 * Real.pi)⁻¹ *
    ∫ t in Set.Ioc (0 : Real) (2 * Real.pi),
      max (Real.log ‖F ((R : Complex) * Complex.exp (Complex.I * (t : Complex)))‖) 0

/- Exact origin-normalization ownership record. -/
structure OriginNormalizationDataHD {P : Params} {S : Set (RealVec P.d)}
    {f : RealVec P.d → Complex}
    (data : PositiveInputDataHD P.alpha P.beta S f) (x : Torus P.d) where
  nu : Nat
  nu_pos : 0 < nu
  baseCountingData : Theorem12.Generic.MeromorphicCountingData (activeMHD data x)
  normalizedM : Complex → Complex
  normalized_eq : ∀ z : Complex, z ≠ 0 →
    normalizedM z = activeMHD data x z / z ^ nu
  analyticAt_zero : AnalyticAt Complex normalizedM 0
  value_zero_ne : normalizedM 0 ≠ 0
  meromorphicOn_univ : MeromorphicOn normalizedM Set.univ
  countingData : Theorem12.Generic.MeromorphicCountingData normalizedM
  order_eq_away_zero : ∀ z : Complex, z ≠ 0 →
    countingData.order z = baseCountingData.order z
  poleMultiplicity_eq : ∀ z : Complex,
    Int.toNat (-countingData.order z) = Int.toNat (-baseCountingData.order z)

/- Clean radii for a normalized meromorphic function. -/
structure CleanRadiusDataHD (F : Complex → Complex) where
  R : Nat → Real
  bounds : ∀ m : Nat, (m : Real) + 1 < R m ∧ R m < (m : Real) + 2
  tendsto_R : Tendsto R atTop atTop
  clean : ∀ m : Nat, ∀ z : Complex, ‖z‖ = R m →
    AnalyticAt Complex F z ∧ F z ≠ 0

end Internal

end UniversalCompletenessHD
