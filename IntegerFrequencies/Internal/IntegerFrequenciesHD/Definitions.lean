import Mathlib.Analysis.Fourier.AddCircleMulti
import Theorem14.Definitions

/-!
# Higher-dimensional integer-frequency definitions

Transparent definitions and proposition-valued structures are centralized
in this file.  In particular, this file fixes the coordinate
models, the normalized product-Haar measure convention, the cube/torus representative,
the rectangular counting convention, and the signs of every Fourier character.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace IntegerFrequenciesHD

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

local instance : Measure.IsAddHaarMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs
    (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs
    (IsProbabilityMeasure AddCircle.haarAddCircle)

/- Integer-real coordinate pairing. -/
def dotIntReal {d : Nat} (n : IntVec d) (alpha : RealVec d) : Real :=
  ∑ i, (n i : Real) * alpha i

/- Rational independence of one and all coordinates. -/
def RationallyIndependentWithOne {d : Nat} (alpha : RealVec d) : Prop :=
  ∀ (q0 : Rat) (q : Fin d → Rat),
    (q0 : Real) + ∑ i, (q i : Real) * alpha i = 0 →
      q0 = 0 ∧ ∀ i, q i = 0

/- Selected frequencies use the half-open interval `Ico (1-v) 1`. -/
def integerFrequencySetHD {d : Nat} (alpha : RealVec d) (v : Real) : Set (IntVec d) :=
  {n | Int.fract (dotIntReal n alpha) ∈ Set.Ico (1 - v) 1}

/- Half-open translated real cube. -/
def realCube {d : Nat} (y : RealVec d) (R : Real) : Set (RealVec d) :=
  {x | ∀ i, y i ≤ x i ∧ x i < y i + R}

/- Finite-cardinality count in a translated cube. -/
def cubeCount {d : Nat} (Lambda : Set (IntVec d)) (y : RealVec d) (R : Real) : Nat :=
  Set.ncard {n : IntVec d |
    n ∈ Lambda ∧ (fun i ↦ (n i : Real)) ∈ realCube y R}

/- Quantitative uniform cubical density. -/
structure HasUniformCubicalDensity {d : Nat}
    (Lambda : Set (IntVec d)) (D : Real) : Prop where
  finite_count : ∀ (y : RealVec d) (R : Real), 0 ≤ R →
    Set.Finite {n : IntVec d |
      n ∈ Lambda ∧ (fun i ↦ (n i : Real)) ∈ realCube y R}
  uniform_error : ∀ epsilon : Real, 0 < epsilon →
    ∃ R0 : Real, 0 < R0 ∧ ∀ R : Real, R0 ≤ R →
      ∀ y : RealVec d,
        |(cubeCount Lambda y R : Real) - D * R ^ d| ≤ epsilon * R ^ d

/- Positive Fourier character. -/
def fourierCharHD {d : Nat} (xi x : RealVec d) : Complex :=
  Complex.exp
    (((2 * Real.pi : Real) : Complex) * Complex.I *
      ((∑ i, xi i * x i : Real) : Complex))

/- Article sample with the negative/conjugated Fourier sign. -/
def fourierSampleOnHD {d : Nat} (S : Set (RealVec d))
    (f : RealVec d → Complex) (xi : RealVec d) : Complex :=
  ∫ x in S, f x * starRingEnd Complex (fourierCharHD xi x)

/- Universal `L1` uniqueness below density `v`. -/
def UniversalL1UniquenessBelowHD {d : Nat}
    (Lambda : Set (IntVec d)) (v : Real) : Prop :=
  ∀ (S : Set (RealVec d)), MeasurableSet S →
    S ⊆ {x | ∀ i, x i ∈ Set.Icc (0 : Real) 1} →
    volume S < ENNReal.ofReal v →
      ∀ (f : RealVec d → Complex), Integrable f (volume.restrict S) →
        (∀ n ∈ Lambda,
          fourierSampleOnHD S f (fun i ↦ (n i : Real)) = 0) →
          f =ᵐ[volume.restrict S] (fun _ ↦ 0)

namespace Internal

/- A product character belongs to every finite-measure
restricted `Lp` space for `1 ≤ p`. -/
theorem memLp_fourierCharHD_restrict {d : Nat}
    (S : Set (RealVec d)) (hSmeas : MeasurableSet S)
    (hSfinite : volume S ≠ ∞)
    (p : ENNReal) (hp : 1 ≤ p) (n : IntVec d) :
    MemLp (fun x => fourierCharHD (fun i => (n i : Real)) x)
      p (volume.restrict S) := by
  letI : IsFiniteMeasure (volume.restrict S) :=
    ⟨by
      simpa [Measure.restrict_apply_univ, hSmeas] using
        (lt_top_iff_ne_top.mpr hSfinite)⟩
  apply MemLp.of_bound (C := 1)
  · apply Continuous.aestronglyMeasurable
    unfold fourierCharHD
    fun_prop
  · filter_upwards with x
    rw [fourierCharHD, Complex.norm_exp]
    simp

end Internal

/- The positive character atom in restricted `Lp`. -/
def exponentialLpHD {d : Nat}
    (S : Set (RealVec d)) (hSmeas : MeasurableSet S)
    (p : ENNReal) (hp : 1 ≤ p) (hSfinite : volume S ≠ ∞)
    (n : IntVec d) : Lp Complex p (volume.restrict S) := by
  letI : Fact (1 ≤ p) := ⟨hp⟩
  exact (Internal.memLp_fourierCharHD_restrict
    S hSmeas hSfinite p hp n).toLp
      (fun x => fourierCharHD (fun i => (n i : Real)) x)

/- Closed-span completeness of the selected exponentials. -/
def ExponentialCompleteInLpHD {d : Nat}
    (Lambda : Set (IntVec d)) (S : Set (RealVec d))
    (hSmeas : MeasurableSet S) (p : ENNReal) (hp : 1 ≤ p)
    (hSfinite : volume S ≠ ∞) : Prop := by
  letI : Fact (1 ≤ p) := ⟨hp⟩
  letI : IsFiniteMeasure (volume.restrict S) :=
    isFiniteMeasure_restrict.mpr hSfinite
  exact Dense (↑(Submodule.span Complex
    (Set.range (fun n : {n : IntVec d // n ∈ Lambda} ↦
      exponentialLpHD S hSmeas p hp hSfinite n.1))) :
        Set (Lp Complex p (volume.restrict S)))

/- Bundled density, `L1`, and finite-`Lp` conclusions. -/
structure IntegerFrequenciesHDConclusion
    (d : Nat) (alpha : RealVec d) (v : Real) : Prop where
  density : HasUniformCubicalDensity (integerFrequencySetHD alpha v) v
  universalL1 :
    UniversalL1UniquenessBelowHD (integerFrequencySetHD alpha v) v
  completeLp : ∀ (S : Set (RealVec d)) (hSmeas : MeasurableSet S)
    (hSsub : S ⊆ {x | ∀ i, x i ∈ Set.Icc (0 : Real) 1})
    (hSlt : volume S < ENNReal.ofReal v)
    (p : ENNReal) (hp : 1 ≤ p) (hpTop : p ≠ ∞),
      ExponentialCompleteInLpHD (integerFrequencySetHD alpha v)
        S hSmeas p hp (ne_of_lt (lt_of_lt_of_le hSlt le_top))

/- Closed article unit cube. -/
def unitCubeHD (d : Nat) : Set (RealVec d) :=
  {x | ∀ i, x i ∈ Set.Icc (0 : Real) 1}

namespace Internal

/- Native `(0,1]^d` representative; `0 + 1` is elaborational. -/
def iocUnitCubeHD (d : Nat) : Set (RealVec d) :=
  {x | ∀ i, x i ∈ Set.Ioc (0 : Real) (0 + 1)}

/- Native measurable equivalence with the Ioc representative. -/
noncomputable def torusIocEquivHD (d : Nat) :
    Torus d ≃ᵐ {x : RealVec d // x ∈ iocUnitCubeHD d} := by
  exact UnitAddTorus.measurableEquivPiIoc (fun _ : Fin d ↦ (0 : Real))

/- Chosen cube representative of a torus point. -/
def torusToCubeHD {d : Nat} (z : Torus d) : RealVec d :=
  (torusIocEquivHD d z).1

/- Coordinate quotient map from the cube to the torus. -/
def cubeToTorusHD {d : Nat} (x : RealVec d) : Torus d :=
  fun i ↦ (x i : UnitAddCircle)

/- Carrier normalized to the native Ioc representative. -/
def normalizedCarrierHD {d : Nat} (S : Set (RealVec d)) : Set (RealVec d) :=
  S ∩ iocUnitCubeHD d

/- Zero extension of the normalized carrier. -/
def zeroExtensionHD {d : Nat} (S : Set (RealVec d))
    (f : RealVec d → Complex) : RealVec d → Complex :=
  (normalizedCarrierHD S).indicator f

/- Raw representative transported to the torus. -/
def torusRepresentativeHD {d : Nat} (S : Set (RealVec d))
    (f : RealVec d → Complex) (z : Torus d) : Complex :=
  zeroExtensionHD S f (torusToCubeHD z)

/- Torus carrier of the normalized set. -/
def torusCarrierHD {d : Nat} (S : Set (RealVec d)) : Set (Torus d) :=
  torusToCubeHD ⁻¹' normalizedCarrierHD S

/- Natural multi-index rectangle. -/
def natIndexRectangle {d : Nat}
    (N : Fin d → Nat) : Finset (Fin d → Nat) :=
  Fintype.piFinset (fun i ↦ Finset.range (N i))

/- Selected interval count over a natural rectangle. -/
noncomputable def rectangularIntervalCount {d : Nat}
    (alpha : RealVec d) (a b : Real) (N : Fin d → Nat) (x : Real) : Nat := by
  classical
  exact ((natIndexRectangle N).filter fun k ↦
    Int.fract (x + ∑ i, (k i : Real) * alpha i) ∈ Set.Ico a b).card

/- Canonical coordinate selected from `0 < d`. -/
def firstCoordinate {d : Nat} (hd : 0 < d) : Fin d :=
  ⟨0, hd⟩

/- Integer origin of the lattice rectangle. -/
def latticeRectangleOrigin {d : Nat} (y : RealVec d) : IntVec d :=
  fun i ↦ Int.ceil (y i)

/- Coordinate side lengths of the lattice rectangle. -/
def latticeRectangleSide {d : Nat} (y : RealVec d) (R : Real) : Fin d → Nat :=
  fun i ↦ Int.toNat (Int.ceil (y i + R) - Int.ceil (y i))

/- Exact reindexing of integer cube points by a natural rectangle. -/
noncomputable def intVecRealCubeEquivNatIndexRectangle {d : Nat}
    (y : RealVec d) (R : Real) (hR : 0 ≤ R) :
    {n : IntVec d // (fun i ↦ (n i : Real)) ∈ realCube y R} ≃
      {k : Fin d → Nat // k ∈ natIndexRectangle (latticeRectangleSide y R)} := by
  classical
  let M : IntVec d := latticeRectangleOrigin y
  let K : Fin d → Nat := latticeRectangleSide y R
  have hdiff (i : Fin d) : 0 ≤ Int.ceil (y i + R) - Int.ceil (y i) := by
    exact sub_nonneg.mpr (Int.ceil_mono (by linarith))
  refine
    { toFun := fun n ↦ ⟨fun i ↦ Int.toNat (n.1 i - M i), ?_⟩
      invFun := fun k ↦ ⟨fun i ↦ M i + (k.1 i : Int), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · simp only [natIndexRectangle, Fintype.mem_piFinset, Finset.mem_range]
    intro i
    have hn := n.2 i
    have hnM : M i ≤ n.1 i := by
      dsimp [M, latticeRectangleOrigin]
      exact Int.ceil_le.mpr hn.1
    have hnU : n.1 i < Int.ceil (y i + R) := by
      exact (Int.lt_ceil).mpr hn.2
    rw [latticeRectangleSide, Int.toNat_lt (sub_nonneg.mpr hnM)]
    rw [Int.toNat_of_nonneg (hdiff i)]
    dsimp [M, latticeRectangleOrigin] at hnM ⊢
    omega
  · intro i
    have hk : k.1 i < latticeRectangleSide y R i :=
      Finset.mem_range.mp (Fintype.mem_piFinset.mp
        (show k.1 ∈ Fintype.piFinset
          (fun j ↦ Finset.range (latticeRectangleSide y R j)) from k.2) i)
    have hKint : (latticeRectangleSide y R i : Int) =
        Int.ceil (y i + R) - Int.ceil (y i) := by
      dsimp [latticeRectangleSide]
      exact Int.toNat_of_nonneg (hdiff i)
    have hkInt : (k.1 i : Int) < (latticeRectangleSide y R i : Int) := by
      exact_mod_cast hk
    constructor
    · apply Int.ceil_le.mp
      dsimp [M, latticeRectangleOrigin]
      omega
    · apply Int.lt_ceil.mp
      dsimp [M, latticeRectangleOrigin]
      omega
  · intro n
    apply Subtype.ext
    funext i
    have hn := n.2 i
    have hnM : M i ≤ n.1 i := by
      dsimp [M, latticeRectangleOrigin]
      exact Int.ceil_le.mpr hn.1
    change M i + (Int.toNat (n.1 i - M i) : Int) = n.1 i
    rw [Int.toNat_of_nonneg (sub_nonneg.mpr hnM)]
    omega
  · intro k
    apply Subtype.ext
    funext i
    have hk : k.1 i < latticeRectangleSide y R i :=
      Finset.mem_range.mp (Fintype.mem_piFinset.mp
        (show k.1 ∈ Fintype.piFinset
          (fun j ↦ Finset.range (latticeRectangleSide y R j)) from k.2) i)
    change Int.toNat ((M i + (k.1 i : Int)) - M i) = k.1 i
    have hnonneg : 0 ≤ (M i + (k.1 i : Int)) - M i := by omega
    have hsimp : (M i + (k.1 i : Int)) - M i = (k.1 i : Int) := by omega
    simp only [hsimp, Int.toNat_natCast]

/- Translation element determined by `alpha`. -/
def alphaTorus {d : Nat} (alpha : RealVec d) : Torus d :=
  fun i ↦ (alpha i : UnitAddCircle)

/- Product frequency box with coordinate bounds `|n_i| ≤ N`. -/
noncomputable def multiIndexBox (d N : Nat) : Finset (IntVec d) := by
  exact Fintype.piFinset (fun _ : Fin d ↦ Finset.Icc (-(N : Int)) (N : Int))

/- Tensor product Fejer multiplier. -/
def productFejerMultiplier {d : Nat} (N : Nat) (n : IntVec d) : Real :=
  ∏ i, Theorem14.Internal.fejerMultiplier N (n i)

/- Finite product Fejer mean. -/
noncomputable def productFejerMean {d : Nat} (N : Nat)
    (F : Torus d → Complex) : C(Torus d, Complex) :=
  ∑ n ∈ multiIndexBox d N,
    ((productFejerMultiplier N n : Complex) *
      UnitAddTorus.mFourierCoeff F n) •
        (UnitAddTorus.mFourier n : C(Torus d, Complex))

/- Tensor product Fejer kernel. -/
def productFejerKernel {d : Nat} (N : Nat) (x : Torus d) : Real :=
  ∏ i, Theorem14.Internal.fejerKernel N (x i)

/- Product convolution uses the orientation `x - y`. -/
noncomputable def productFejerConvolution {d : Nat} (N : Nat)
    (F : Torus d → Complex) (x : Torus d) : Complex :=
  ∫ y, (productFejerKernel N y : Complex) * F (x - y)

/- A summably convergent subsequence of product Fejer means. -/
structure ProductFejerApproximation {d : Nat} (F : Torus d → Complex) where
  index : Nat → Nat
  summable_error : Summable (fun j ↦
    ∫ x, ‖productFejerMean (index j) F x - F x‖)

/- Windowed coefficient along the minus orbit. -/
def weightedOrbitCoeffHD {d : Nat} (epsilon : Real) (alpha : RealVec d)
    (F : Torus d → Complex) (x : Torus d) (k : Int) : Complex :=
  Theorem14.Internal.windowCoeff epsilon k *
    F (x - k • alphaTorus alpha)

/- Nonnegative extended-real mass of the orbit coefficients. -/
def weightedOrbitENNRealMassHD {d : Nat} (epsilon : Real)
    (alpha : RealVec d) (F : Torus d → Complex) (x : Torus d) : ENNReal :=
  ∑' k : Int, (‖weightedOrbitCoeffHD epsilon alpha F x k‖₊ : ENNReal)

/- Pointwise package of all weighted norm-summability facts. -/
structure WeightedApproximationAtHD {d : Nat} (epsilon : Real)
    (alpha : RealVec d) (F : Torus d → Complex)
    (A : ProductFejerApproximation F) (x : Torus d) : Prop where
  targetSummable : Summable (fun k : Int ↦
    ‖weightedOrbitCoeffHD epsilon alpha F x k‖)
  stageSummable : ∀ j, Summable (fun k : Int ↦
    ‖weightedOrbitCoeffHD epsilon alpha
      (productFejerMean (A.index j) F) x k‖)
  errorSummable : ∀ j, Summable (fun k : Int ↦
    ‖weightedOrbitCoeffHD epsilon alpha
      (fun y ↦ productFejerMean (A.index j) F y - F y) x k‖)
  summable_errorNorm : Summable (fun j ↦ ∑' k : Int,
    ‖weightedOrbitCoeffHD epsilon alpha
      (fun y ↦ productFejerMean (A.index j) F y - F y) x k‖)

/- Fourier synthesis with the positive translated-window phase. -/
noncomputable def broadenedFunctionHD {d : Nat} (epsilon : Real)
    (alpha : RealVec d) (F : Torus d → Complex) (x : Torus d) :
    C(AddCircle (1 : Real), Complex) :=
  Theorem14.Internal.fourierSynthesis
    (weightedOrbitCoeffHD epsilon alpha F x)

/- Coefficient and support data for the broadened function. -/
structure BroadeningDataHD {d : Nat} (epsilon : Real)
    (alpha : RealVec d) (v : Real) (F : Torus d → Complex)
    (x : Torus d) : Prop where
  coeffSummable : Summable (fun k : Int ↦
    ‖weightedOrbitCoeffHD epsilon alpha F x k‖)
  coeff_eq : ∀ k : Int,
    fourierCoeff (broadenedFunctionHD epsilon alpha F x) k =
      weightedOrbitCoeffHD epsilon alpha F x k
  supported : Theorem14.Internal.SupportedInInitialArc
    (broadenedFunctionHD epsilon alpha F x) (1 - v + epsilon)

/- Deterministic broadening width below the density threshold. -/
def broadeningWidthHD {d : Nat} (v : Real) (S : Set (RealVec d)) : Real :=
  (v - (volume S).toReal) / 2

end Internal

end IntegerFrequenciesHD
