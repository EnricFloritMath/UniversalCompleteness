import Mathlib

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Topology ENNReal FourierTransform

namespace SpectralGapsPrelim.HigherDim

/-!
Definitions for the higher-dimensional nonuniqueness theorem. Other proof
modules import these shared geometric and Fourier-space objects.
-/

abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

noncomputable def toE {d : ℕ} (x : Fin d → ℝ) : E d :=
  WithLp.toLp 2 x

noncomputable def coord {d : ℕ} (x : E d) (i : Fin d) : ℝ :=
  WithLp.ofLp x i

noncomputable def coordinateVector {d : ℕ} (i : Fin d) : E d :=
  toE fun j => if j = i then 1 else 0

noncomputable def firstCoordinateVector {d : ℕ} (hd_pos : 0 < d) : E d :=
  coordinateVector ⟨0, hd_pos⟩

def lineFibre {d : ℕ} (A : Set (E d)) (w v : E d) : Set ℝ :=
  {s | w + s • v ∈ A}

noncomputable def intVec {d : ℕ} (k : Fin d → ℤ) : E d :=
  toE fun i => (k i : ℝ)

noncomputable def natVec {d : ℕ} (k : Fin d → ℕ) : E d :=
  toE fun i => (k i : ℝ)

def integerLattice (d : ℕ) : Set (E d) :=
  Set.range (intVec : (Fin d → ℤ) → E d)

def unitCube (d : ℕ) : Set (E d) :=
  {x | ∀ i : Fin d, 0 ≤ coord x i ∧ coord x i ≤ 1}

structure AContextHD (d : ℕ) (A : Set (E d)) : Prop where
  measurable : MeasurableSet A
  subset_unitCube : A ⊆ unitCube d
  positive : 0 < volume A

structure AlphaLeDimHalf (d : ℕ) (alpha : ℝ) : Prop where
  nonneg : 0 ≤ alpha
  le_dim : 2 * alpha ≤ (d : ℝ)

def latticeTranslate {d : ℕ} (A : Set (E d)) (k : Fin d → ℤ) : Set (E d) :=
  {xi | xi - intVec k ∈ A}

def spectrum {d : ℕ} (A : Set (E d)) : Set (E d) :=
  {xi | ∃ k : Fin d → ℤ, xi ∈ latticeTranslate A k}

def exp2piI (u : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * u : ℝ) : ℂ) * Complex.I)

def fourierChar {d : ℕ} (xi x : E d) : ℂ :=
  exp2piI (inner ℝ xi x)

def PhiZeroExt {d : ℕ} (A : Set (E d)) (Phi : E d → ℂ) : E d → ℂ :=
  Set.indicator A Phi

def inverseFourierIntegral {d : ℕ} (P : E d → ℂ) (x : E d) : ℂ :=
  ∫ xi : E d, fourierChar xi x * P xi

def momentFunctional {d : ℕ} (A : Set (E d)) (h : E d) (Phi : E d → ℂ) : ℂ :=
  ∫ t, Phi t * exp2piI (inner ℝ h t) ∂(volume.restrict A)

def sobolevPower {d : ℕ} (alpha : ℝ) (xi : E d) : ℝ :=
  if alpha = 0 then 1 else Real.rpow ‖xi‖ (2 * alpha)

def sobolevWeight {d : ℕ} (alpha : ℝ) (xi : E d) : ℝ :=
  1 + sobolevPower alpha xi

def SupportedInSpectrumAE {d : ℕ} (A : Set (E d)) (P : E d → ℂ) : Prop :=
  ∀ᵐ xi ∂volume, xi ∉ spectrum A → P xi = 0

def weightedMeasure {d : ℕ} (alpha : ℝ) (A : Set (E d)) : Measure (E d) :=
  (volume.restrict (spectrum A)).withDensity
    (fun xi => ENNReal.ofReal (sobolevWeight alpha xi))

def WeightedEnergyIntegrable {d : ℕ}
    (alpha : ℝ) (A : Set (E d)) (P : E d → ℂ) : Prop :=
  MemLp P 2 (weightedMeasure alpha A)

def weightedEnergy {d : ℕ}
    (alpha : ℝ) (A : Set (E d)) (P : E d → ℂ) : ℝ :=
  (eLpNorm P 2 (weightedMeasure alpha A)).toReal ^ 2

def weightedNorm {d : ℕ}
    (alpha : ℝ) (A : Set (E d)) (P : E d → ℂ) : ℝ :=
  (eLpNorm P 2 (weightedMeasure alpha A)).toReal

def weightedL2Fun {d : ℕ} (alpha : ℝ) (P : E d → ℂ) : E d → ℂ :=
  fun xi => (Real.sqrt (sobolevWeight alpha xi) : ℂ) * P xi

structure ContinuousInvFourierRep {d : ℕ} (P f : E d → ℂ) : Prop where
  P_memL2 : MemLp P 2 volume
  f_memL2 : MemLp f 2 volume
  f_cont : Continuous f
  inv_eq_l2 :
    (𝓕⁻ (P_memL2.toLp P) : Lp (α := E d) ℂ 2 volume) =
      f_memL2.toLp f

structure WeightedFourierSide {d : ℕ}
    (alpha : ℝ) (A : Set (E d)) (P : E d → ℂ) : Prop where
  aestronglyMeasurable : AEStronglyMeasurable P volume
  supported : SupportedInSpectrumAE A P
  weightedMemLp : MemLp P 2 (weightedMeasure alpha A)
  memL2 : MemLp P 2 volume

structure WeightedFourierWitness {d : ℕ}
    (alpha : ℝ) (A : Set (E d)) (f P : E d → ℂ) : Prop where
  side : WeightedFourierSide alpha A P
  invRep : ContinuousInvFourierRep P f

def WeightedPW {d : ℕ} (alpha : ℝ) (A : Set (E d)) (f : E d → ℂ) : Prop :=
  ∃ P : E d → ℂ, WeightedFourierWitness alpha A f P

def UniformlyDiscrete {d : ℕ} (Lambda : Set (E d)) : Prop :=
  ∃ delta : ℝ, 0 < delta ∧
    ∀ x ∈ Lambda, ∀ y ∈ Lambda, x ≠ y → delta ≤ dist x y

def latticeObstructionSet {d : ℕ} (K : Set (E d)) (y : E d) : Set (E d) :=
  {h | h ∈ integerLattice d ∧ h + y ∈ K}

def partialSum {d : ℕ}
    (g0 : E d → ℂ) (q : ℕ → E d → ℂ) (n : ℕ) (x : E d) : ℂ :=
  g0 x + (Finset.range n).sum (fun r => q r x)

def partialFourier {d : ℕ}
    (G0 : E d → ℂ) (Q : ℕ → E d → ℂ) (n : ℕ) (xi : E d) : ℂ :=
  G0 xi + (Finset.range n).sum (fun r => Q r xi)

def weightedL2Tendsto {d : ℕ}
    (alpha : ℝ) (A : Set (E d))
    (F : ℕ → E d → ℂ) (P : E d → ℂ) : Prop :=
  Tendsto
    (fun n => eLpNorm (fun xi => F n xi - P xi) 2 (weightedMeasure alpha A))
    atTop (nhds 0)

def weightedSeriesTendsto {d : ℕ}
    (alpha : ℝ) (A : Set (E d))
    (G0 : E d → ℂ) (Q : ℕ → E d → ℂ) (H : E d → ℂ) : Prop :=
  weightedL2Tendsto alpha A (partialFourier G0 Q) H

def LocallyUniformLimit {d : ℕ}
    (F : ℕ → E d → ℂ) (f : E d → ℂ) : Prop :=
  ∀ K : Set (E d), IsCompact K →
    ∀ eps : ℝ, 0 < eps →
      ∀ᶠ n in atTop, ∀ x ∈ K, dist (F n x) (f x) < eps

abbrev PosNat := {N : ℕ // 1 ≤ N}

def indexBox (d N : ℕ) : Finset (Fin d → ℕ) :=
  Fintype.piFinset fun _ : Fin d => Finset.Icc 1 N

def a {d : ℕ} (alpha : ℝ) (k : Fin d → ℕ) : ℝ :=
  1 / sobolevWeight alpha (natVec k)

def B (d : ℕ) (alpha : ℝ) (N : ℕ) : ℝ :=
  (indexBox d N).sum (fun k => a alpha k)

def c {d : ℕ} (alpha : ℝ) (N : ℕ) (k : Fin d → ℕ) : ℝ :=
  if k ∈ indexBox d N then a alpha k / B d alpha N else 0

def coeffPolynomial {d : ℕ}
    (N : ℕ) (b : (Fin d → ℕ) → ℂ) (u : E d) : ℂ :=
  (indexBox d N).sum
    (fun k => b k * exp2piI (inner ℝ (natVec k) u))

def Q {d : ℕ} (alpha : ℝ) (N : ℕ) (u : E d) : ℂ :=
  coeffPolynomial N (fun k => (c alpha N k : ℂ)) u

def firstCoordinateSliceWeightSum {d : ℕ}
    (hd_pos : 0 < d) (alpha : ℝ) (N : ℕ) : ℝ :=
  ((indexBox d N).filter (fun k => k ⟨0, hd_pos⟩ = 1)).sum
    (fun k => 1 / sobolevWeight alpha (natVec k))

def correctionRadius {d : ℕ} (lambda : ℕ → E d) (n : ℕ) : ℝ :=
  min ((n : ℝ) + 1) (‖lambda n‖ / 2)

def correctionCompact {d : ℕ} (lambda : ℕ → E d) (n : ℕ) : Set (E d) :=
  if lambda n = 0 then ∅
  else Metric.closedBall (0 : E d) (correctionRadius lambda n)

structure PeakSeed {d : ℕ}
    (A K : Set (E d)) (y : E d) (E0 : Finset (E d)) : Type where
  hK : IsCompact K
  hyK : y ∉ K
  hE : ∀ e ∈ E0, e ≠ y
  D : Finset (E d)
  D_mem :
    ∀ h,
      h ∈ D ↔
        h ∈ ((fun e : E d => e - y) '' (E0 : Set (E d))) ∪
          latticeObstructionSet K y
  D_zero_not_mem : 0 ∉ D
  Phi : E d → ℂ
  Phi_aestronglyMeasurable :
    AEStronglyMeasurable Phi (volume.restrict A)
  Phi_memL2 : MemLp Phi 2 (volume.restrict A)
  Phi_integrable : Integrable Phi (volume.restrict A)
  Phi_moment_one :
    (∫ t, Phi t ∂(volume.restrict A)) = 1
  Phi_moment_zero :
    ∀ h ∈ D,
      (∫ t, Phi t * exp2piI (inner ℝ h t) ∂(volume.restrict A)) = 0
  phi : E d → ℂ
  phi_def :
    ∀ u,
      phi u =
        ∫ t, Phi t * exp2piI (inner ℝ t u) ∂(volume.restrict A)
  phi_cont : Continuous phi
  phi_zero : phi 0 = 1
  phi_vanish_E : ∀ e ∈ E0, phi (e - y) = 0
  phi_vanish_K_lattice :
    ∀ z : Fin d → ℤ, intVec z + y ∈ K → phi (intVec z) = 0

noncomputable def candidateP {d : ℕ}
    (A : Set (E d)) {K : Set (E d)} {y : E d} {E0 : Finset (E d)}
    (seed : PeakSeed A K y E0)
    (N : ℕ) (b : (Fin d → ℕ) → ℂ) : E d → ℂ :=
  fun xi =>
    exp2piI (-(inner ℝ y xi)) *
      (indexBox d N).sum
        (fun k => b k * PhiZeroExt A seed.Phi (xi - natVec k))

noncomputable def candidatep {d : ℕ}
    {A K : Set (E d)} {y : E d} {E0 : Finset (E d)}
    (seed : PeakSeed A K y E0)
    (N : ℕ) (b : (Fin d → ℕ) → ℂ) : E d → ℂ :=
  fun x => seed.phi (x - y) * coeffPolynomial N b (x - y)

structure PeakCandidate {d : ℕ}
    (A K : Set (E d)) (y : E d) (E0 : Finset (E d))
    (seed : PeakSeed A K y E0)
    (N : ℕ) (b : (Fin d → ℕ) → ℂ) : Type where
  hN : 1 ≤ N
  sum_b : (indexBox d N).sum b = 1
  P_integrable : Integrable (candidateP A seed N b) volume
  P_memL2 : MemLp (candidateP A seed N b) 2 volume
  P_supported : SupportedInSpectrumAE A (candidateP A seed N b)
  p_cont : Continuous (candidatep seed N b)
  p_y : candidatep seed N b y = 1
  p_zero_E : ∀ e ∈ E0, candidatep seed N b e = 0

end SpectralGapsPrelim.HigherDim
