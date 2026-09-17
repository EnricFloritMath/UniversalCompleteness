import Mathlib

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Topology ENNReal FourierTransform

namespace SpectralGapsPrelim.Theorem112

universe u

/-!
Definitions for the one-dimensional nonuniqueness theorem imported by the
higher-dimensional proof.
-/

structure AContext (A : Set ℝ) : Prop where
  measurable : MeasurableSet A
  subset_Icc : A ⊆ Set.Icc 0 1
  positive : 0 < volume A

structure AlphaLeHalf (alpha : ℝ) : Prop where
  nonneg : 0 ≤ alpha
  le_half : alpha ≤ (1 / 2 : ℝ)

def intTranslate (A : Set ℝ) (k : ℤ) : Set ℝ :=
  {xi | xi - (k : ℝ) ∈ A}

def spectrum (A : Set ℝ) : Set ℝ :=
  {xi | ∃ k : ℤ, xi ∈ intTranslate A k}

def exp2piI (u : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * u : ℝ) : ℂ) * Complex.I)

def PhiZeroExt (A : Set ℝ) (Phi : ℝ → ℂ) : ℝ → ℂ :=
  Set.indicator A Phi

def inverseFourierIntegral (P : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ xi : ℝ, exp2piI (xi * x) * P xi

structure FiniteSet (α : Type u) : Type (u + 1) where
  carrier : Set α
  finite : carrier.Finite

namespace FiniteSet

noncomputable def toFinset (F : FiniteSet α) : Finset α :=
  F.finite.toFinset

def ofFinset (s : Finset α) : FiniteSet α :=
  ⟨(s : Set α), s.finite_toSet⟩

def ofSet (s : Set α) (hs : s.Finite) : FiniteSet α :=
  ⟨s, hs⟩

def union (F G : FiniteSet α) : FiniteSet α :=
  ⟨F.carrier ∪ G.carrier, F.finite.union G.finite⟩

lemma mem_toFinset [DecidableEq α] {F : FiniteSet α} {x : α} :
    x ∈ F.toFinset ↔ x ∈ F.carrier := by
  classical
  exact F.finite.mem_toFinset

lemma coe_toFinset [DecidableEq α] (F : FiniteSet α) :
    (F.toFinset : Set α) = F.carrier := by
  classical
  ext x
  exact mem_toFinset

end FiniteSet

def integerObstructionSet (K : Set ℝ) (y : ℝ) : Set ℝ :=
  {d : ℝ | d ∈ Set.range (fun z : ℤ => (z : ℝ)) ∧ d + y ∈ K}

noncomputable def integerObstructionsOfFinite (K : Set ℝ) (y : ℝ)
    (hfinite : (integerObstructionSet K y).Finite) : FiniteSet ℝ :=
  ⟨integerObstructionSet K y, hfinite⟩

def sobolevPower (alpha xi : ℝ) : ℝ :=
  if alpha = 0 then 1 else |xi| ^ (2 * alpha)

def sobolevWeight (alpha xi : ℝ) : ℝ :=
  1 + sobolevPower alpha xi

def SupportedInSpectrumAE (A : Set ℝ) (P : ℝ → ℂ) : Prop :=
  ∀ᵐ xi ∂volume, xi ∉ spectrum A → P xi = 0

def WeightedEnergyIntegrable (alpha : ℝ) (A : Set ℝ) (P : ℝ → ℂ) : Prop :=
  Integrable
    (fun xi => sobolevWeight alpha xi * ‖P xi‖ ^ 2)
    (volume.restrict (spectrum A))

def weightedEnergy (alpha : ℝ) (A : Set ℝ) (P : ℝ → ℂ) : ℝ :=
  ∫ xi, sobolevWeight alpha xi * ‖P xi‖ ^ 2 ∂(volume.restrict (spectrum A))

def weightedNorm (alpha : ℝ) (A : Set ℝ) (P : ℝ → ℂ) : ℝ :=
  Real.sqrt (weightedEnergy alpha A P)

structure ContinuousInvFourierRep (P f : ℝ → ℂ) : Prop where
  memL2 : MemLp P 2 volume
  cont : Continuous f
  invPlancherel_ae :
    (𝓕⁻ (memL2.toLp P : Lp (α := ℝ) ℂ 2 volume) :
        Lp (α := ℝ) ℂ 2 volume) =ᵐ[volume] f

structure WeightedFourierWitness
    (alpha : ℝ) (A : Set ℝ) (f P : ℝ → ℂ) : Prop where
  supported : SupportedInSpectrumAE A P
  weightedIntegrable : WeightedEnergyIntegrable alpha A P
  invRep : ContinuousInvFourierRep P f

def WeightedPW (alpha : ℝ) (A : Set ℝ) (f : ℝ → ℂ) : Prop :=
  ∃ P : ℝ → ℂ, WeightedFourierWitness alpha A f P

def partialSum
    (g0 : ℝ → ℂ) (q : ℕ → ℝ → ℂ)
    (n : ℕ) (x : ℝ) : ℂ :=
  g0 x + (Finset.range n).sum (fun r => q r x)

abbrev «partial»
    (g0 : ℝ → ℂ) (q : ℕ → ℝ → ℂ)
    (n : ℕ) (x : ℝ) : ℂ :=
  partialSum g0 q n x

def partialFourier
    (G0 : ℝ → ℂ) (Q : ℕ → ℝ → ℂ)
    (n : ℕ) (xi : ℝ) : ℂ :=
  G0 xi + (Finset.range n).sum (fun r => Q r xi)

def weightedL2Tendsto
    (alpha : ℝ) (A : Set ℝ)
    (F : ℕ → ℝ → ℂ) (P : ℝ → ℂ) : Prop :=
  Tendsto
    (fun n => weightedNorm alpha A (fun xi => F n xi - P xi))
    atTop (nhds 0)

def weightedSeriesTendsto
    (alpha : ℝ) (A : Set ℝ)
    (G0 : ℝ → ℂ) (Q : ℕ → ℝ → ℂ)
    (H : ℝ → ℂ) : Prop :=
  weightedL2Tendsto alpha A (partialFourier G0 Q) H

def LocallyUniformLimit
    (F : ℕ → ℝ → ℂ) (f : ℝ → ℂ) : Prop :=
  ∀ K : Set ℝ, IsCompact K →
    ∀ eps : ℝ, 0 < eps →
      ∀ᶠ n in atTop, ∀ x ∈ K, dist (F n x) (f x) < eps

def UniformlyDiscrete (Lambda : Set ℝ) : Prop :=
  ∃ delta : ℝ, 0 < delta ∧
    ∀ ⦃x y : ℝ⦄,
      x ∈ Lambda → y ∈ Lambda → x ≠ y → delta ≤ dist x y

def a (alpha : ℝ) (k : ℕ) : ℝ :=
  (1 + (k : ℝ)) ^ (-(2 * alpha))

def B (alpha : ℝ) (N : ℕ) : ℝ :=
  (Finset.Icc 1 N).sum (fun k => a alpha k)

def c (alpha : ℝ) (N k : ℕ) : ℝ :=
  if k ∈ Finset.Icc 1 N then a alpha k / B alpha N else 0

def coeffPolynomial (N : ℕ) (b : ℕ → ℂ) (u : ℝ) : ℂ :=
  (Finset.Icc 1 N).sum (fun k => b k * exp2piI ((k : ℝ) * u))

def Q (alpha : ℝ) (N : ℕ) (u : ℝ) : ℂ :=
  coeffPolynomial N (fun k => (c alpha N k : ℂ)) u

noncomputable def previousZeroSet
    (x0 : ℝ) (lambda : ℕ → ℝ) (n : ℕ) : Finset ℝ := by
  classical
  exact ({x0} : Finset ℝ) ∪ (Finset.range n).image lambda

def correctionRadius (lambda : ℕ → ℝ) (n : ℕ) : ℝ :=
  min ((n : ℝ) + 1) (‖lambda n‖ / 2)

noncomputable def correctionCompact (lambda : ℕ → ℝ) (n : ℕ) : Set ℝ := by
  classical
  exact
    if lambda n = 0 then ∅
    else Set.Icc (-(correctionRadius lambda n)) (correctionRadius lambda n)

structure PeakSeed (A K : Set ℝ) (y : ℝ) (E : Finset ℝ) : Type 2 where
  hK : IsCompact K
  hyK : y ∉ K
  hE : ∀ e ∈ E, e ≠ y
  D : FiniteSet ℝ
  D_eq :
    D.carrier =
      ((fun e : ℝ => e - y) '' (E : Set ℝ)) ∪
        integerObstructionSet K y
  D_zero_not_mem : 0 ∉ D.carrier
  Phi : ℝ → ℂ
  Phi_aestronglyMeasurable :
    AEStronglyMeasurable Phi (volume.restrict A)
  Phi_memL2 : MemLp Phi 2 (volume.restrict A)
  Phi_integrable : Integrable Phi (volume.restrict A)
  Phi_moment_one :
    ∫ t, Phi t ∂volume.restrict A = 1
  Phi_moment_zero :
    ∀ d ∈ D.carrier,
      ∫ t, Phi t * exp2piI (d * t) ∂volume.restrict A = 0
  phi : ℝ → ℂ
  phi_def :
    ∀ u, phi u = ∫ t, Phi t * exp2piI (t * u) ∂volume.restrict A
  phi_cont : Continuous phi
  phi_zero : phi 0 = 1
  phi_vanish_E : ∀ e ∈ E, phi (e - y) = 0
  phi_vanish_K_int :
    ∀ z : ℤ, (z : ℝ) + y ∈ K → phi (z : ℝ) = 0

structure PeakCandidate
    (A K : Set ℝ) (y : ℝ) (E : Finset ℝ)
    (seed : PeakSeed A K y E)
    (N : ℕ) (b : ℕ → ℂ) : Type 2 where
  hN : 1 ≤ N
  sum_b : (Finset.Icc 1 N).sum b = 1
  P : ℝ → ℂ
  p : ℝ → ℂ
  P_def :
    ∀ xi,
      P xi =
        exp2piI (-(y * xi)) *
          (Finset.Icc 1 N).sum
            (fun k => b k * PhiZeroExt A seed.Phi (xi - (k : ℝ)))
  p_def :
    ∀ x,
      p x =
        seed.phi (x - y) *
          coeffPolynomial N b (x - y)
  P_integrable : Integrable P volume
  P_memL2 : MemLp P 2 volume
  P_supported : SupportedInSpectrumAE A P
  p_cont : Continuous p
  invRep : ContinuousInvFourierRep P p
  p_y : p y = 1
  p_zero_E : ∀ e ∈ E, p e = 0

abbrev PosNat := {N : ℕ // 1 ≤ N}

end SpectralGapsPrelim.Theorem112
