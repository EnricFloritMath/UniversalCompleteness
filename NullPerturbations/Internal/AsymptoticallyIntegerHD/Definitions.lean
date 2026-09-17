import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Foundational definitions for higher-dimensional asymptotically integer frequencies

This module contains the foundational definitions and supporting theorems
for higher-dimensional asymptotically integer frequencies.
-/

noncomputable section

open Filter MeasureTheory Set Topology
open scoped BigOperators ComplexConjugate ENNReal

namespace AsymptoticallyIntegerHD

/-- Coordinate model of `R^d`; its Pi norm is the sup norm. -/
abbrev RealVec (d : Nat) := Fin d → Real

/-- Coordinate model of `Z^d`. -/
abbrev IntVec (d : Nat) := Fin d → Int

/-- The sole coordinatewise integer embedding. -/
def integerEmbed {d : Nat} (n : IntVec d) : RealVec d :=
  fun i ↦ (n i : Real)

@[simp]
theorem integerEmbed_apply {d : Nat} (n : IntVec d) (i : Fin d) :
    integerEmbed n i = (n i : Real) := rfl

/-- The coordinatewise integer embedding is injective. -/
theorem integerEmbed_injective {d : Nat} :
    Function.Injective (integerEmbed (d := d)) := by
  intro n m hnm
  funext i
  have hi : (n i : Real) = (m i : Real) := congrFun hnm i
  exact_mod_cast hi

/-- Cached real coordinate basis vector. -/
def basisVector {d : Nat} (r : Fin d) : RealVec d :=
  fun i ↦ if i = r then 1 else 0

@[simp]
theorem basisVector_apply {d : Nat} (r i : Fin d) :
    basisVector r i = if i = r then 1 else 0 := rfl

/-- Integer companion of `basisVector`. -/
def intBasisVector {d : Nat} (r : Fin d) : IntVec d :=
  fun i ↦ if i = r then 1 else 0

@[simp]
theorem intBasisVector_apply {d : Nat} (r i : Fin d) :
    intBasisVector r i = if i = r then 1 else 0 := rfl

/-- Integer basis vectors embed as real basis vectors. -/
@[simp]
theorem integerEmbed_intBasisVector {d : Nat} (r : Fin d) :
    integerEmbed (intBasisVector r) = basisVector r := by
  ext i
  simp only [integerEmbed_apply, intBasisVector_apply, basisVector_apply]
  split <;> simp_all

/-- Natural `l¹` radius on the integer lattice. -/
def indexSize {d : Nat} (n : IntVec d) : Nat :=
  ∑ i : Fin d, (n i).natAbs

/-- Exact finite ball for `indexSize`. -/
def indexBall (d N : Nat) : Finset (IntVec d) := by
  classical
  exact (Fintype.piFinset (fun _ : Fin d ↦
    Finset.Icc (-(N : Int)) (N : Int))).filter (fun n ↦ indexSize n ≤ N)

/-- Exact membership criterion for an index ball. -/
@[simp]
theorem mem_indexBall {d N : Nat} {n : IntVec d} :
    n ∈ indexBall d N ↔ indexSize n ≤ N := by
  classical
  constructor
  · intro hn
    exact (Finset.mem_filter.mp hn).2
  · intro hn
    apply Finset.mem_filter.mpr
    refine ⟨?_, hn⟩
    rw [Fintype.mem_piFinset]
    intro i
    simp only [Finset.mem_Icc]
    have hcoord : (n i).natAbs ≤ N := by
      refine le_trans ?_ hn
      unfold indexSize
      exact Finset.single_le_sum
        (f := fun j : Fin d ↦ (n j).natAbs)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    omega

/-- Every coordinate radius is bounded by `indexSize`. -/
theorem indexSize_coordinate_le {d : Nat} (n : IntVec d) (i : Fin d) :
    (n i).natAbs ≤ indexSize n := by
  unfold indexSize
  exact Finset.single_le_sum
    (f := fun j : Fin d ↦ (n j).natAbs)
    (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)

/-- Index balls are monotone in their radius. -/
theorem indexBall_mono {d N M : Nat} (hNM : N ≤ M) :
    indexBall d N ⊆ indexBall d M := by
  intro n hn
  rw [mem_indexBall] at hn ⊢
  exact hn.trans hNM

/-- Two-sided null condition on `Z^d`. -/
def TendsToZeroAtIntVecInfinity {d : Nat}
    (delta : IntVec d → RealVec d) : Prop :=
  ∀ eta : Real, 0 < eta → ∃ N : Nat, ∀ n : IntVec d,
    N ≤ indexSize n → ‖delta n‖ < eta

/-- Perturbed lattice frequency. -/
def frequency {d : Nat} (delta : IntVec d → RealVec d)
    (n : IntVec d) : RealVec d :=
  fun i ↦ (n i : Real) + delta n i

@[simp]
theorem frequency_apply {d : Nat} (delta : IntVec d → RealVec d)
    (n : IntVec d) (i : Fin d) :
    frequency delta n i = (n i : Real) + delta n i := rfl

/-- Set of perturbed frequencies; repetitions are collapsed. -/
def frequencySet {d : Nat} (delta : IntVec d → RealVec d) :
    Set (RealVec d) :=
  Set.range (frequency delta)

/-- Positive-sign Fourier character. -/
def fourierChar {d : Nat} (xi x : RealVec d) : Complex :=
  Complex.exp
    (((2 * Real.pi : Real) : Complex) * Complex.I *
      ((∑ i : Fin d, xi i * x i : Real) : Complex))

/-- Positive inverse Fourier sample on a restricted carrier. -/
def inverseSampleOn {d : Nat} (S : Set (RealVec d))
    (F : RealVec d → Complex) (xi : RealVec d) : Complex :=
  ∫ x in S, F x * fourierChar xi x

/-- Positive whole-space inverse Fourier sample. -/
def inverseSample {d : Nat} (F : RealVec d → Complex)
    (xi : RealVec d) : Complex :=
  inverseSampleOn Set.univ F xi

/-- Representative-stable almost-everywhere support. -/
def AESupportedIn {d : Nat} (F : RealVec d → Complex)
    (S : Set (RealVec d)) : Prop :=
  ∀ᵐ x ∂volume, x ∉ S → F x = 0

/-- Real squared `L²` mass on a carrier. -/
def sqNormOn {d : Nat} (S : Set (RealVec d))
    (F : RealVec d → Complex) : Real :=
  ∫ x in S, ‖F x‖ ^ 2

/-- Open unit product cube. -/
def unitCube (d : Nat) : Set (RealVec d) :=
  {x | ∀ i, x i ∈ Set.Ioo (0 : Real) 1}

/-- Membership in the integer lattice. -/
def IsIntegralVector {d : Nat} (xi : RealVec d) : Prop :=
  ∃ n : IntVec d, xi = integerEmbed n

namespace Internal

/-- Euclidean wrapper used only at the Schwartz boundary. -/
abbrev EuclideanVec (d : Nat) := EuclideanSpace Real (Fin d)

/-- Sole continuous-linear equivalence for Pi/Euclidean transport. -/
noncomputable def realVecEuclideanCLE (d : Nat) :
    RealVec d ≃L[Real] EuclideanVec d :=
  (PiLp.continuousLinearEquiv 2 Real (fun _ : Fin d => Real)).symm

/-- Coordinate-identity map into Euclidean space. -/
noncomputable def toEuclidean {d : Nat} (x : RealVec d) : EuclideanVec d :=
  realVecEuclideanCLE d x

/-- Inverse coordinate-identity map. -/
noncomputable def fromEuclidean {d : Nat} (z : EuclideanVec d) : RealVec d :=
  (realVecEuclideanCLE d).symm z

/-- Coordinate interface for `toEuclidean`. -/
@[simp]
theorem toEuclidean_apply {d : Nat} (x : RealVec d) (i : Fin d) :
    toEuclidean x i = x i := by
  rfl

/-- Coordinate interface for `fromEuclidean`. -/
@[simp]
theorem fromEuclidean_apply {d : Nat} (z : EuclideanVec d) (i : Fin d) :
    fromEuclidean z i = z i := by
  rfl

/-- Left inverse of the Euclidean transport. -/
@[simp]
theorem fromEuclidean_toEuclidean {d : Nat} (x : RealVec d) :
    fromEuclidean (toEuclidean x) = x := by
  exact (realVecEuclideanCLE d).symm_apply_apply x

/-- Right inverse of the Euclidean transport. -/
@[simp]
theorem toEuclidean_fromEuclidean {d : Nat} (z : EuclideanVec d) :
    toEuclidean (fromEuclidean z) = z := by
  exact (realVecEuclideanCLE d).apply_symm_apply z

/-- The Pi-to-Euclidean coordinate identity preserves volume. -/
theorem toEuclidean_measurePreserving {d : Nat} :
    MeasurePreserving (toEuclidean (d := d)) volume volume := by
  change MeasurePreserving (WithLp.toLp 2) volume volume
  exact PiLp.volume_preserving_toLp (Fin d)

/-- The inverse coordinate identity preserves volume. -/
theorem fromEuclidean_measurePreserving {d : Nat} :
    MeasurePreserving (fromEuclidean (d := d)) volume volume := by
  change MeasurePreserving WithLp.ofLp volume volume
  exact PiLp.volume_preserving_ofLp (Fin d)

/-- Exact factor order for the Euclidean inner product. -/
theorem toEuclidean_inner_eq_sum {d : Nat} (xi x : RealVec d) :
    inner Real (toEuclidean xi) (toEuclidean x) =
      (∑ i : Fin d, xi i * x i : Real) := by
  rw [show toEuclidean xi = WithLp.toLp 2 xi from rfl,
    show toEuclidean x = WithLp.toLp 2 x from rfl,
    EuclideanSpace.inner_toLp_toLp]
  simp only [dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

/-- Pi supremum norm is bounded by the Euclidean norm. -/
theorem piNorm_le_toEuclidean_norm {d : Nat} (x : RealVec d) :
    ‖x‖ ≤ ‖toEuclidean x‖ := by
  have hnn : (Finset.univ.sup fun i : Fin d ↦ ‖x i‖₊) ≤ ‖toEuclidean x‖₊ := by
    rw [Finset.sup_le_iff]
    intro i _
    simpa only [toEuclidean_apply] using
      (PiLp.nnnorm_apply_le (toEuclidean x) i)
  calc
    ‖x‖ = ↑(Finset.univ.sup fun i : Fin d ↦ ‖x i‖₊) := rfl
    _ ≤ ↑‖toEuclidean x‖₊ := NNReal.coe_le_coe.mpr hnn
    _ = ‖toEuclidean x‖ := rfl

/-- Exact no-scalar integral substitution. -/
theorem integral_comp_fromEuclidean {d : Nat} (g : RealVec d → Complex)
    (_hg : Integrable g volume) :
    (∫ z : EuclideanVec d, g (fromEuclidean z) ∂volume) =
      ∫ x : RealVec d, g x ∂volume := by
  simpa only [fromEuclidean] using
    (MeasureTheory.MeasurePreserving.integral_comp
      (fromEuclidean_measurePreserving (d := d))
      (realVecEuclideanCLE d).symm.toHomeomorph.measurableEmbedding g)

/-- Smoothness transport through `WithLp.ofLp`. -/
theorem contDiff_comp_fromEuclidean {d : Nat} {g : RealVec d → Complex}
    (hg : ContDiff Real (↑(⊤ : ℕ∞)) g) :
    ContDiff Real (↑(⊤ : ℕ∞))
      (fun z : EuclideanVec d => g (fromEuclidean z)) := by
  change ContDiff Real (↑(⊤ : ℕ∞)) (g ∘ WithLp.ofLp)
  exact hg.comp (PiLp.contDiff_ofLp (p := (2 : ENNReal)))

/-- Compact-support transport through the PiLp homeomorphism. -/
theorem hasCompactSupport_comp_fromEuclidean {d : Nat}
    {g : RealVec d → Complex} (hg : HasCompactSupport g) :
    HasCompactSupport (fun z : EuclideanVec d => g (fromEuclidean z)) := by
  change HasCompactSupport (g ∘ WithLp.ofLp)
  exact hg.comp_homeomorph (realVecEuclideanCLE d).symm.toHomeomorph

end Internal

end AsymptoticallyIntegerHD
