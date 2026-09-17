import Mathlib

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Topology ENNReal

namespace SpectralGapsPrelim.BirkhoffPointwise

variable {X : Type*} [MeasurableSpace X]
variable {μ : Measure X} {τ : X → X}

/-- Finite Birkhoff partial sums, kept as finite sums throughout the proof. -/
def partialSum (τ : X → X) (g : X → ℝ) (n : ℕ) (x : X) : ℝ :=
  Finset.sum (Finset.range n) (fun q => g (τ^[q] x))

/-- Finite positive-maximal set for Hopf's finite maximal ergodic lemma. -/
def finitePositiveMaxSet (τ : X → X) (g : X → ℝ) (K : ℕ) : Set X :=
  {x | ∃ n : ℕ, 0 < n ∧ n ≤ K ∧ 0 < partialSum τ g n x}

/-- Finite maximum of the partial sums `S_0, ..., S_K`. -/
def finiteMaxFunction (τ : X → X) (g : X → ℝ) (K : ℕ) (x : X) : ℝ :=
  Finset.sup' (Finset.range (K + 1)) (by simp) (fun n => partialSum τ g n x)

/-- Infinite absolute maximal set for Birkhoff averages. -/
def absMaxSet (τ : X → X) (F : X → ℝ) (lambda : ℝ) : Set X :=
  {x | ∃ N : ℕ, 0 < N ∧ lambda < |birkhoffAverage ℝ τ F N x|}

/-- Private-to-the-proof finite absolute maximal set.  It lives here because
it is used by the later maximal inequality. -/
def absMaxSetFinite (τ : X → X) (F : X → ℝ) (lambda : ℝ) (K : ℕ) : Set X :=
  {x | ∃ N : ℕ, 0 < N ∧ N ≤ K ∧ lambda < |birkhoffAverage ℝ τ F N x|}

/-- Finite positive-average maximal set used to pass from Hopf's lemma to weak
type `(1,1)`. -/
def positiveAvgMaxSetFinite (τ : X → X) (F : X → ℝ) (lambda : ℝ) (K : ℕ) :
    Set X :=
  {x | ∃ N : ℕ, 0 < N ∧ N ≤ K ∧
      lambda < birkhoffAverage ℝ τ (fun y => |F y|) N x}

/-- Strongly measurable representative of a raw integrable observable. -/
noncomputable def strongRep {F : X → ℝ} (hF : Integrable F μ) : X → ℝ :=
  hF.aestronglyMeasurable.mk F

/-- Quotient-level `L2` coboundary core.  The raw representative is
`c + g - g ∘ τ`. -/
structure L2CoboundaryCore (τ : X → X) (μ : Measure X) where
  c : ℝ
  g : Lp ℝ 2 μ

namespace L2CoboundaryCore

/-- Raw representative of an `L2` coboundary core. -/
def toFun (C : L2CoboundaryCore (X := X) τ μ) : X → ℝ :=
  fun x => C.c + C.g x - C.g (τ x)

end L2CoboundaryCore

/-- Koopman operator on `L2`, built from composition by a measure-preserving
map, built using `MeasureTheory.Lp.compMeasurePreservingₗᵢ`. -/
noncomputable def koopmanL2
    (hτ_mp : MeasurePreserving τ μ μ) :
    Lp ℝ 2 μ →ₗᵢ[ℝ] Lp ℝ 2 μ :=
  MeasureTheory.Lp.compMeasurePreservingₗᵢ
    ℝ (E := ℝ) (p := 2) τ hτ_mp

/-- Koopman operator as a continuous linear map, for the mean ergodic theorem. -/
noncomputable def koopmanL2CLM
    (hτ_mp : MeasurePreserving τ μ μ) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (koopmanL2 (μ := μ) hτ_mp).toContinuousLinearMap

private noncomputable def l2ToL1Linear [IsProbabilityMeasure μ] :
    Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 1 μ where
  toFun := fun g =>
    ⟨g.1,
      (MeasureTheory.Lp.antitone
        (E := ℝ) (μ := μ) (p := 1) (q := 2)
        (by norm_num : (1 : ℝ≥0∞) ≤ 2)) g.2⟩
  map_add' := by
    intro f g
    apply Subtype.ext
    rfl
  map_smul' := by
    intro c g
    apply Subtype.ext
    rfl

private lemma l2ToL1Linear_bound [IsProbabilityMeasure μ]
    (g : Lp ℝ 2 μ) :
    ‖l2ToL1Linear (μ := μ) g‖ ≤ ‖g‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  refine ENNReal.toReal_mono (Lp.eLpNorm_ne_top g) ?_
  simpa [l2ToL1Linear] using
    (MeasureTheory.eLpNorm_le_eLpNorm_of_exponent_le
      (μ := μ) (f := (g : X → ℝ)) (p := 1) (q := 2)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (Lp.aestronglyMeasurable g))

/-- Continuous inclusion `L2 -> L1` on a probability space. -/
noncomputable def l2ToL1 [IsProbabilityMeasure μ] :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 1 μ :=
  LinearMap.mkContinuous
    (l2ToL1Linear (μ := μ)) 1 (by
      intro g
      simpa using l2ToL1Linear_bound (μ := μ) g)

lemma l2ToL1_norm_le [IsProbabilityMeasure μ]
    (g : Lp ℝ 2 μ) :
    ‖l2ToL1 (μ := μ) g‖ ≤ ‖g‖ := by
  -- Proof idea: exported wrapper so later dense-core files do not repeat the
  -- same exponent-monotonicity proof.
  simpa [l2ToL1] using l2ToL1Linear_bound (μ := μ) g

namespace L2CoboundaryCore

/-- Quotient-level `L2` representative of the coboundary core. -/
noncomputable def toL2 [IsProbabilityMeasure μ]
    (hτ_mp : MeasurePreserving τ μ μ)
    (C : L2CoboundaryCore (X := X) τ μ) : Lp ℝ 2 μ :=
  Lp.const 2 μ C.c + C.g - koopmanL2 (μ := μ) hτ_mp C.g

/-- Quotient-level `L1` representative of the coboundary core. -/
noncomputable def toL1 [IsProbabilityMeasure μ]
    (hτ_mp : MeasurePreserving τ μ μ)
    (C : L2CoboundaryCore (X := X) τ μ) : Lp ℝ 1 μ :=
  l2ToL1 (μ := μ) (C.toL2 (τ := τ) hτ_mp)

end L2CoboundaryCore

/-- Countable metric basis for the maximal dense-transfer theorem. -/
def basisEps (m : ℕ) : ℝ := ((m + 1 : ℕ) : ℝ)⁻¹

/-- Maximal-error threshold attached to `basisEps`. -/
def basisLambda (m : ℕ) : ℝ := basisEps m / 4

end SpectralGapsPrelim.BirkhoffPointwise
