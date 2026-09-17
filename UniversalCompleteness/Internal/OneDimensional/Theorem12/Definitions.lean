import Mathlib.Analysis.Fourier.FourierTransform

noncomputable section

open MeasureTheory Set
open scoped ENNReal Topology BigOperators

namespace Theorem12

/- Proof idea: transparent formula. -/
def delta (alpha : ℝ) (beta : ℚ) (n : ℤ) : ℝ :=
  (beta : ℝ) * (Int.fract ((n : ℝ) * alpha) - 1 / 2)

/- Proof idea: transparent formula. -/
def frequency (alpha : ℝ) (beta : ℚ) (n : ℤ) : ℝ :=
  (n : ℝ) + delta alpha beta n

/- Proof idea: indexed range. -/
def frequencySet (alpha : ℝ) (beta : ℚ) : Set ℝ :=
  Set.range (frequency alpha beta)

/- Proof idea: transparent predicate. -/
def IsUniformlyDiscrete (Λ : Set ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ x ∈ Λ, ∀ y ∈ Λ, x ≠ y → c ≤ |x - y|

/- Proof idea: set ncard. -/
def intervalCount (Λ : Set ℝ) (x R : ℝ) : ℕ :=
  (Λ ∩ Set.Icc x (x + R)).ncard

/- Proof idea: literal uniform predicate. -/
def HasUniformDensity (Λ : Set ℝ) (D : ℝ) : Prop :=
  0 ≤ D ∧
    (∀ x R : ℝ, 0 ≤ R → (Λ ∩ Set.Icc x (x + R)).Finite) ∧
    ∀ ε : ℝ, 0 < ε → ∃ R0 : ℝ, 0 < R0 ∧
      ∀ R : ℝ, R0 ≤ R → ∀ x : ℝ,
        |((intervalCount Λ x R : ℕ) : ℝ) - D * R| ≤ ε * R

/- Proof idea: restricted integral. -/
def fourierSampleOn (S : Set ℝ) (f : ℝ → ℂ) (xi : ℝ) : ℂ :=
  ∫ x in S, f x * Complex.exp (-((2 * Real.pi : ℝ) : ℂ) * Complex.I *
    (xi : ℂ) * (x : ℂ))

/- Proof idea: literal restricted-measure
predicate with negative Fourier sign. -/
def UniversalL1Uniqueness (Λ : Set ℝ) : Prop :=
  ∀ (S : Set ℝ), MeasurableSet S → volume S < 1 →
    ∀ (f : ℝ → ℂ), Integrable f (volume.restrict S) →
      (∀ xi ∈ Λ, fourierSampleOn S f xi = 0) →
        f =ᵐ[volume.restrict S] (fun _ => 0)

/- Proof idea: bounded
measurable character on a finite restricted measure. -/
theorem memLp_exponential_restrict
    (S : Set ℝ) (hSmeas : MeasurableSet S) (hSfinite : volume S ≠ ∞)
    (p : ENNReal) (hp : 1 ≤ p) (xi : ℝ) :
    MemLp (fun x : ℝ => Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I *
      (xi : ℂ) * (x : ℂ))) p (volume.restrict S) := by
  letI : IsFiniteMeasure (volume.restrict S) :=
    ⟨by
      simpa [Measure.restrict_apply_univ, hSmeas] using
        (lt_top_iff_ne_top.mpr hSfinite)⟩
  apply MemLp.of_bound (C := 1)
  · fun_prop
  · filter_upwards with x
    rw [Complex.norm_exp]
    simp

/- Proof idea: transparent toLp wrapper. -/
def exponentialLp
    (S : Set ℝ) (hSmeas : MeasurableSet S) (p : ENNReal) (hp : 1 ≤ p)
    (hSfinite : volume S ≠ ∞) (xi : ℝ) : Lp ℂ p (volume.restrict S) := by
  letI : Fact (1 ≤ p) := ⟨hp⟩
  exact (memLp_exponential_restrict S hSmeas hSfinite p hp xi).toLp
    (fun x : ℝ => Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I *
      (xi : ℂ) * (x : ℂ)))

/- Proof idea: density of the
complex span of the indexed characters. -/
def ExponentialCompleteInLp
    (Λ : Set ℝ) (S : Set ℝ) (hSmeas : MeasurableSet S)
    (p : ENNReal) (hp : 1 ≤ p) (hSfinite : volume S ≠ ∞) : Prop := by
  letI : Fact (1 ≤ p) := ⟨hp⟩
  letI : IsFiniteMeasure (volume.restrict S) :=
    ⟨by
      simpa [Measure.restrict_apply_univ, hSmeas] using
        (lt_top_iff_ne_top.mpr hSfinite)⟩
  exact Dense (↑(Submodule.span ℂ
    (Set.range (fun xi : {x : ℝ // x ∈ Λ} =>
      exponentialLp S hSmeas p hp hSfinite xi.1))) : Set (Lp ℂ p (volume.restrict S)))

/- Proof idea: literal
proposition-valued structure. -/
structure Theorem12Conclusion (alpha : ℝ) (beta : ℚ) : Prop where
  uniformlyDiscrete : IsUniformlyDiscrete (frequencySet alpha beta)
  uniformDensity : HasUniformDensity (frequencySet alpha beta) 1
  universalL1 : UniversalL1Uniqueness (frequencySet alpha beta)
  completeLp : ∀ (S : Set ℝ) (hSmeas : MeasurableSet S) (hSlt : volume S < 1)
    (p : ENNReal) (hp : 1 ≤ p) (hpTop : p ≠ ∞),
      ExponentialCompleteInLp (frequencySet alpha beta) S hSmeas p hp
        (ne_of_lt (lt_of_lt_of_le hSlt le_top))

end Theorem12
