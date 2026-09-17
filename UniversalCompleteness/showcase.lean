import UniversalCompletenessHD.Basic

/-!
# Universal completeness on finite-measure sets — Section 6, item (1)

Move each integer point n in the direction β by the amount {n·α} − 1/2:
  Λ = {n + β({n·α} − 1/2) : n ∈ ℤᵈ}.
Under the two rational-independence assumptions below and ‖β‖₂ < 1/2,
this set is uniformly discrete and has density one. The same Λ works for
every measurable S with |S| < 1: its Fourier samples determine every L¹(S)
function, and its exponentials span a dense subspace of every Lᵖ(S), 1 ≤ p < ∞.

First we define the frequencies, then completeness, separation, and density.
`universal_completeness` states all four conclusions together. Read
the definitions and the theorem through `:= by`; the proof that follows
connects these objects to the completed formalization. The repository README
gives the build instructions.
-/

open Complex MeasureTheory Real Set
open scoped BigOperators ENNReal Topology

noncomputable section

namespace UniversalCompleteness

variable {d : ℕ}

/-! ## Euclidean coordinates and exponentials -/

/-! `Fin d` indexes the d coordinates as 0, …, d−1; this is the article's
1, …, d with a change of indexing. A vector is a function on those indices,
and `∑ i` sums over all of them. `volume` is product Lebesgue measure.
The cast `(n i : ℝ)` regards an integer coordinate as a real number. -/
local notation "ℝᵈ" => (Fin d → ℝ)
local notation "ℤᵈ" => (Fin d → ℤ)

/-- The scalar product x · y = ∑ᵢ xᵢ yᵢ. -/
def dot (x y : ℝᵈ) : ℝ := ∑ i, x i * y i

/-- The paper's exponential e_ξ(x) = exp(2πi ξ·x). -/
def e (ξ x : ℝᵈ) : ℂ :=
  Complex.exp (((2 * π : ℝ) : ℂ) * I * (dot ξ x : ℂ))

/-- E(Λ) = {e_ξ : ξ ∈ Λ}, as a set of actual functions. -/
def E (Λ : Set ℝᵈ) : Set (ℝᵈ → ℂ) := e '' Λ

/-! ## The arithmetic construction Λ_{α,β} -/

/-- Rational independence of 1, α₁, ..., α_d. -/
def Independent (α : ℝᵈ) : Prop :=
  ∀ (q₀ : ℚ) (q : Fin d → ℚ),
    (q₀ : ℝ) + ∑ i, (q i : ℝ) * α i = 0 → q₀ = 0 ∧ ∀ i, q i = 0

/-- Rational independence of 1 + α·β, β₁, ..., β_d. -/
def Nonresonant (α β : ℝᵈ) : Prop :=
  ∀ (q₀ : ℚ) (q : Fin d → ℚ),
    (q₀ : ℝ) * (1 + dot α β) + ∑ i, (q i : ℝ) * β i = 0 →
      q₀ = 0 ∧ ∀ i, q i = 0

/-- The Euclidean norm, written explicitly on coordinate vectors. -/
def norm₂ (x : ℝᵈ) : ℝ := √(∑ i, x i ^ 2)

/-- δₙ = β({n·α} − 1/2); `Int.fract t` is the fractional part {t}. -/
def δ (α β : ℝᵈ) (n : ℤᵈ) : ℝᵈ :=
  fun i => (Int.fract (∑ j, (n j : ℝ) * α j) - 1 / 2) * β i

/-- Λ_{α,β} = {n + δₙ : n ∈ ℤᵈ}. -/
def Λ (α β : ℝᵈ) : Set ℝᵈ :=
  Set.range (fun n : ℤᵈ => fun i => (n i : ℝ) + δ α β n i)

/-! ## Completeness in Lᵖ(S) -/

/-- E(Λ) is complete in Lᵖ(S) when its complex linear span is dense.

Each generator g is an Lᵖ equivalence class equal almost everywhere on S to
an exponential from E(Λ). `=ᵐ[volume.restrict S]` expresses that equality;
`volume.restrict S` is Lebesgue measure restricted to S.

In the theorem, the measure bound makes S finite-measure. Every exponential
has modulus one, so its restriction belongs to each finite Lᵖ(S). The a.e.
formulation describes these classes without separate integrability arguments.
`Dense` uses the Lᵖ norm topology. The type `ℝ≥0∞` allows extended nonnegative
exponents; the theorem requires `1 ≤ p` and `p < ∞`. The certificate hp supplies
Lean with the lower bound needed for this topology. -/
def Complete (Λ : Set ℝᵈ) (S : Set ℝᵈ) (p : ℝ≥0∞) (hp : 1 ≤ p) : Prop :=
  letI : Fact (1 ≤ p) := ⟨hp⟩
  Dense (↑(Submodule.span ℂ
    {g : Lp ℂ p (volume.restrict S) | ∃ f ∈ E Λ, g =ᵐ[volume.restrict S] f}) :
      Set (Lp ℂ p (volume.restrict S)))

/-- Completeness on every measurable S of measure less than v, in every
Lᵖ(S) with 1 ≤ p < ∞. -/
def UniversallyComplete (Λ : Set ℝᵈ) (v : ℝ) : Prop :=
  ∀ S : Set ℝᵈ, MeasurableSet S → volume S < ENNReal.ofReal v →
    ∀ (p : ℝ≥0∞) (hp : 1 ≤ p), p < ∞ → Complete Λ S p hp

/-! ## Separation and uniform density -/

/-- Distinct points have a common positive Euclidean separation. -/
def UniformlyDiscrete (Λ : Set ℝᵈ) : Prop :=
  ∃ ρ > (0 : ℝ), ∀ x ∈ Λ, ∀ y ∈ Λ, x ≠ y → ρ ≤ norm₂ (x - y)

/-- D(Λ) = D: the normalized counts converge uniformly in the cube origin x.
For each ε, one threshold R₀ works for every x. The set inside `ncard` is
Λ ∩ (x + [0,R)ᵈ), and its finiteness makes `ncard` the ordinary point count. -/
def UniformDensity (Λ : Set ℝᵈ) (D : ℝ) : Prop :=
  (∀ (x : ℝᵈ) (R : ℝ), 0 < R →
    (Λ ∩ {y | ∀ i, x i ≤ y i ∧ y i < x i + R}).Finite) ∧
  ∀ ε > (0 : ℝ), ∃ R₀ > (0 : ℝ), ∀ (R : ℝ), R₀ ≤ R → ∀ (x : ℝᵈ),
    |((Λ ∩ {y | ∀ i, x i ≤ y i ∧ y i < x i + R}).ncard : ℝ) / R ^ d - D| ≤ ε

/-- The L¹ uniqueness conclusion on all measurable sets of measure less than v.
The functions `g ∈ E Λ` are the positive exponentials; `star (g x)` gives
the negative Fourier sign in the article. -/
def L1Uniqueness (Λ : Set ℝᵈ) (v : ℝ) : Prop :=
  ∀ S : Set ℝᵈ, MeasurableSet S → volume S < ENNReal.ofReal v →
    ∀ f : ℝᵈ → ℂ, Integrable f (volume.restrict S) →
      (∀ g ∈ E Λ, (∫ x in S, f x * star (g x)) = 0) →
      f =ᵐ[volume.restrict S] 0

/-! ## Section 6, item (1) -/

/-- Section 6, item (1), with its four conclusions in the paper's order:
1. a positive separation between distinct frequencies;
2. uniform density one;
3. L¹ Fourier uniqueness on every measurable S with |S| < 1;
4. dense exponential span in every Lᵖ(S), 1 ≤ p < ∞, on each such S.

The same Λ works for all S and p. -/
theorem universal_completeness
    (hd : 0 < d) (α β : ℝᵈ)
    (hα : Independent α) (hβ : Nonresonant α β) (hsmall : norm₂ β < 1 / 2) :
    UniformlyDiscrete (Λ α β) ∧
    UniformDensity (Λ α β) 1 ∧
    L1Uniqueness (Λ α β) 1 ∧
    UniversallyComplete (Λ α β) 1 := by
  -- Apply the completed theorem, then identify the displayed Lᵖ generators.
  have h := UniversalCompletenessHD.universal_completeness_higher_dimension
    d hd α β hα hβ hsmall
  have hL1 : L1Uniqueness (Λ α β) 1 := by
    intro S hS hsmallS f hf hzero
    apply h.universalL1 S hS hsmallS f hf
    intro ξ hξ
    exact hzero (e ξ) ⟨ξ, hξ, rfl⟩
  refine ⟨h.uniformlyDiscrete, ⟨?_, ?_⟩, hL1, ?_⟩
  · intro x R hR
    exact h.uniformDensity.finite_count x R hR.le
  · intro ε hε
    obtain ⟨R₀, hR₀, hbound⟩ := h.uniformDensity.uniform_limit ε hε
    refine ⟨R₀, hR₀, ?_⟩
    intro R hR x
    exact le_of_lt (hbound x R hR)
  intro S hS hsmallS p hp hptop
  let hfin := ne_of_lt (lt_of_lt_of_le hsmallS le_top)
  let a (ξ : {ξ : ℝᵈ // ξ ∈ Λ α β}) :=
    UniversalCompletenessHD.positiveExponentialLpHD S hS p hp hfin ξ.1
  have ha : ∀ ξ, a ξ =ᵐ[volume.restrict S] e ξ.1 := by
    intro ξ
    exact (UniversalCompletenessHD.Internal.memLp_fourierCharHD_restrict
      S hS hfin p hp ξ.1).coeFn_toLp
  have hgen := lp_generators_eq (Λ α β) S p a ha
  dsimp only [Complete]
  rw [hgen]
  convert h.completeLp S hS hsmallS p hp (ne_of_lt hptop) using 1
  all_goals rfl

where
  /-- Conversion used only by the proof above: the visible almost-everywhere
  exponentials are exactly any chosen Lᵖ representatives of those functions. -/
  lp_generators_eq (Λ : Set ℝᵈ) (S : Set ℝᵈ) (p : ℝ≥0∞)
      (a : {ξ : ℝᵈ // ξ ∈ Λ} → Lp ℂ p (volume.restrict S))
      (ha : ∀ ξ, a ξ =ᵐ[volume.restrict S] e ξ.1) :
      {g : Lp ℂ p (volume.restrict S) | ∃ f ∈ E Λ, g =ᵐ[volume.restrict S] f} =
        Set.range a := by
    ext g
    constructor
    · rintro ⟨f, ⟨ξ, hξ, rfl⟩, hg⟩
      exact ⟨⟨ξ, hξ⟩, Lp.ext ((ha ⟨ξ, hξ⟩).trans hg.symm)⟩
    · rintro ⟨ξ, rfl⟩
      exact ⟨e ξ.1, ⟨ξ.1, ξ.2, rfl⟩, ha ξ⟩

/-! ## Lean dependency check -/

#print axioms universal_completeness

end UniversalCompleteness
