import IntegerFrequenciesHD.Basic

/-!
# Universal integer frequencies — Section 6, item (3)

Let 0 ≤ v ≤ 1, and choose α so that 1, α₁, …, α_d are rationally independent.
Retain precisely those integer vectors n whose fractional part {n·α} lies in [1−v,1).
The selected set Λᵥ has uniform density v. For every measurable S ⊆ [0,1]ᵈ
with |S| < v, its Fourier samples determine every L¹(S) function and its
exponentials span a dense subspace of every Lᵖ(S), 1 ≤ p < ∞.

We define the selected frequencies, then completeness, density and uniqueness.
`integer_frequencies` states the three conclusions together. To compare with
the article, read the definitions and the theorem through `:= by`; the proof
that follows connects these objects to the completed formalization.
Build instructions are in ../README.md.
-/

open Complex MeasureTheory Real Set
open scoped BigOperators ENNReal Topology

noncomputable section

namespace IntegerFrequencies

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

/-- The coordinatewise injection of integer vectors into real vectors. -/
def integerEmbed (n : ℤᵈ) : ℝᵈ := fun i => (n i : ℝ)

theorem integerEmbed_injective {d : ℕ} :
    Function.Injective (integerEmbed (d := d)) := by
  intro n m h
  funext i
  have hi := congrFun h i
  change (n i : ℝ) = (m i : ℝ) at hi
  exact_mod_cast hi

/-- E(Λ) = {e_ξ : ξ ∈ Λ}, as a set of actual functions. -/
def E (Λ : Set ℝᵈ) : Set (ℝᵈ → ℂ) := e '' Λ

/-! ## The selected integer frequencies -/

/-- Rational independence of 1, α₁, ..., α_d. -/
def Independent (α : ℝᵈ) : Prop :=
  ∀ (q₀ : ℚ) (q : Fin d → ℚ),
    (q₀ : ℝ) + ∑ i, (q i : ℝ) * α i = 0 → q₀ = 0 ∧ ∀ i, q i = 0

/-- Λᵥ = {n ∈ ℤᵈ : {n·α} ∈ [1−v,1)}. The selection interval is half-open. -/
def integerΛ (α : ℝᵈ) (v : ℝ) : Set ℤᵈ :=
  {n | Int.fract (∑ i, (n i : ℝ) * α i) ∈ Set.Ico (1 - v) 1}

/-! The selected integer vectors embedded in the real frequency space. -/
def Λ (α : ℝᵈ) (v : ℝ) : Set ℝᵈ := integerEmbed '' integerΛ α v

/-- The closed cube [0,1]ᵈ containing the sets S in the article. -/
def unitCube : Set ℝᵈ := {x | ∀ i, x i ∈ Set.Icc (0 : ℝ) 1}

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

/-- Completeness on every measurable S ⊆ unitCube of measure less than v, in every
Lᵖ(S) with 1 ≤ p < ∞. -/
def UniversallyCompleteOnUnitCube (Λ : Set ℝᵈ) (v : ℝ) : Prop :=
  ∀ S : Set ℝᵈ, MeasurableSet S → S ⊆ unitCube → volume S < ENNReal.ofReal v →
    ∀ (p : ℝ≥0∞) (hp : 1 ≤ p), p < ∞ → Complete Λ S p hp

/-! ## Uniform density and Fourier uniqueness -/

/-- Integer frequencies in the real half-open cube y + [0,R)ᵈ. -/
def integerCubePoints (Λ : Set ℤᵈ) (y : ℝᵈ) (R : ℝ) : Set ℤᵈ :=
  {n | n ∈ Λ ∧ ∀ i, y i ≤ (n i : ℝ) ∧ (n i : ℝ) < y i + R}

/-- D(Λ) = D: the normalized counts tend to D uniformly in the origin y.
For each ε, one threshold R₀ works for every y. Equivalently, the counting
error is o(Rᵈ), uniformly in y. The finiteness clause makes `ncard` the
ordinary number of selected real frequencies. -/
def UniformDensity (Λ : Set ℝᵈ) (D : ℝ) : Prop :=
  (∀ (x : ℝᵈ) (R : ℝ), 0 < R →
    (Λ ∩ {y | ∀ i, x i ≤ y i ∧ y i < x i + R}).Finite) ∧
  ∀ ε > (0 : ℝ), ∃ R₀ > (0 : ℝ), ∀ (R : ℝ), R₀ ≤ R → ∀ (x : ℝᵈ),
    |((Λ ∩ {y | ∀ i, x i ≤ y i ∧ y i < x i + R}).ncard : ℝ) / R ^ d - D| ≤ ε

/-- Uniqueness for integrable functions on subsets of the unit cube.
The functions `g ∈ E Λ` are the positive exponentials; `star (g x)` gives
the negative Fourier sign in the paper. -/
def L1UniquenessOnUnitCube (Λ : Set ℝᵈ) (v : ℝ) : Prop :=
  ∀ S : Set ℝᵈ, MeasurableSet S → S ⊆ unitCube → volume S < ENNReal.ofReal v →
    ∀ f : ℝᵈ → ℂ, Integrable f (volume.restrict S) →
      (∀ g ∈ E Λ, (∫ x in S, f x * star (g x)) = 0) →
      f =ᵐ[volume.restrict S] 0

/-! ## Section 6, item (3) -/

/-- Section 6, item (3), has three conclusions: uniform density v; L¹ Fourier
uniqueness; and dense exponential span in each finite Lᵖ(S), p ≥ 1.
The last two hold for every measurable S ⊆ [0,1]ᵈ with |S| < v.

At v = 0 the window is empty and Λᵥ has density zero; the strict inequality
|S| < 0 leaves no S for the analytic conclusions. At v = 1 the window
contains every fractional part and Λᵥ is the embedded integer lattice. -/
theorem integer_frequencies
    (hd : 0 < d) (α : ℝᵈ) (hα : Independent α)
    (v : ℝ) (hv : v ∈ Set.Icc (0 : ℝ) 1) :
    UniformDensity (Λ α v) v ∧ L1UniquenessOnUnitCube (Λ α v) v ∧
    UniversallyCompleteOnUnitCube (Λ α v) v := by
  -- Apply the completed theorem, then identify the displayed Lᵖ generators.
  have h := IntegerFrequenciesHD.integer_frequencies_higher_dimension
    d hd α hα v hv.1 hv.2
  have hcube (y : ℝᵈ) (R : ℝ) :
      (Λ α v ∩ {x | ∀ i, y i ≤ x i ∧ x i < y i + R}) =
        integerEmbed '' integerCubePoints (integerΛ α v) y R := by
    ext x
    constructor
    · rintro ⟨⟨n, hn, rfl⟩, hx⟩
      refine ⟨n, ?_, rfl⟩
      exact ⟨hn, by simpa [integerEmbed] using hx⟩
    · rintro ⟨n, ⟨hn, hx⟩, rfl⟩
      refine ⟨⟨n, hn, rfl⟩, ?_⟩
      simpa [integerEmbed] using hx
  have hcount (y : ℝᵈ) (R : ℝ) :
      ((Λ α v ∩ {x | ∀ i, y i ≤ x i ∧ x i < y i + R}).ncard : ℝ) =
        (IntegerFrequenciesHD.cubeCount
          (IntegerFrequenciesHD.integerFrequencySetHD α v) y R : ℝ) := by
    rw [hcube, Set.ncard_image_of_injective _ integerEmbed_injective]
    simp [integerCubePoints, integerΛ, IntegerFrequenciesHD.cubeCount,
      IntegerFrequenciesHD.integerFrequencySetHD,
      IntegerFrequenciesHD.realCube, IntegerFrequenciesHD.dotIntReal]
  have hL1 : L1UniquenessOnUnitCube (Λ α v) v := by
    intro S hS hsub hsmall f hf hzero
    apply h.universalL1 S hS hsub hsmall f hf
    intro n hn
    have hn' : n ∈ integerΛ α v := by
      change Int.fract (∑ i, (n i : ℝ) * α i) ∈ Set.Ico (1 - v) 1
      exact hn
    exact hzero (e (integerEmbed n))
      ⟨integerEmbed n, ⟨n, hn', rfl⟩, rfl⟩
  refine ⟨⟨?_, ?_⟩, hL1, ?_⟩
  · intro y R hR
    rw [hcube]
    exact (h.density.finite_count y R hR.le).image integerEmbed
  · intro ε hε
    obtain ⟨R₀, hR₀, hbound⟩ := h.density.uniform_error ε hε
    refine ⟨R₀, hR₀, ?_⟩
    intro R hR y
    have hRpos : 0 < R := lt_of_lt_of_le hR₀ hR
    have hpow : 0 < R ^ d := pow_pos hRpos _
    have hraw := hbound R hR y
    rw [hcount]
    calc
      |(IntegerFrequenciesHD.cubeCount
          (IntegerFrequenciesHD.integerFrequencySetHD α v) y R : ℝ) /
            R ^ d - v|
          = |((IntegerFrequenciesHD.cubeCount
              (IntegerFrequenciesHD.integerFrequencySetHD α v) y R : ℝ) -
            v * R ^ d) / R ^ d| := by
              congr 1
              field_simp [ne_of_gt hpow]
      _ = |(IntegerFrequenciesHD.cubeCount
          (IntegerFrequenciesHD.integerFrequencySetHD α v) y R : ℝ) -
            v * R ^ d| / R ^ d := by
            rw [abs_div, abs_of_pos hpow]
      _ ≤ ε := (div_le_iff₀ hpow).2 hraw
  intro S hS hsub hsmall p hp hptop
  let hfin := ne_of_lt (lt_of_lt_of_le hsmall le_top)
  let a (n : {n : ℤᵈ // n ∈ integerΛ α v}) :=
    IntegerFrequenciesHD.exponentialLpHD S hS p hp hfin n.1
  have ha : ∀ n, a n =ᵐ[volume.restrict S] e (integerEmbed n.1) := by
    intro n
    exact (IntegerFrequenciesHD.Internal.memLp_fourierCharHD_restrict
      S hS hfin p hp n.1).coeFn_toLp
  have hgen := lp_generators_eq (integerΛ α v) (Λ α v) (by rfl) S p a ha
  dsimp only [Complete]
  rw [hgen]
  simpa only [IntegerFrequenciesHD.ExponentialCompleteInLpHD, a, hfin,
    Λ, integerΛ, IntegerFrequenciesHD.integerFrequencySetHD,
    IntegerFrequenciesHD.dotIntReal] using
    h.completeLp S hS hsub hsmall p hp (ne_of_lt hptop)

where
  /-- Conversion used only by the proof above: the visible almost-everywhere
  exponentials are exactly any chosen Lᵖ representatives of those functions. -/
  lp_generators_eq (ΛI : Set ℤᵈ) (Λ : Set ℝᵈ)
      (hΛ : Λ = integerEmbed '' ΛI) (S : Set ℝᵈ) (p : ℝ≥0∞)
      (a : {ξ : ℤᵈ // ξ ∈ ΛI} → Lp ℂ p (volume.restrict S))
      (ha : ∀ ξ, a ξ =ᵐ[volume.restrict S] e (integerEmbed ξ.1)) :
      {g : Lp ℂ p (volume.restrict S) | ∃ f ∈ E Λ, g =ᵐ[volume.restrict S] f} =
        Set.range a := by
    have hE : E Λ = e '' (integerEmbed '' ΛI) := by
      simp [E, hΛ]
    rw [hE]
    ext g
    constructor
    · rintro ⟨f, ⟨x, ⟨ξ, hξ, rfl⟩, rfl⟩, hg⟩
      exact ⟨⟨ξ, hξ⟩, Lp.ext ((ha ⟨ξ, hξ⟩).trans hg.symm)⟩
    · rintro ⟨ξ, rfl⟩
      exact ⟨e (integerEmbed ξ.1),
        ⟨integerEmbed ξ.1, ⟨ξ.1, ξ.2, rfl⟩, rfl⟩, ha ξ⟩

/-! ## Lean dependency check -/

#print axioms integer_frequencies

end IntegerFrequencies
