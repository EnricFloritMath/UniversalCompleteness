import PeriodicWeakGapsHD.HigherDim.Basic

/-!
# Sobolev nonuniqueness — Section 6, items (4) and (5)

Repeat a measurable A ⊆ [0,1]ᵈ with 0 < |A| < 1 over every integer translate
to obtain the spectrum S = A + ℤᵈ. At every exponent 0 ≤ α ≤ d/2, including
the endpoint, a uniformly discrete set Λ cannot determine all continuous
functions in PW_S^(α): a function can vanish on Λ and still take the value
one at any prescribed x₀ outside Λ.

We first define the periodic spectrum, then the weighted Fourier space PWalpha.
`sobolev_nonuniqueness` is the main statement; `endpoint_nonuniqueness` gives
its α = 0 consequence for the same admissible A. The scope of that consequence
relative to item (5) is explained beside its declaration.
To compare with the article, read the definitions and each theorem through
`:= by`; the following proofs connect them to the completed formalization.
Build instructions are in ../README.md.
-/

open Complex MeasureTheory Real Set
open scoped BigOperators ENNReal FourierTransform Topology

noncomputable section

namespace PeriodicWeakGaps

variable {d : ℕ}

/-! `Fin d` indexes the d coordinates as 0, …, d−1, corresponding to the
article's 1, …, d. `EuclideanSpace` carries the Euclidean norm and ordinary
Lebesgue measure; its vectors still have coordinates `x i`. -/
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)
local notation "ℤᵈ" => (Fin d → ℤ)

/-! ## The periodic spectrum S = A + ℤᵈ -/

/-- The closed cube [0,1]ᵈ. -/
def unitCube : Set ℝᵈ := {x | ∀ i, x i ∈ Set.Icc (0 : ℝ) 1}

/-- S = A + ℤᵈ = ⋃ₖ (A+k). The integer coordinates are viewed in ℝᵈ. -/
def periodicSpectrum (A : Set ℝᵈ) : Set ℝᵈ :=
  {ξ | ∃ k : ℤᵈ, ξ - WithLp.toLp 2 (fun i => (k i : ℝ)) ∈ A}

/-- A common positive Euclidean separation between distinct points. -/
def UniformlyDiscrete (Λ : Set ℝᵈ) : Prop :=
  ∃ ρ > (0 : ℝ), ∀ x ∈ Λ, ∀ y ∈ Λ, x ≠ y → ρ ≤ ‖x - y‖

/-! ## Sobolev Paley–Wiener spaces -/

/-- The Sobolev weight 1 + |t|^(2α).
At α = 0 it is identically 2, so PWalpha 0 S is PW S. -/
def w (α : ℝ) (t : ℝᵈ) : ℝ :=
  1 + if α = 0 then 1 else Real.rpow ‖t‖ (2 * α)

/-- PW_S^(α): the functions f whose Fourier-side representative F satisfies:
1. F vanishes almost everywhere outside S;
2. its weighted energy ∫_S (1+|t|^(2α)) |F(t)|² dt is finite;
3. F and f belong to L²(ℝᵈ) and f = 𝓕⁻F as an L² class.

`∀ᵐ t ∂volume` means for almost every t with respect to Lebesgue measure.
The `withDensity` term is the measure (1+|t|^(2α)) 1_S(t) dt, so its `MemLp`
condition expresses the weighted energy bound. The witnesses hF and hf
certify square integrability of these same functions; `toLp` forms their
a.e. equivalence classes.

`𝓕⁻` is Mathlib's L² inverse Fourier transform, with positive sign exp(2πi t·x).
When F is also integrable, it agrees almost everywhere with
x ↦ ∫ F(t) exp(2πi t·x) dt. The theorem chooses a continuous representative,
so the values at x₀ and on Λ have their ordinary pointwise meaning. -/
def PWalpha (α : ℝ) (S : Set ℝᵈ) : Set (ℝᵈ → ℂ) :=
  {f | ∃ F : ℝᵈ → ℂ,
    (∀ᵐ t ∂volume, t ∉ S → F t = 0) ∧
    MemLp F 2 ((volume.restrict S).withDensity (fun t => ENNReal.ofReal (w α t))) ∧
    ∃ (hF : MemLp F 2 volume) (hf : MemLp f 2 volume),
      (𝓕⁻ (hF.toLp F) : Lp ℂ 2 volume) = hf.toLp f}

/-- The endpoint Paley–Wiener space PW_S = PW_S^(0). -/
def PW (S : Set ℝᵈ) : Set (ℝᵈ → ℂ) := PWalpha 0 S

/-! ## Nonuniqueness conclusion in Section 6, item (4) -/

/-- At and below α = d/2, every uniformly discrete Λ is a nonuniqueness set
for PW_S^(α) ∩ C(ℝᵈ), with S = A + ℤᵈ. The value at x₀ may be prescribed as 1.
The same function f belongs to PWalpha, is continuous, takes this prescribed value,
and vanishes at every point of Λ; in particular it is not the zero function. -/
theorem sobolev_nonuniqueness
    (hd : 0 < d) (A : Set ℝᵈ)
    (hA : MeasurableSet A) (hAcube : A ⊆ unitCube)
    (hApos : 0 < volume A) (hAsmall : volume A < 1)
    (α : ℝ) (hα : 0 ≤ α ∧ α ≤ (d : ℝ) / 2)
    (Λ : Set ℝᵈ) (hΛ : UniformlyDiscrete Λ)
    (x₀ : ℝᵈ) (hx₀ : x₀ ∉ Λ) :
    ∃ f ∈ PWalpha α (periodicSpectrum A),
      Continuous f ∧ f x₀ = 1 ∧ ∀ ξ ∈ Λ, f ξ = 0 := by
  obtain ⟨f, ⟨F, hF⟩, hcont, hvalue, hzero⟩ :=
    SpectralGapsPrelim.HigherDim.Hermite hd hA hAcube hApos hAsmall
      hα.1 (by linarith [hα.2]) hΛ hx₀
  exact ⟨f, ⟨F, hF.side.supported, hF.side.weightedMemLp,
    hF.invRep.P_memL2, hF.invRep.f_memL2, hF.invRep.inv_eq_l2⟩,
    hcont, hvalue, hzero⟩

/-! ## The α = 0 consequence used in Section 6, item (5) -/

/-- For every admissible A, PW_(A+ℤᵈ) ∩ C(ℝᵈ) has no uniformly discrete
uniqueness set: there is a nonzero function vanishing on any such Λ.
This proves the nonuniqueness conclusion for every A satisfying the hypotheses.
Item 5 additionally asserts the existence of a measurable spectrum
with periodic weak gaps. This declaration does not separately formalize that
existence, the spectrum's measurability, or the periodic weak-gap property.

For the article's deduction, one may choose A = [0,1/2]ᵈ: its measure is 2^(−d),
and (A+ℤᵈ) ∩ [0,1]ᵈ agrees with A up to boundary null sets. This sentence
explains the mathematical deduction; those additional claims are not Lean
conclusions of the declaration below. -/
theorem endpoint_nonuniqueness
    (hd : 0 < d) (A : Set ℝᵈ)
    (hA : MeasurableSet A) (hAcube : A ⊆ unitCube)
    (hApos : 0 < volume A) (hAsmall : volume A < 1) :
    ∀ Λ : Set ℝᵈ, UniformlyDiscrete Λ →
      ∃ f ∈ PW (periodicSpectrum A),
        Continuous f ∧ f ≠ 0 ∧ ∀ ξ ∈ Λ, f ξ = 0 := by
  intro Λ hΛ
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hnull : volume Λ = 0 :=
    (SpectralGapsPrelim.HigherDim.uniformlyDiscrete_countable hΛ).measure_zero volume
  have hnot : ¬ A ⊆ Λ := by
    intro hsub
    have hle : volume A ≤ volume Λ := measure_mono hsub
    rw [hnull] at hle
    exact (not_lt_of_ge hle) hApos
  obtain ⟨x₀, _, hx₀⟩ := Set.not_subset.mp hnot
  obtain ⟨f, hf, hcont, hvalue, hzero⟩ :=
    sobolev_nonuniqueness hd A hA hAcube hApos hAsmall 0
      ⟨le_rfl, by positivity⟩ Λ hΛ x₀ hx₀
  refine ⟨f, hf, hcont, ?_, hzero⟩
  intro hzeroFun
  simp [hzeroFun] at hvalue

/-! ## Lean dependency check -/

#print axioms sobolev_nonuniqueness
#print axioms endpoint_nonuniqueness

end PeriodicWeakGaps
