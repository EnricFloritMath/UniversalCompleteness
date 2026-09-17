import AsymptoticallyIntegerHD.PublicAssembly

/-!
# Null perturbations are not universally complete — Section 6, item (2)

Let Λ = {n + δₙ : n ∈ ℤᵈ}, where δₙ tends to zero as |n| tends to infinity.
For every ε > 0, there is a measurable S with |S| < ε on which E(Λ) fails
to have dense span in L²(S). The perturbation is fixed before ε is chosen;
the theorem supplies a possibly different set S for each ε.

We define the frequencies and their null-convergence condition, then the
meaning of completeness in L². `null_perturbations` is the main statement.
To compare with the article, read the definitions and the theorem through
`:= by`; the proof that follows connects them to the completed formalization.
Build instructions are in ../README.md.
-/

open Complex MeasureTheory Real Set
open scoped BigOperators ENNReal Topology

noncomputable section

namespace NullPerturbations

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

/-! ## Asymptotically integral frequencies -/

/-- The Euclidean ℓ² norm on real coordinate vectors. -/
def norm₂ (x : ℝᵈ) : ℝ := √(∑ i, x i ^ 2)

/-- The coordinatewise injection of integer vectors into real vectors. -/
def integerEmbed (n : ℤᵈ) : ℝᵈ := fun i => (n i : ℝ)

/-- δₙ → 0 as |n| → ∞, with no rate or nonvanishing assumption.
Both the integer radius and the perturbation size are displayed using the
Euclidean ℓ² norm. -/
def NullPerturbation (δ : ℤᵈ → ℝᵈ) : Prop :=
  ∀ η > (0 : ℝ), ∃ N : ℕ, ∀ n : ℤᵈ,
    (N : ℝ) ≤ norm₂ (integerEmbed n) → norm₂ (δ n) < η

/-- Λ = {n + δₙ : n ∈ ℤᵈ}; repetitions are allowed. -/
def Λ (δ : ℤᵈ → ℝᵈ) : Set ℝᵈ :=
  Set.range (fun n : ℤᵈ => fun i => (n i : ℝ) + δ n i)

/-! ## Completeness in Lᵖ(S) -/

/-- E(Λ) is complete in Lᵖ(S) when its complex linear span is dense.

Each generator g is an Lᵖ equivalence class equal almost everywhere on S to
an exponential from E(Λ). `=ᵐ[volume.restrict S]` expresses that equality;
`volume.restrict S` is Lebesgue measure restricted to S.
`Dense` uses the Lᵖ norm topology. The parameter `hp` supplies the lower
bound required for this topology. -/
def Complete (Λ : Set ℝᵈ) (S : Set ℝᵈ) (p : ℝ≥0∞) (hp : 1 ≤ p) : Prop :=
  letI : Fact (1 ≤ p) := ⟨hp⟩
  Dense (↑(Submodule.span ℂ
    {g : Lp ℂ p (volume.restrict S) | ∃ f ∈ E Λ, g =ᵐ[volume.restrict S] f}) :
      Set (Lp ℂ p (volume.restrict S)))

/-! ## Section 6, item (2) -/

/-- For every ε > 0 there is a measurable S ⊆ ℝᵈ with |S| < ε such that
E(Λ) is not complete in L²(S). The set S need not be bounded.
`ENNReal.ofReal ε` regards the positive real ε as a measure value. -/
theorem null_perturbations
    (hd : 0 < d) (δ : ℤᵈ → ℝᵈ) (hδ : NullPerturbation δ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ S : Set ℝᵈ, MeasurableSet S ∧ volume S < ENNReal.ofReal ε ∧
      ¬ Complete (Λ δ) S 2 (by norm_num) := by
  have norm₂_eq_toEuclidean (x : ℝᵈ) :
      norm₂ x = ‖AsymptoticallyIntegerHD.Internal.toEuclidean x‖ := by
    rw [norm₂, EuclideanSpace.norm_eq]
    change √(∑ i, x i ^ 2) = √(∑ i, ‖x i‖ ^ 2)
    simp [Real.norm_eq_abs, sq_abs]
  have pi_le_norm₂ (x : ℝᵈ) : ‖x‖ ≤ norm₂ x := by
    rw [norm₂_eq_toEuclidean x]
    exact AsymptoticallyIntegerHD.Internal.piNorm_le_toEuclidean_norm x
  have coord_le_norm₂ (n : ℤᵈ) (i : Fin d) :
      ‖(n i : ℝ)‖ ≤ norm₂ (integerEmbed n) := by
    calc
      ‖(fun j : Fin d => (n j : ℝ)) i‖ ≤ ‖(fun j : Fin d => (n j : ℝ))‖ := by
        change ‖(n i : ℝ)‖ ≤ ‖fun j : Fin d => (n j : ℝ)‖
        exact norm_le_pi_norm (fun j : Fin d => (n j : ℝ)) i
      _ ≤ norm₂ (fun j : Fin d => (n j : ℝ)) := pi_le_norm₂ _
      _ = norm₂ (integerEmbed n) := rfl
  have hδ' : AsymptoticallyIntegerHD.TendsToZeroAtIntVecInfinity δ := by
    intro η hη
    obtain ⟨N, hN⟩ := hδ η hη
    refine ⟨d * N, ?_⟩
    intro n hn
    change d * N ≤ ∑ i : Fin d, (n i).natAbs at hn
    obtain ⟨i, hi⟩ : ∃ i : Fin d, N ≤ (n i).natAbs := by
      by_contra h
      push Not at h
      have hle : ∀ i : Fin d, (n i).natAbs ≤ N := by
        intro i
        exact Nat.le_of_lt (h i)
      have hlt : (∑ i : Fin d, (n i).natAbs) < ∑ i : Fin d, N := by
        apply Finset.sum_lt_sum
        · intro i hi_mem
          exact hle i
        · refine ⟨⟨0, hd⟩, Finset.mem_univ _, h _⟩
      simp at hlt
      omega
    apply (pi_le_norm₂ (δ n)).trans_lt
    apply hN n
    calc
      (N : ℝ) ≤ ‖(n i : ℝ)‖ := by
        rw [Real.norm_eq_abs]
        calc
          (N : ℝ) ≤ ((n i).natAbs : ℝ) := by exact_mod_cast hi
          _ = |(n i : ℝ)| := by
            have h := congrArg (fun z : ℤ => (z : ℝ)) (Int.natCast_natAbs (n i))
            simpa [Int.cast_abs] using h
      _ ≤ norm₂ (integerEmbed n) := coord_le_norm₂ n i
  -- Transfer the completed noncompleteness result to the displayed L² classes.
  obtain ⟨S, hS, hfin, hsmall, hnot⟩ :=
    AsymptoticallyIntegerHD.theorem_1_4_higher_dimension d hd δ hδ' ε hε
  refine ⟨S, hS, hsmall, ?_⟩
  intro hcomplete
  apply hnot
  let a (ξ : {ξ : ℝᵈ // ξ ∈ Λ δ}) :=
    AsymptoticallyIntegerHD.restrictedExponential S hS hfin ξ.1
  have ha : ∀ ξ, a ξ =ᵐ[volume.restrict S] e ξ.1 := by
    intro ξ
    exact (AsymptoticallyIntegerHD.Internal.restrictedExponential_memLp
      S hS hfin ξ.1).coeFn_toLp
  have hgen := lp_generators_eq (Λ δ) S 2 a ha
  have hrange : Set.range a =
      {f | ∃ ξ ∈ Λ δ, f = AsymptoticallyIntegerHD.restrictedExponential S hS hfin ξ} := by
    ext f
    constructor
    · rintro ⟨ξ, rfl⟩; exact ⟨ξ.1, ξ.2, rfl⟩
    · rintro ⟨ξ, hξ, rfl⟩; exact ⟨⟨ξ, hξ⟩, rfl⟩
  dsimp only [Complete] at hcomplete
  rw [hgen, hrange] at hcomplete
  convert hcomplete using 1
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

#print axioms null_perturbations

end NullPerturbations
