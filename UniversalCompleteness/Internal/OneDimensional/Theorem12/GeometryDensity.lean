import Theorem12.Definitions

noncomputable section

open Set

namespace Theorem12
namespace Internal

/- Proof idea: use fract bounds. -/
theorem abs_delta_le (alpha : ℝ) (beta : ℚ) (n : ℤ) :
    |delta alpha beta n| ≤ |(beta : ℝ)| / 2 := by
  rw [delta, abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  rw [abs_le]
  constructor <;>
    linarith [Int.fract_nonneg ((n : ℝ) * alpha),
      Int.fract_lt_one ((n : ℝ) * alpha)]

/- Proof idea: triangle inequality. -/
theorem abs_delta_sub_delta_le (alpha : ℝ) (beta : ℚ) (n m : ℤ) :
    |delta alpha beta n - delta alpha beta m| ≤ |(beta : ℝ)| := by
  rw [delta, delta]
  have hfactor :
      (beta : ℝ) * (Int.fract ((n : ℝ) * alpha) - 1 / 2) -
          (beta : ℝ) * (Int.fract ((m : ℝ) * alpha) - 1 / 2) =
        (beta : ℝ) *
          (Int.fract ((n : ℝ) * alpha) - Int.fract ((m : ℝ) * alpha)) := by
    ring
  rw [hfactor, abs_mul]
  have hfract :
      |Int.fract ((n : ℝ) * alpha) - Int.fract ((m : ℝ) * alpha)| ≤ 1 := by
    rw [abs_le]
    constructor <;>
      linarith [Int.fract_nonneg ((n : ℝ) * alpha),
        Int.fract_lt_one ((n : ℝ) * alpha),
        Int.fract_nonneg ((m : ℝ) * alpha),
        Int.fract_lt_one ((m : ℝ) * alpha)]
  simpa using mul_le_mul_of_nonneg_left hfract (abs_nonneg (beta : ℝ))

/- Proof idea: reverse triangle inequality. -/
theorem frequency_separation_indexed (alpha : ℝ) (beta : ℚ) (n m : ℤ)
    (hnm : n ≠ m) :
    1 - |(beta : ℝ)| ≤ |frequency alpha beta n - frequency alpha beta m| := by
  have hnm0 : n - m ≠ 0 := sub_ne_zero.mpr hnm
  have honeInt : (1 : ℤ) ≤ |n - m| := Int.one_le_abs hnm0
  have hone : (1 : ℝ) ≤ |((n - m : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast honeInt
  have hdelta := abs_delta_sub_delta_le alpha beta n m
  calc
    1 - |(beta : ℝ)| ≤ |((n - m : ℤ) : ℝ)| -
        |delta alpha beta n - delta alpha beta m| := by linarith
    _ ≤ |((n - m : ℤ) : ℝ) -
        (-(delta alpha beta n - delta alpha beta m))| := by
      simpa only [abs_neg] using
        (abs_sub_abs_le_abs_sub (((n - m : ℤ) : ℝ))
          (-(delta alpha beta n - delta alpha beta m)))
    _ = |frequency alpha beta n - frequency alpha beta m| := by
      congr 1
      simp only [frequency, Int.cast_sub]
      ring

/- Proof idea: positive separation. -/
theorem frequency_injective (alpha : ℝ) (beta : ℚ)
    (hbetaSmall : |(beta : ℝ)| < 1 / 2) :
    Function.Injective (frequency alpha beta) := by
  intro n m hnmFreq
  by_contra hnm
  have hsep := frequency_separation_indexed alpha beta n m hnm
  have hpos : 0 < 1 - |(beta : ℝ)| := by linarith
  have hzero : |frequency alpha beta n - frequency alpha beta m| = 0 := by
    rw [hnmFreq, sub_self, abs_zero]
  linarith

end Internal

/- Proof idea: separation witness. -/
theorem frequencySet_uniformlyDiscrete (alpha : ℝ) (beta : ℚ)
    (hbetaSmall : |(beta : ℝ)| < 1 / 2) :
    IsUniformlyDiscrete (frequencySet alpha beta) := by
  refine ⟨1 - |(beta : ℝ)|, by linarith, ?_⟩
  rintro _ ⟨n, rfl⟩ _ ⟨m, rfl⟩ hne
  apply Internal.frequency_separation_indexed alpha beta n m
  intro hnm
  subst m
  exact hne rfl

namespace Internal

/- Proof idea: displacement and injectivity. -/
theorem frequency_preimage_Icc_sandwich (alpha : ℝ) (beta : ℚ)
    (hbetaSmall : |(beta : ℝ)| < 1 / 2) (x R : ℝ) (hR : 0 ≤ R) :
    Set.range (fun n : {n : ℤ // (n : ℝ) ∈
      Set.Icc (x + |(beta : ℝ)| / 2) (x + R - |(beta : ℝ)| / 2)} =>
        frequency alpha beta n.1) ⊆
      frequencySet alpha beta ∩ Set.Icc x (x + R) ∧
    ∀ y ∈ frequencySet alpha beta ∩ Set.Icc x (x + R),
      ∃! n : ℤ, y = frequency alpha beta n ∧
        (n : ℝ) ∈ Set.Icc (x - |(beta : ℝ)| / 2)
          (x + R + |(beta : ℝ)| / 2) := by
  constructor
  · rintro _ ⟨n, rfl⟩
    have hdelta := abs_delta_le alpha beta n.1
    have hdelta' := (abs_le.mp hdelta)
    refine ⟨⟨n.1, rfl⟩, ?_⟩
    simp only [frequency]
    constructor <;> linarith [n.2.1, n.2.2]
  · intro y hy
    rcases hy.1 with ⟨n, rfl⟩
    have hdelta := abs_delta_le alpha beta n
    have hdelta' := abs_le.mp hdelta
    refine ⟨n, ?_, ?_⟩
    · refine ⟨rfl, ?_⟩
      simp only [frequency] at hy
      constructor <;> linarith [hy.2.1, hy.2.2]
    · intro m hm
      exact frequency_injective alpha beta hbetaSmall hm.1.symm

private theorem integerWindow_eq_finset (a b : ℝ) :
    {n : ℤ | (n : ℝ) ∈ Set.Icc a b} =
      (↑(Finset.Icc ⌈a⌉ ⌊b⌋) : Set ℤ) := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_Icc, Finset.mem_coe, Finset.mem_Icc]
  rw [Int.ceil_le, Int.le_floor]

private theorem integerWindow_finite (a b : ℝ) :
    Set.Finite {n : ℤ | (n : ℝ) ∈ Set.Icc a b} := by
  rw [integerWindow_eq_finset]
  exact Finset.finite_toSet _

private theorem integerWindow_ncard_upper (a b : ℝ) (hab : 0 ≤ b - a) :
    ((({n : ℤ | (n : ℝ) ∈ Set.Icc a b}.ncard : ℕ) : ℝ)) ≤ b - a + 1 := by
  rw [integerWindow_eq_finset, Set.ncard_coe_finset]
  by_cases h : ⌈a⌉ ≤ ⌊b⌋
  · have hcardInt := Int.card_Icc_of_le ⌈a⌉ ⌊b⌋
        (le_trans h (Int.le_add_of_nonneg_right (by omega)))
    have hcardReal :
        ((Finset.Icc ⌈a⌉ ⌊b⌋).card : ℝ) =
          ((⌊b⌋ + 1 - ⌈a⌉ : ℤ) : ℝ) := by
      exact_mod_cast hcardInt
    rw [hcardReal]
    have hfloor : ((⌊b⌋ : ℤ) : ℝ) ≤ b := Int.floor_le b
    have hceil : a ≤ ((⌈a⌉ : ℤ) : ℝ) := Int.le_ceil a
    push_cast
    linarith
  · rw [Finset.Icc_eq_empty h, Finset.card_empty]
    norm_num
    linarith

private theorem integerWindow_ncard_lower (a b : ℝ) (hab : 2 ≤ b - a) :
    b - a - 1 ≤ ((({n : ℤ | (n : ℝ) ∈ Set.Icc a b}.ncard : ℕ) : ℝ)) := by
  rw [integerWindow_eq_finset, Set.ncard_coe_finset]
  have hceil_lt : ((⌈a⌉ : ℤ) : ℝ) < a + 1 := Int.ceil_lt_add_one a
  have hfloor_gt : b - 1 < ((⌊b⌋ : ℤ) : ℝ) := Int.sub_one_lt_floor b
  have hle : ⌈a⌉ ≤ ⌊b⌋ := by
    rw [← Int.cast_le (R := ℝ)]
    linarith
  have hcardInt := Int.card_Icc_of_le ⌈a⌉ ⌊b⌋
      (le_trans hle (Int.le_add_of_nonneg_right (by omega)))
  have hcardReal :
      ((Finset.Icc ⌈a⌉ ⌊b⌋).card : ℝ) =
        ((⌊b⌋ + 1 - ⌈a⌉ : ℤ) : ℝ) := by
    exact_mod_cast hcardInt
  rw [hcardReal]
  push_cast
  linarith

/- Proof idea: compare integer windows. -/
theorem frequency_intervalCount_error_le_four (alpha : ℝ) (beta : ℚ)
    (hbetaSmall : |(beta : ℝ)| < 1 / 2) (x R : ℝ) (hR : 0 ≤ R) :
    (frequencySet alpha beta ∩ Set.Icc x (x + R)).Finite ∧
      |(((intervalCount (frequencySet alpha beta) x R : ℕ) : ℝ) - R)| ≤ 4 := by
  let A : Set ℝ := frequencySet alpha beta ∩ Set.Icc x (x + R)
  let K : Set ℤ := {n : ℤ | (n : ℝ) ∈
    Set.Icc (x + |(beta : ℝ)| / 2) (x + R - |(beta : ℝ)| / 2)}
  let J : Set ℤ := {n : ℤ | (n : ℝ) ∈
    Set.Icc (x - |(beta : ℝ)| / 2) (x + R + |(beta : ℝ)| / 2)}
  have hsand := frequency_preimage_Icc_sandwich alpha beta hbetaSmall x R hR
  have hJfinite : J.Finite := by
    exact integerWindow_finite
      (x - |(beta : ℝ)| / 2) (x + R + |(beta : ℝ)| / 2)
  have hA_subset : A ⊆ frequency alpha beta '' J := by
    intro y hy
    rcases hsand.2 y hy with ⟨n, hn, _⟩
    exact ⟨n, hn.2, hn.1.symm⟩
  have hAfinite : A.Finite :=
    (hJfinite.image (frequency alpha beta)).subset hA_subset
  have hK_subset : frequency alpha beta '' K ⊆ A := by
    rintro _ ⟨n, hn, rfl⟩
    exact hsand.1 ⟨⟨n, hn⟩, rfl⟩
  have hinj := frequency_injective alpha beta hbetaSmall
  have hUpperNat : A.ncard ≤ J.ncard := by
    calc
      A.ncard ≤ (frequency alpha beta '' J).ncard :=
        Set.ncard_le_ncard hA_subset (hJfinite.image _)
      _ = J.ncard := Set.ncard_image_of_injective J hinj
  have hLowerNat : K.ncard ≤ A.ncard := by
    calc
      K.ncard = (frequency alpha beta '' K).ncard :=
        (Set.ncard_image_of_injective K hinj).symm
      _ ≤ A.ncard := Set.ncard_le_ncard hK_subset hAfinite
  have hJlength :
      0 ≤ (x + R + |(beta : ℝ)| / 2) - (x - |(beta : ℝ)| / 2) := by
    nlinarith [abs_nonneg (beta : ℝ)]
  have hJcard := integerWindow_ncard_upper
    (x - |(beta : ℝ)| / 2) (x + R + |(beta : ℝ)| / 2) hJlength
  have hUpperCast : (A.ncard : ℝ) ≤ (J.ncard : ℝ) := by
    exact_mod_cast hUpperNat
  have hUpper : (A.ncard : ℝ) - R ≤ 4 := by
    change ((J.ncard : ℕ) : ℝ) ≤ _ at hJcard
    nlinarith
  have hLowerCast : (K.ncard : ℝ) ≤ (A.ncard : ℝ) := by
    exact_mod_cast hLowerNat
  have hLower : -4 ≤ (A.ncard : ℝ) - R := by
    by_cases hRfour : 4 ≤ R
    · have hKlength :
          2 ≤ (x + R - |(beta : ℝ)| / 2) -
            (x + |(beta : ℝ)| / 2) := by
        linarith
      have hKcard := integerWindow_ncard_lower
        (x + |(beta : ℝ)| / 2) (x + R - |(beta : ℝ)| / 2) hKlength
      change _ ≤ ((K.ncard : ℕ) : ℝ) at hKcard
      change ((K.ncard : ℕ) : ℝ) ≤ ((A.ncard : ℕ) : ℝ) at hLowerCast
      change -4 ≤ ((A.ncard : ℕ) : ℝ) - R
      nlinarith
    · have hAlt : R < 4 := lt_of_not_ge hRfour
      have hAncard : 0 ≤ (A.ncard : ℝ) := Nat.cast_nonneg _
      linarith
  change A.Finite ∧ |(A.ncard : ℝ) - R| ≤ 4
  refine ⟨hAfinite, ?_⟩
  rw [abs_le]
  exact ⟨hLower, hUpper⟩

/- Proof idea: choose R0 above C/epsilon. -/
theorem hasUniformDensity_of_bounded_error (Λ : Set ℝ) (D C : ℝ)
    (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hfinite : ∀ x R : ℝ, 0 ≤ R → (Λ ∩ Set.Icc x (x + R)).Finite)
    (herror : ∀ x R : ℝ, 0 ≤ R →
      |(((intervalCount Λ x R : ℕ) : ℝ) - D * R)| ≤ C) :
    HasUniformDensity Λ D := by
  refine ⟨hD, hfinite, ?_⟩
  intro ε hε
  refine ⟨max 1 (C / ε), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro R hR x
  have hRone : 1 ≤ R := le_trans (le_max_left _ _) hR
  have hRnonneg : 0 ≤ R := le_trans (by norm_num) hRone
  have hCdiv : C / ε ≤ R := le_trans (le_max_right _ _) hR
  have hCbound : C ≤ ε * R := by
    have := (div_le_iff₀ hε).mp hCdiv
    simpa [mul_comm] using this
  exact (herror x R hRnonneg).trans hCbound

end Internal

/- Proof idea: apply bounded error bridge. -/
theorem frequencySet_uniformDensity (alpha : ℝ) (beta : ℚ)
    (hbetaSmall : |(beta : ℝ)| < 1 / 2) :
    HasUniformDensity (frequencySet alpha beta) 1 := by
  apply Internal.hasUniformDensity_of_bounded_error
      (frequencySet alpha beta) 1 4 (by norm_num) (by norm_num)
  · intro x R hR
    exact (Internal.frequency_intervalCount_error_le_four
      alpha beta hbetaSmall x R hR).1
  · intro x R hR
    simpa using (Internal.frequency_intervalCount_error_le_four
      alpha beta hbetaSmall x R hR).2

end Theorem12
