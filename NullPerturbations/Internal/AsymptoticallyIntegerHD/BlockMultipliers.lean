import AsymptoticallyIntegerHD.Definitions
import AsymptoticallyIntegerHD.ThinInterpolation
import AsymptoticallyIntegerHD.DyadicBlocks
import Mathlib.Algebra.MonoidAlgebra.Support

/-! # Exceptional and coordinate block multipliers

The finite-shift return package has a helper type, so `blockShiftFinset`
remains the value-producing declaration used by its consumers.
-/

noncomputable section

open Set
open scoped BigOperators Pointwise

namespace AsymptoticallyIntegerHD

namespace Internal

private theorem phase_eq_one_iff_integer (x : Real) :
    Complex.exp ((((2 * Real.pi * x : Real)) : Complex) * Complex.I) = 1 ↔
      ∃ n : Int, x = n := by
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hpi : (2 * Real.pi : Real) ≠ 0 := by positivity
    apply (mul_left_cancel₀ hpi)
    have him : 2 * Real.pi * x = (n : Real) * (2 * Real.pi) := by
      simpa using congrArg Complex.im hn
    simpa [mul_comm] using him
  · rintro ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    push_cast
    ring

/-- Central frequencies requiring a nonintegral root factor. -/
def exceptionalFinset {d : Nat} {delta : IntVec d → RealVec d}
    (data : ModifiedFrequencyData delta) : Finset (IntVec d) := by
  classical
  exact data.C0.filter fun n => ¬ IsIntegralVector (frequency delta n)

/-- Deterministic coordinate/root data for one exception. -/
structure RootFactorData {d : Nat} {delta : IntVec d → RealVec d}
    (data : ModifiedFrequencyData delta)
    (a : {n : IntVec d // n ∈ exceptionalFinset data}) where
  r : Fin d
  r_bad :
    Complex.exp ((((2 * Real.pi * frequency delta a.1 r : Real)) : Complex) *
      Complex.I) ≠ 1
  r_least : ∀ i,
    Complex.exp ((((2 * Real.pi * frequency delta a.1 i : Real)) : Complex) *
      Complex.I) ≠ 1 → r.val ≤ i.val
  q : Complex
  q_eq : q = Complex.exp
    ((((2 * Real.pi * frequency delta a.1 r : Real)) : Complex) * Complex.I)
  q_ne_one : q ≠ 1
  norm_q : ‖q‖ = 1

/-- Existence theorem for the deterministic realization of `RootFactorData`. -/
theorem rootFactorData_nonempty {d : Nat} {delta : IntVec d → RealVec d}
    (data : ModifiedFrequencyData delta)
    (a : {n : IntVec d // n ∈ exceptionalFinset data}) :
    Nonempty (RootFactorData data a) := by
  classical
  have hnotIntegral : ¬ IsIntegralVector (frequency delta a.1) :=
    (Finset.mem_filter.mp a.2).2
  have hexists : ∃ i : Fin d,
      Complex.exp ((((2 * Real.pi * frequency delta a.1 i : Real)) : Complex) *
        Complex.I) ≠ 1 := by
    by_contra h
    simp only [not_exists, not_not] at h
    apply hnotIntegral
    let n : IntVec d := fun i => Classical.choose
      ((phase_eq_one_iff_integer (frequency delta a.1 i)).mp (h i))
    refine ⟨n, ?_⟩
    funext i
    exact Classical.choose_spec
      ((phase_eq_one_iff_integer (frequency delta a.1 i)).mp (h i))
  let bad : Finset (Fin d) := Finset.univ.filter fun i =>
    Complex.exp ((((2 * Real.pi * frequency delta a.1 i : Real)) : Complex) *
      Complex.I) ≠ 1
  have hbad : bad.Nonempty := by
    obtain ⟨i, hi⟩ := hexists
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  let r : Fin d := bad.min' hbad
  have hrbad : Complex.exp
      ((((2 * Real.pi * frequency delta a.1 r : Real)) : Complex) * Complex.I) ≠ 1 :=
    (Finset.mem_filter.mp (bad.min'_mem hbad)).2
  let q : Complex := Complex.exp
    ((((2 * Real.pi * frequency delta a.1 r : Real)) : Complex) * Complex.I)
  refine ⟨{
    r := r
    r_bad := hrbad
    r_least := ?_
    q := q
    q_eq := rfl
    q_ne_one := hrbad
    norm_q := ?_ }⟩
  · intro i hi
    exact_mod_cast bad.min'_le i
      (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
  · rw [Complex.norm_exp]
    simp

/-- Deterministic realization of `RootFactorData` used by the finite product. -/
noncomputable def rootFactorData {d : Nat} {delta : IntVec d → RealVec d}
    (data : ModifiedFrequencyData delta)
    (a : {n : IntVec d // n ∈ exceptionalFinset data}) :
    RootFactorData data a :=
  Classical.choice (rootFactorData_nonempty data a)

/-- Product of the cached exceptional coordinate factors. -/
noncomputable def exceptionalMultiplier {d : Nat}
    {delta : IntVec d → RealVec d} (data : ModifiedFrequencyData delta)
    (xi : RealVec d) : Complex :=
  Finset.univ.prod fun a : {n : IntVec d // n ∈ exceptionalFinset data} =>
    fourierChar xi (basisVector (rootFactorData data a).r) -
      (rootFactorData data a).q

end Internal

private theorem fourierChar_basisVector {d : Nat} (xi : RealVec d) (r : Fin d) :
    fourierChar xi (basisVector r) =
      Complex.exp ((((2 * Real.pi * xi r : Real)) : Complex) * Complex.I) := by
  rw [fourierChar]
  congr 1
  push_cast
  have hsum :
      (∑ i : Fin d, (xi i : Complex) * (basisVector r i : Complex)) = xi r := by
    rw [Finset.sum_eq_single r]
    · simp [basisVector]
    · intro b _ hbr
      simp [basisVector, hbr]
    · simp
  rw [hsum]
  ring_nf

private theorem fourierChar_integerEmbed_basisVector {d : Nat}
    (m : IntVec d) (r : Fin d) :
    fourierChar (integerEmbed m) (basisVector r) = 1 := by
  rw [fourierChar_basisVector]
  simp only [integerEmbed_apply]
  convert Complex.exp_int_mul_two_pi_mul_I (m r) using 1
  push_cast
  ring_nf

/-- Exceptional roots and the common nonzero integer value. -/
theorem exceptionalMultiplier_roots {d : Nat}
    {delta : IntVec d → RealVec d} (data : Internal.ModifiedFrequencyData delta) :
    (∀ n ∈ Internal.exceptionalFinset data,
      Internal.exceptionalMultiplier data (frequency delta n) = 0) ∧
    (∀ m : IntVec d,
      Internal.exceptionalMultiplier data (integerEmbed m) =
        Finset.univ.prod fun a :
          {n : IntVec d // n ∈ Internal.exceptionalFinset data} =>
            (1 - (Internal.rootFactorData data a).q)) ∧
    (Finset.univ.prod fun a :
      {n : IntVec d // n ∈ Internal.exceptionalFinset data} =>
        (1 - (Internal.rootFactorData data a).q)) ≠ 0 := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    rw [Internal.exceptionalMultiplier]
    let a : {n : IntVec d // n ∈ Internal.exceptionalFinset data} := ⟨n, hn⟩
    apply Finset.prod_eq_zero (Finset.mem_univ a)
    rw [fourierChar_basisVector, (Internal.rootFactorData data a).q_eq]
    simp [a]
  · intro m
    rw [Internal.exceptionalMultiplier]
    apply Finset.prod_congr rfl
    intro a _ha
    rw [fourierChar_integerEmbed_basisVector]
  · apply Finset.prod_ne_zero_iff.mpr
    intro a _ha
    exact sub_ne_zero.mpr (Ne.symm (Internal.rootFactorData data a).q_ne_one)

namespace Internal

private theorem fourierChar_integerEmbed_zero {d : Nat} (xi : RealVec d) :
    fourierChar xi (integerEmbed (0 : IntVec d)) = 1 := by
  simp [fourierChar, integerEmbed]

private theorem fourierChar_integerEmbed_add {d : Nat} (xi : RealVec d)
    (a b : IntVec d) :
    fourierChar xi (integerEmbed (a + b)) =
      fourierChar xi (integerEmbed a) * fourierChar xi (integerEmbed b) := by
  rw [fourierChar, fourierChar, fourierChar, ← Complex.exp_add]
  congr 1
  push_cast
  simp only [Pi.add_apply, integerEmbed_apply, Int.cast_add]
  push_cast
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  ring

private noncomputable def fourierCharacterHom {d : Nat} (xi : RealVec d) :
    Multiplicative (IntVec d) →* Complex where
  toFun a := fourierChar xi (integerEmbed a.toAdd)
  map_one' := fourierChar_integerEmbed_zero xi
  map_mul' a b := fourierChar_integerEmbed_add xi a.toAdd b.toAdd

private noncomputable def fourierEvaluation {d : Nat} (xi : RealVec d) :
    AddMonoidAlgebra Complex (IntVec d) →ₐ[Complex] Complex :=
  AddMonoidAlgebra.lift Complex Complex (IntVec d) (fourierCharacterHom xi)

private theorem fourierEvaluation_apply {d : Nat} (xi : RealVec d)
    (c : AddMonoidAlgebra Complex (IntVec d)) :
    fourierEvaluation xi c =
      c.support.sum fun a => c a * fourierChar xi (integerEmbed a) := by
  rw [fourierEvaluation, AddMonoidAlgebra.lift_apply]
  simp only [smul_eq_mul, fourierCharacterHom]
  rfl

private noncomputable def exceptionalCoeffFactor {d : Nat}
    {delta : IntVec d → RealVec d} (data : ModifiedFrequencyData delta)
    (a : {n : IntVec d // n ∈ exceptionalFinset data}) :
    AddMonoidAlgebra Complex (IntVec d) :=
  AddMonoidAlgebra.single (intBasisVector (rootFactorData data a).r) 1 -
    AddMonoidAlgebra.single 0 (rootFactorData data a).q

private noncomputable def exceptionalCoeff {d : Nat}
    {delta : IntVec d → RealVec d} (data : ModifiedFrequencyData delta) :
    AddMonoidAlgebra Complex (IntVec d) :=
  Finset.univ.prod (exceptionalCoeffFactor data)

private theorem fourierEvaluation_exceptionalCoeffFactor {d : Nat}
    {delta : IntVec d → RealVec d} (data : ModifiedFrequencyData delta)
    (a : {n : IntVec d // n ∈ exceptionalFinset data}) (xi : RealVec d) :
    fourierEvaluation xi (exceptionalCoeffFactor data a) =
      fourierChar xi (basisVector (rootFactorData data a).r) -
        (rootFactorData data a).q := by
  rw [exceptionalCoeffFactor, map_sub]
  simp [fourierEvaluation, fourierCharacterHom, integerEmbed_intBasisVector,
    fourierChar_integerEmbed_zero]

private theorem exceptionalCoeff_evaluation {d : Nat}
    {delta : IntVec d → RealVec d} (data : ModifiedFrequencyData delta)
    (xi : RealVec d) :
    ((exceptionalCoeff data).support.sum fun a =>
        exceptionalCoeff data a * fourierChar xi (integerEmbed a)) =
      exceptionalMultiplier data xi := by
  rw [← fourierEvaluation_apply xi (exceptionalCoeff data)]
  rw [exceptionalCoeff, map_prod, exceptionalMultiplier]
  apply Finset.prod_congr rfl
  intro a _ha
  exact fourierEvaluation_exceptionalCoeffFactor data a xi

private theorem exceptionalCoeffFactor_support {d : Nat}
    {delta : IntVec d → RealVec d} (data : ModifiedFrequencyData delta)
    (a : {n : IntVec d // n ∈ exceptionalFinset data}) :
    (exceptionalCoeffFactor data a).support.card ≤ 2 ∧
      ∀ v ∈ (exceptionalCoeffFactor data a).support, ∀ i,
        0 ≤ v i ∧ v i ≤ 1 := by
  classical
  have hsubset : (exceptionalCoeffFactor data a).support ⊆
      {intBasisVector (rootFactorData data a).r} ∪ {0} := by
    intro v hv
    have hv' := Finsupp.support_sub hv
    rcases Finset.mem_union.mp hv' with hv' | hv'
    · exact Finset.mem_union.mpr
        (Or.inl (Finsupp.support_single_subset hv'))
    · exact Finset.mem_union.mpr
        (Or.inr (Finsupp.support_single_subset hv'))
  constructor
  · calc
      (exceptionalCoeffFactor data a).support.card ≤
          (({intBasisVector (rootFactorData data a).r} : Finset (IntVec d)) ∪
            {0}).card :=
        Finset.card_le_card hsubset
      _ ≤ ({intBasisVector (rootFactorData data a).r} : Finset (IntVec d)).card +
          ({0} : Finset (IntVec d)).card := Finset.card_union_le _ _
      _ = 2 := by simp
  · intro v hv i
    have hv' := hsubset hv
    simp only [Finset.mem_union, Finset.mem_singleton] at hv'
    rcases hv' with rfl | rfl
    · simp only [intBasisVector_apply]
      split <;> omega
    · simp

private theorem exceptionalCoeffOn_support {d : Nat}
    {delta : IntVec d → RealVec d} (data : ModifiedFrequencyData delta)
    (s : Finset {n : IntVec d // n ∈ exceptionalFinset data}) :
    (s.prod (exceptionalCoeffFactor data)).support.card ≤ 2 ^ s.card ∧
      ∀ v ∈ (s.prod (exceptionalCoeffFactor data)).support, ∀ i,
        0 ≤ v i ∧ v i ≤ (s.card : Int) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      have hfactor := exceptionalCoeffFactor_support data a
      constructor
      · calc
          (exceptionalCoeffFactor data a * s.prod (exceptionalCoeffFactor data)).support.card ≤
              ((exceptionalCoeffFactor data a).support +
                (s.prod (exceptionalCoeffFactor data)).support).card :=
            Finset.card_le_card (AddMonoidAlgebra.support_mul _ _)
          _ ≤ (exceptionalCoeffFactor data a).support.card *
                (s.prod (exceptionalCoeffFactor data)).support.card :=
            Finset.card_add_le
          _ ≤ 2 * 2 ^ s.card := Nat.mul_le_mul hfactor.1 ih.1
          _ = 2 ^ (insert a s).card := by
            simp [Finset.card_insert_of_notMem ha, pow_succ, mul_comm]
      · intro v hv i
        have hvsum := AddMonoidAlgebra.support_mul
          (exceptionalCoeffFactor data a) (s.prod (exceptionalCoeffFactor data)) hv
        obtain ⟨y, hy, z, hz, hyz⟩ := Finset.mem_add.mp hvsum
        have hyb := hfactor.2 y hy i
        have hzb := ih.2 z hz i
        subst v
        simp only [Pi.add_apply]
        rw [Finset.card_insert_of_notMem ha]
        push_cast
        constructor <;> omega

private theorem exceptionalCoeff_support {d : Nat}
    {delta : IntVec d → RealVec d} (data : ModifiedFrequencyData delta) :
    (exceptionalCoeff data).support.card ≤ 2 ^ (exceptionalFinset data).card ∧
      ∀ v ∈ (exceptionalCoeff data).support, ∀ i,
        0 ≤ v i ∧ v i ≤ ((exceptionalFinset data).card : Int) := by
  simpa [exceptionalCoeff] using
    (exceptionalCoeffOn_support data
      (Finset.univ : Finset {n : IntVec d // n ∈ exceptionalFinset data}))

private noncomputable def nearExceptionalMultiplier {d : Nat}
    {delta : IntVec d → RealVec d} (data : ModifiedFrequencyData delta)
    (v : RealVec d) : Complex :=
  Finset.univ.prod fun a : {n : IntVec d // n ∈ exceptionalFinset data} =>
    Complex.exp ((((2 * Real.pi * v (rootFactorData data a).r : Real)) : Complex) *
      Complex.I) - (rootFactorData data a).q

private theorem fourierChar_frequency_basisVector_eq {d : Nat}
    (delta : IntVec d → RealVec d) (n : IntVec d) (r : Fin d) :
    fourierChar (frequency delta n) (basisVector r) =
      Complex.exp ((((2 * Real.pi * delta n r : Real)) : Complex) * Complex.I) := by
  rw [fourierChar]
  have hsum : (∑ i : Fin d, frequency delta n i * basisVector r i) =
      frequency delta n r := by
    rw [Finset.sum_eq_single r]
    · simp [basisVector]
    · intro b _ hbr
      simp [basisVector, hbr]
    · simp
  rw [hsum, frequency_apply]
  have harg :
      ((((2 * Real.pi : Real) : Complex) * Complex.I *
        (((n r : Real) + delta n r : Real) : Complex))) =
        ((n r : Int) : Complex) * (2 * (Real.pi : Complex) * Complex.I) +
          ((((2 * Real.pi * delta n r : Real)) : Complex) * Complex.I) := by
    push_cast
    ring
  rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul]

private theorem exceptionalMultiplier_frequency_eq_near {d : Nat}
    {delta : IntVec d → RealVec d} (data : ModifiedFrequencyData delta)
    (n : IntVec d) :
    exceptionalMultiplier data (frequency delta n) =
      nearExceptionalMultiplier data (delta n) := by
  rw [exceptionalMultiplier, nearExceptionalMultiplier]
  apply Finset.prod_congr rfl
  intro a _ha
  rw [fourierChar_frequency_basisVector_eq]

private theorem nearExceptionalMultiplier_zero {d : Nat}
    {delta : IntVec d → RealVec d} (data : ModifiedFrequencyData delta) :
    nearExceptionalMultiplier data 0 =
      Finset.univ.prod fun a :
        {n : IntVec d // n ∈ exceptionalFinset data} =>
          (1 - (rootFactorData data a).q) := by
  rw [nearExceptionalMultiplier]
  apply Finset.prod_congr rfl
  intro a _ha
  simp

private theorem nearExceptionalMultiplier_continuous {d : Nat}
    {delta : IntVec d → RealVec d} (data : ModifiedFrequencyData delta) :
    Continuous (nearExceptionalMultiplier data) := by
  unfold nearExceptionalMultiplier
  fun_prop

private theorem dyadicScale_eq_inv_pow_local (j : Nat) :
    dyadicScale j = ((2 : Real)⁻¹) ^ j := by
  rw [dyadicScale, zpow_neg, zpow_natCast, inv_pow]

private theorem dyadicScale_tendsto_zero_local :
    Filter.Tendsto dyadicScale Filter.atTop (nhds 0) := by
  convert tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : Real) ≤ (2 : Real)⁻¹)
    (by norm_num : (2 : Real)⁻¹ < 1) using 1
  funext j
  exact dyadicScale_eq_inv_pow_local j

private theorem exceptionalMultiplier_global_upper {d : Nat}
    {delta : IntVec d → RealVec d} (data : ModifiedFrequencyData delta)
    (n : IntVec d) :
    ‖exceptionalMultiplier data (frequency delta n)‖ ≤
      (2 : Real) ^ (exceptionalFinset data).card := by
  rw [exceptionalMultiplier_frequency_eq_near, nearExceptionalMultiplier,
    Complex.norm_prod]
  calc
    ∏ a : {n : IntVec d // n ∈ exceptionalFinset data},
        ‖Complex.exp
            (↑(2 * Real.pi * delta n (rootFactorData data a).r) * Complex.I) -
          (rootFactorData data a).q‖ ≤
        ∏ _a : {n : IntVec d // n ∈ exceptionalFinset data}, (2 : Real) := by
      apply Finset.prod_le_prod
      · intro a _ha
        positivity
      · intro a _ha
        calc
          ‖Complex.exp
              (↑(2 * Real.pi * delta n (rootFactorData data a).r) * Complex.I) -
            (rootFactorData data a).q‖ ≤
              ‖Complex.exp
                (↑(2 * Real.pi * delta n (rootFactorData data a).r) * Complex.I)‖ +
                ‖(rootFactorData data a).q‖ := norm_sub_le _ _
          _ = 2 := by
            rw [Complex.norm_exp, (rootFactorData data a).norm_q]
            norm_num
    _ = (2 : Real) ^ (exceptionalFinset data).card := by simp

private theorem exists_exceptionalMultiplier_late_lower {d : Nat}
    (_hd : 0 < d) {delta : IntVec d → RealVec d}
    (hdelta : TendsToZeroAtIntVecInfinity delta)
    (data : ModifiedFrequencyData delta) :
    ∃ lower : Real, 0 < lower ∧ ∃ jSep : Nat, 3 ≤ jSep ∧
      ∀ j n, jSep ≤ j → n ∈ dyadicBlock delta hdelta data.C0 j →
        lower ≤ ‖exceptionalMultiplier data (frequency delta n)‖ := by
  have hbase : nearExceptionalMultiplier data 0 ≠ 0 := by
    rw [nearExceptionalMultiplier_zero]
    exact (exceptionalMultiplier_roots data).2.2
  let lower : Real := ‖nearExceptionalMultiplier data 0‖ / 2
  have hlower : 0 < lower := div_pos (norm_pos_iff.mpr hbase) (by norm_num)
  obtain ⟨rho, hrho, hclose⟩ :=
    (Metric.continuousAt_iff.mp
      (nearExceptionalMultiplier_continuous data).continuousAt)
      lower hlower
  have hEventually : ∀ᶠ j : Nat in Filter.atTop, dyadicScale j < rho :=
    dyadicScale_tendsto_zero_local.eventually (Iio_mem_nhds hrho)
  obtain ⟨J, hJ⟩ := Filter.eventually_atTop.1 hEventually
  let jSep := max 3 J
  refine ⟨lower, hlower, jSep, le_max_left _ _, ?_⟩
  intro j n hj hn
  have hjJ : J ≤ j := (le_max_right 3 J).trans hj
  have hnsmall : ‖delta n‖ < rho :=
    (mem_dyadicBlock_iff.mp hn).2.2.2.trans (hJ j hjJ)
  have hdistInput : dist (delta n) 0 < rho := by
    simpa [dist_eq_norm] using hnsmall
  have hout := hclose hdistInput
  have hnormdiff :
      |‖nearExceptionalMultiplier data (delta n)‖ -
          ‖nearExceptionalMultiplier data 0‖| ≤
        dist (nearExceptionalMultiplier data (delta n))
          (nearExceptionalMultiplier data 0) := by
    simpa [dist_eq_norm] using
      abs_norm_sub_norm_le (nearExceptionalMultiplier data (delta n))
        (nearExceptionalMultiplier data 0)
  rw [exceptionalMultiplier_frequency_eq_near]
  dsimp [lower] at hout ⊢
  have hleft := (abs_le.mp hnormdiff).1
  nlinarith

/-- Uniform exceptional separation and finite expansion data. -/
structure ExceptionalConstants {d : Nat} (hd : 0 < d)
    (delta : IntVec d → RealVec d)
    (hdelta : TendsToZeroAtIntVecInfinity delta)
    (data : ModifiedFrequencyData delta) {mu0 : Real}
    (P : BlockParameters hd delta hdelta data mu0) where
  lower : Real
  lower_pos : 0 < lower
  upper : Real
  upper_pos : 0 < upper
  shiftUpper : Fin d → Nat
  jSep : Nat
  three_le_jSep : 3 ≤ jSep
  multiplier_bounds : ∀ j n,
    jSep ≤ j → n ∈ dyadicBlock delta hdelta data.C0 j →
      lower ≤ ‖exceptionalMultiplier data (frequency delta n)‖ ∧
        ‖exceptionalMultiplier data (frequency delta n)‖ ≤ upper
  coeff : Finsupp (IntVec d) Complex
  coeff_evaluation : ∀ xi,
    (coeff.support.sum fun a => coeff a * fourierChar xi (integerEmbed a)) =
      exceptionalMultiplier data xi
  coeff_sq_le : (coeff.support.sum fun a => ‖coeff a‖ ^ 2) ≤ upper ^ 2
  coeff_card_le : coeff.support.card ≤
    2 ^ (exceptionalFinset data).card
  coeff_coordinate_bounds : ∀ a ∈ coeff.support, ∀ i,
    0 ≤ a i ∧ a i ≤ (shiftUpper i : Int)

/-- Existence theorem for the fixed exceptional constants. -/
theorem exceptionalConstants_nonempty {d : Nat} (hd : 0 < d)
    (delta : IntVec d → RealVec d)
    (hdelta : TendsToZeroAtIntVecInfinity delta)
    (data : ModifiedFrequencyData delta) {mu0 : Real}
    (P : BlockParameters hd delta hdelta data mu0) :
    Nonempty (ExceptionalConstants hd delta hdelta data P) := by
  classical
  obtain ⟨lower, hlower, jSep, hjSep, hlate⟩ :=
    exists_exceptionalMultiplier_late_lower hd hdelta data
  let coeff : Finsupp (IntVec d) Complex := exceptionalCoeff data
  let energy : Real := coeff.support.sum fun a => ‖coeff a‖ ^ 2
  let global : Real := (2 : Real) ^ (exceptionalFinset data).card
  let upper : Real := 1 + global + energy
  have henergy : 0 ≤ energy := by
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hglobal : 0 ≤ global := by
    exact pow_nonneg (by norm_num) _
  have hupper : 0 < upper := by
    dsimp [upper]
    linarith
  have henergySq : energy ≤ upper ^ 2 := by
    have henergyUpper : energy ≤ upper := by
      dsimp [upper]
      linarith
    have honeUpper : 1 ≤ upper := by
      dsimp [upper]
      linarith
    have hmul : 0 ≤ upper * (upper - 1) :=
      mul_nonneg hupper.le (sub_nonneg.mpr honeUpper)
    nlinarith
  refine ⟨{
    lower := lower
    lower_pos := hlower
    upper := upper
    upper_pos := hupper
    shiftUpper := fun _ => (exceptionalFinset data).card
    jSep := jSep
    three_le_jSep := hjSep
    multiplier_bounds := ?_
    coeff := coeff
    coeff_evaluation := ?_
    coeff_sq_le := ?_
    coeff_card_le := ?_
    coeff_coordinate_bounds := ?_ }⟩
  · intro j n hj hn
    refine ⟨hlate j n hj hn, ?_⟩
    have h := exceptionalMultiplier_global_upper data n
    dsimp [upper, global]
    exact h.trans (by linarith)
  · intro xi
    simpa [coeff] using exceptionalCoeff_evaluation data xi
  · simpa [coeff, energy] using henergySq
  · simpa [coeff] using (exceptionalCoeff_support data).1
  · intro a ha i
    simpa [coeff] using (exceptionalCoeff_support data).2 a ha i

/-- Construct the fixed exceptional constants. -/
noncomputable def exceptionalConstants {d : Nat} (hd : 0 < d)
    (delta : IntVec d → RealVec d)
    (hdelta : TendsToZeroAtIntVecInfinity delta)
    (data : ModifiedFrequencyData delta) {mu0 : Real}
    (P : BlockParameters hd delta hdelta data mu0) :
    ExceptionalConstants hd delta hdelta data P :=
  Classical.choice (exceptionalConstants_nonempty hd delta hdelta data P)

end Internal

/-- Integer dyadic translation step. -/
def dyadicStep (j : Nat) : Int := ((2 ^ (j - 1) : Nat) : Int)

/-- Selected-coordinate dyadic character multiplier. -/
def dyadicMultiplier {d : Nat} (j : Nat) (r : Fin d) (xi : RealVec d) :
    Complex :=
  fourierChar xi ((dyadicStep j : Real) • basisVector r) - 1

/-- Combined exceptional and selected-coordinate multiplier. -/
noncomputable def blockMultiplier {d : Nat}
    {delta : IntVec d → RealVec d} (data : Internal.ModifiedFrequencyData delta)
    (j : Nat) (r : Fin d) (xi : RealVec d) : Complex :=
  Internal.exceptionalMultiplier data xi * dyadicMultiplier j r xi

private theorem fourierChar_smul_basisVector {d : Nat}
    (xi : RealVec d) (c : Real) (r : Fin d) :
    fourierChar xi (c • basisVector r) =
      Complex.exp ((((2 * Real.pi * (c * xi r) : Real)) : Complex) * Complex.I) := by
  rw [fourierChar]
  congr 1
  push_cast
  have hsum :
      (∑ i : Fin d, (xi i : Complex) * ((c • basisVector r) i : Complex)) =
        (c : Complex) * xi r := by
    rw [Finset.sum_eq_single r]
    · simp [basisVector, mul_comm]
    · intro b _ hbr
      simp [basisVector, hbr]
    · simp
  rw [hsum]
  ring_nf

private theorem dyadicMultiplier_frequency_eq {d : Nat}
    (delta : IntVec d → RealVec d) (n : IntVec d) (j : Nat) (r : Fin d) :
    dyadicMultiplier j r (frequency delta n) =
      Complex.exp ((((2 * Real.pi * ((dyadicStep j : Real) * delta n r) : Real)) :
        Complex) * Complex.I) - 1 := by
  rw [dyadicMultiplier, fourierChar_smul_basisVector, frequency_apply]
  have harg :
      ((((2 * Real.pi * ((dyadicStep j : Real) * ((n r : Real) + delta n r)) :
          Real)) : Complex) * Complex.I) =
        ((dyadicStep j * n r : Int) : Complex) *
            (2 * (Real.pi : Complex) * Complex.I) +
          ((((2 * Real.pi * ((dyadicStep j : Real) * delta n r) : Real)) :
            Complex) * Complex.I) := by
    push_cast
    ring
  rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul]

private theorem norm_exp_mul_I_sub_one_ge_one {theta : Real}
    (hlower : Real.pi / 2 ≤ |theta|)
    (hupper : |theta| ≤ 3 * Real.pi / 2) :
    1 ≤ ‖Complex.exp ((theta : Complex) * Complex.I) - 1‖ := by
  rw [mul_comm, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs,
    abs_mul, abs_of_pos (by norm_num : (0 : Real) < 2)]
  rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi]
  · have hx0 : Real.pi / 4 ≤ |theta / 2| := by
      rw [abs_div]
      nlinarith
    have hx1 : |theta / 2| ≤ 3 * Real.pi / 4 := by
      rw [abs_div]
      nlinarith
    rcases le_total |theta / 2| (Real.pi / 2) with hxmid | hxmid
    · have hs : Real.sin (Real.pi / 6) ≤ Real.sin |theta / 2| :=
        Real.sin_le_sin_of_le_of_le_pi_div_two (by nlinarith [Real.pi_pos]) hxmid
          (by nlinarith [Real.pi_pos])
      rw [Real.sin_pi_div_six] at hs
      nlinarith
    · have hy0 : Real.pi / 6 ≤ Real.pi - |theta / 2| := by
        nlinarith [Real.pi_pos]
      have hy1 : Real.pi - |theta / 2| ≤ Real.pi / 2 := by linarith
      have hs : Real.sin (Real.pi / 6) ≤
          Real.sin (Real.pi - |theta / 2|) :=
        Real.sin_le_sin_of_le_of_le_pi_div_two (by nlinarith [Real.pi_pos]) hy1
          (by nlinarith [Real.pi_pos])
      rw [Real.sin_pi_div_six, Real.sin_pi_sub] at hs
      nlinarith
  · rw [abs_div]
    nlinarith [Real.pi_pos]

private theorem dyadicMultiplier_upper {d : Nat}
    (delta : IntVec d → RealVec d) (n : IntVec d) (j : Nat) (r : Fin d) :
    ‖dyadicMultiplier j r (frequency delta n)‖ ≤
      2 * Real.pi * (2 : Real) ^ (j - 1) * ‖delta n‖ := by
  rw [dyadicMultiplier_frequency_eq]
  let theta : Real := 2 * Real.pi * ((dyadicStep j : Real) * delta n r)
  have hexp :
      ‖Complex.exp ((theta : Complex) * Complex.I) - 1‖ ≤ |theta| := by
    simpa [mul_comm, Real.norm_eq_abs] using
      (Real.norm_exp_I_mul_ofReal_sub_one_le (x := theta))
  have hcoord : |delta n r| ≤ ‖delta n‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm (delta n) r
  have hstep : (dyadicStep j : Real) = (2 : Real) ^ (j - 1) := by
    simp [dyadicStep]
  calc
    ‖Complex.exp
        (↑(2 * Real.pi * (↑(dyadicStep j) * delta n r)) * Complex.I) - 1‖ =
        ‖Complex.exp ((theta : Complex) * Complex.I) - 1‖ := by rfl
    _ ≤ |theta| := hexp
    _ = 2 * Real.pi * (2 : Real) ^ (j - 1) * |delta n r| := by
      dsimp [theta]
      rw [hstep]
      rw [show 2 * Real.pi * (2 ^ (j - 1) * delta n r) =
          (2 * Real.pi * 2 ^ (j - 1)) * delta n r by ring]
      rw [abs_mul, abs_of_nonneg (by positivity :
        0 ≤ 2 * Real.pi * (2 : Real) ^ (j - 1))]
    _ ≤ 2 * Real.pi * (2 : Real) ^ (j - 1) * ‖delta n‖ :=
      mul_le_mul_of_nonneg_left hcoord
        (mul_nonneg (by positivity) (pow_nonneg (by norm_num) _))

private theorem dyadic_power_bound (j k : Nat) :
    2 * Real.pi * (2 : Real) ^ (j - 1) * dyadicScale k ≤
      4 * Real.pi * (2 : Real) ^ ((j : Int) - (k : Int)) := by
  have hpow : (2 : Real) ^ (j - 1) ≤ (2 : Real) ^ j := by
    exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le j 1)
  have hcombine : (2 : Real) ^ j * dyadicScale k =
      (2 : Real) ^ ((j : Int) - (k : Int)) := by
    rw [dyadicScale]
    rw [← zpow_natCast]
    rw [← zpow_add₀ (by norm_num : (2 : Real) ≠ 0)]
    congr 2
  calc
    2 * Real.pi * (2 : Real) ^ (j - 1) * dyadicScale k ≤
        2 * Real.pi * (2 : Real) ^ j * dyadicScale k := by
      apply mul_le_mul_of_nonneg_right _ (by unfold dyadicScale; positivity)
      exact mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = 2 * Real.pi * (2 : Real) ^ ((j : Int) - (k : Int)) := by
      rw [mul_assoc, hcombine]
    _ ≤ 4 * Real.pi * (2 : Real) ^ ((j : Int) - (k : Int)) := by
      apply mul_le_mul_of_nonneg_right _ (zpow_nonneg (by norm_num) _)
      nlinarith [Real.pi_pos]

private theorem dyadicMultiplier_future_upper {d : Nat}
    {delta : IntVec d → RealVec d}
    {hdelta : TendsToZeroAtIntVecInfinity delta}
    {C0 : Finset (IntVec d)}
    (j k : Nat) (r : Fin d) (n : IntVec d)
    (hn : n ∈ dyadicBlock delta hdelta C0 k) :
    ‖dyadicMultiplier j r (frequency delta n)‖ ≤
      4 * Real.pi * (2 : Real) ^ ((j : Int) - (k : Int)) := by
  have hnupper : ‖delta n‖ ≤ dyadicScale k :=
    (mem_dyadicBlock_iff.mp hn).2.2.2.le
  calc
    ‖dyadicMultiplier j r (frequency delta n)‖ ≤
        2 * Real.pi * (2 : Real) ^ (j - 1) * ‖delta n‖ :=
      dyadicMultiplier_upper delta n j r
    _ ≤ 2 * Real.pi * (2 : Real) ^ (j - 1) * dyadicScale k := by
      gcongr
    _ ≤ 4 * Real.pi * (2 : Real) ^ ((j : Int) - (k : Int)) :=
      dyadic_power_bound j k

private theorem dyadicStep_mul_next_scale (j : Nat) (hj : 1 ≤ j) :
    (dyadicStep j : Real) * dyadicScale (j + 1) = 1 / 4 := by
  rw [dyadicStep, dyadicScale]
  push_cast
  rw [← zpow_natCast]
  rw [← zpow_add₀ (by norm_num : (2 : Real) ≠ 0)]
  rw [show ((j - 1 : Nat) : Int) + -((j : Int) + 1) = -2 by omega]
  norm_num

private theorem dyadicStep_mul_scale (j : Nat) (hj : 1 ≤ j) :
    (dyadicStep j : Real) * dyadicScale j = 1 / 2 := by
  rw [dyadicStep, dyadicScale]
  push_cast
  rw [← zpow_natCast]
  rw [← zpow_add₀ (by norm_num : (2 : Real) ≠ 0)]
  rw [show ((j - 1 : Nat) : Int) + -(j : Int) = -1 by omega]
  norm_num

/-- Current lower and future upper multiplier estimates. -/
theorem blockMultiplier_bounds {d : Nat} (hd : 0 < d)
    {delta : IntVec d → RealVec d}
    {hdelta : TendsToZeroAtIntVecInfinity delta}
    {data : Internal.ModifiedFrequencyData delta} {mu0 : Real}
    {P : Internal.BlockParameters hd delta hdelta data mu0}
    (EC : Internal.ExceptionalConstants hd delta hdelta data P) :
    (∀ j r n, EC.jSep ≤ j →
      n ∈ coordinateBlock delta hdelta data.C0 hd j r →
        EC.lower ≤ ‖blockMultiplier data j r (frequency delta n)‖) ∧
    (∀ j k r n, n ∈ dyadicBlock delta hdelta data.C0 k →
      ‖dyadicMultiplier j r (frequency delta n)‖ ≤
        2 * Real.pi * (2 : Real) ^ (j - 1) * ‖delta n‖) ∧
    (∀ j k r n, n ∈ dyadicBlock delta hdelta data.C0 k → j ≤ k →
      ‖dyadicMultiplier j r (frequency delta n)‖ ≤
        4 * Real.pi * (2 : Real) ^ ((j : Int) - (k : Int))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro j r n hj hn
    obtain ⟨hnBlock, hselect⟩ := mem_coordinateBlock_iff.mp hn
    have hnzero : delta n ≠ 0 := (mem_dyadicBlock_iff.mp hnBlock).2.1
    have habs : |delta n r| = ‖delta n‖ := by
      simpa [hselect] using
        (Internal.maxCoordinate hd (delta n) hnzero).abs_eq_norm
    have hjone : 1 ≤ j := by
      have := EC.three_le_jSep
      omega
    have hprodLower : 1 / 4 ≤ (dyadicStep j : Real) * ‖delta n‖ := by
      calc
        1 / 4 = (dyadicStep j : Real) * dyadicScale (j + 1) :=
          (dyadicStep_mul_next_scale j hjone).symm
        _ ≤ (dyadicStep j : Real) * ‖delta n‖ :=
          mul_le_mul_of_nonneg_left (mem_dyadicBlock_iff.mp hnBlock).2.2.1
            (by simp [dyadicStep])
    have hprodUpper : (dyadicStep j : Real) * ‖delta n‖ < 1 / 2 := by
      calc
        (dyadicStep j : Real) * ‖delta n‖ <
            (dyadicStep j : Real) * dyadicScale j :=
          mul_lt_mul_of_pos_left (mem_dyadicBlock_iff.mp hnBlock).2.2.2
            (by simp [dyadicStep])
        _ = 1 / 2 := dyadicStep_mul_scale j hjone
    let theta : Real := 2 * Real.pi * ((dyadicStep j : Real) * delta n r)
    have habsTheta : |theta| =
        2 * Real.pi * ((dyadicStep j : Real) * ‖delta n‖) := by
      have hstepNonneg : 0 ≤ (dyadicStep j : Real) := by simp [dyadicStep]
      dsimp [theta]
      rw [show 2 * Real.pi * (↑(dyadicStep j) * delta n r) =
          (2 * Real.pi * (dyadicStep j : Real)) * delta n r by ring]
      rw [abs_mul, abs_of_nonneg
        (mul_nonneg (by positivity) hstepNonneg), habs]
      ring
    have hthetaLower : Real.pi / 2 ≤ |theta| := by
      rw [habsTheta]
      nlinarith [Real.pi_pos]
    have hthetaUpper : |theta| ≤ 3 * Real.pi / 2 := by
      rw [habsTheta]
      nlinarith [Real.pi_pos]
    have hdyadic : 1 ≤ ‖dyadicMultiplier j r (frequency delta n)‖ := by
      rw [dyadicMultiplier_frequency_eq]
      exact norm_exp_mul_I_sub_one_ge_one hthetaLower hthetaUpper
    rw [blockMultiplier, norm_mul]
    have hexceptional := (EC.multiplier_bounds j n hj hnBlock).1
    exact hexceptional.trans
      (le_mul_of_one_le_right (norm_nonneg _) hdyadic)
  · intro j _k r n _hn
    exact dyadicMultiplier_upper delta n j r
  · intro j k r n hn _hjk
    exact dyadicMultiplier_future_upper j k r n hn

namespace Internal

/-- Integer vector implementing the selected-coordinate dyadic translation. -/
def dyadicShiftVector {d : Nat} (j : Nat) (r : Fin d) : IntVec d :=
  fun i => dyadicStep j * intBasisVector r i

/-- Transparent collected coefficients of the exceptional/dyadic product. -/
noncomputable def blockShiftCoefficients {d : Nat}
    {delta : IntVec d → RealVec d} (data : ModifiedFrequencyData delta)
    {hd : 0 < d} {hdelta : TendsToZeroAtIntVecInfinity delta} {mu0 : Real}
    {P : BlockParameters hd delta hdelta data mu0}
    (EC : ExceptionalConstants hd delta hdelta data P)
    (j : Nat) (r : Fin d) : Finsupp (IntVec d) Complex :=
  EC.coeff.sum fun a z =>
    Finsupp.single (a + dyadicShiftVector j r) z - Finsupp.single a z

private def addRight {d : Nat} (s : IntVec d) (a : IntVec d) : IntVec d :=
  a + s

private theorem addRight_injective {d : Nat} (s : IntVec d) :
    Function.Injective (addRight s) := fun _ _ h => add_right_cancel h

private noncomputable def shiftCoeff {d : Nat}
    (c : Finsupp (IntVec d) Complex) (s : IntVec d) :
    Finsupp (IntVec d) Complex :=
  Finsupp.mapDomain (addRight s) c

private theorem shiftCoeff_eq_sum {d : Nat}
    (c : Finsupp (IntVec d) Complex) (s : IntVec d) :
    shiftCoeff c s = c.sum fun a z => Finsupp.single (a + s) z := by
  rfl

private theorem shiftCoeff_sub_eq_sum {d : Nat}
    (c : Finsupp (IntVec d) Complex) (s : IntVec d) :
    shiftCoeff c s - c =
      c.sum fun a z => Finsupp.single (a + s) z - Finsupp.single a z := by
  rw [Finsupp.sum_sub, shiftCoeff_eq_sum, Finsupp.sum_single]

private theorem shiftCoeff_support {d : Nat}
    (c : Finsupp (IntVec d) Complex) (s : IntVec d) :
    (shiftCoeff c s).support = c.support.image (addRight s) := by
  rw [shiftCoeff]
  exact Finsupp.mapDomain_support_of_injOn c (addRight_injective s).injOn

private theorem shiftCoeff_apply {d : Nat}
    (c : Finsupp (IntVec d) Complex) (s a : IntVec d) :
    shiftCoeff c s (a + s) = c a := by
  exact Finsupp.mapDomain_apply (addRight_injective s) c a

private theorem shiftCoeff_card {d : Nat}
    (c : Finsupp (IntVec d) Complex) (s : IntVec d) :
    (shiftCoeff c s).support.card = c.support.card := by
  rw [shiftCoeff_support]
  exact Finset.card_image_of_injective _ (addRight_injective s)

private theorem shiftCoeff_energy {d : Nat}
    (c : Finsupp (IntVec d) Complex) (s : IntVec d) :
    (shiftCoeff c s).support.sum (fun a => ‖shiftCoeff c s a‖ ^ 2) =
      c.support.sum fun a => ‖c a‖ ^ 2 := by
  rw [shiftCoeff_support]
  rw [Finset.sum_image]
  · simp only [addRight, shiftCoeff_apply]
  · exact (addRight_injective s).injOn

private noncomputable def plainFourierEvaluation {d : Nat} (xi : RealVec d) :
    (IntVec d →₀ Complex) →ₗ[Complex] Complex :=
  Finsupp.lsum Complex fun a =>
    LinearMap.lsmul Complex Complex (fourierChar xi (integerEmbed a))

private theorem plainFourierEvaluation_apply {d : Nat} (xi : RealVec d)
    (c : Finsupp (IntVec d) Complex) :
    plainFourierEvaluation xi c =
      c.support.sum fun a => c a * fourierChar xi (integerEmbed a) := by
  rw [plainFourierEvaluation, Finsupp.lsum_apply]
  simp only [Finsupp.sum, LinearMap.lsmul_apply]
  apply Finset.sum_congr rfl
  intro a _ha
  exact mul_comm _ _

private theorem plainFourierEvaluation_shift {d : Nat}
    (c : Finsupp (IntVec d) Complex) (s : IntVec d) (xi : RealVec d) :
    plainFourierEvaluation xi (shiftCoeff c s) =
      plainFourierEvaluation xi c * fourierChar xi (integerEmbed s) := by
  rw [plainFourierEvaluation_apply, plainFourierEvaluation_apply, shiftCoeff_support]
  rw [Finset.sum_image]
  · rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _ha
    change shiftCoeff c s (a + s) * fourierChar xi (integerEmbed (a + s)) = _
    rw [shiftCoeff_apply, fourierChar_integerEmbed_add]
    ring
  · exact (addRight_injective s).injOn

private theorem fourierEvaluation_shift {d : Nat}
    (c : Finsupp (IntVec d) Complex) (s : IntVec d) (xi : RealVec d) :
    fourierEvaluation xi (shiftCoeff c s) =
      fourierEvaluation xi c * fourierChar xi (integerEmbed s) := by
  rw [fourierEvaluation_apply, fourierEvaluation_apply, shiftCoeff_support]
  rw [Finset.sum_image]
  · rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _ha
    change shiftCoeff c s (a + s) * fourierChar xi (integerEmbed (a + s)) = _
    rw [shiftCoeff_apply, fourierChar_integerEmbed_add]
    ring
  · exact (addRight_injective s).injOn

private theorem shiftCoeff_mem {d : Nat}
    (c : Finsupp (IntVec d) Complex) (s v : IntVec d)
    (hv : v ∈ (shiftCoeff c s).support) :
    ∃ a ∈ c.support, a + s = v := by
  rw [shiftCoeff_support] at hv
  exact Finset.mem_image.mp hv

private theorem intEmbed_dyadicShift {d : Nat} (j : Nat) (r : Fin d) :
    integerEmbed (dyadicShiftVector j r) =
      (dyadicStep j : Real) • basisVector r := by
  ext i
  simp only [integerEmbed_apply, dyadicShiftVector, Pi.smul_apply, smul_eq_mul,
    intBasisVector_apply, basisVector_apply]
  split <;> simp_all

private theorem finsupp_sub_energy_le {α : Type*} [DecidableEq α]
    (p q : Finsupp α Complex) :
    (p - q).support.sum (fun a => ‖(p - q) a‖ ^ 2) ≤
      2 * p.support.sum (fun a => ‖p a‖ ^ 2) +
        2 * q.support.sum (fun a => ‖q a‖ ^ 2) := by
  classical
  let u := p.support ∪ q.support
  have hsupport : (p - q).support ⊆ u := Finsupp.support_sub
  calc
    (p - q).support.sum (fun a => ‖(p - q) a‖ ^ 2) ≤
        u.sum (fun a => ‖(p - q) a‖ ^ 2) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsupport (fun _ _ _ => sq_nonneg _)
    _ ≤ u.sum (fun a => 2 * ‖p a‖ ^ 2 + 2 * ‖q a‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro a _ha
      have hnorm : ‖p a - q a‖ ≤ ‖p a‖ + ‖q a‖ := norm_sub_le _ _
      have hmul := mul_le_mul hnorm hnorm (norm_nonneg _)
        (add_nonneg (norm_nonneg _) (norm_nonneg _))
      simp only [Finsupp.sub_apply]
      nlinarith [sq_nonneg (‖p a‖ - ‖q a‖)]
    _ = 2 * p.support.sum (fun a => ‖p a‖ ^ 2) +
        2 * q.support.sum (fun a => ‖q a‖ ^ 2) := by
      have hp : u.sum (fun a => ‖p a‖ ^ 2) =
          p.support.sum (fun a => ‖p a‖ ^ 2) := by
        symm
        change p.sum (fun a z => ‖z‖ ^ 2) = _
        exact p.sum_of_support_subset Finset.subset_union_left _ (by simp)
      have hq : u.sum (fun a => ‖q a‖ ^ 2) =
          q.support.sum (fun a => ‖q a‖ ^ 2) := by
        symm
        change q.sum (fun a z => ‖z‖ ^ 2) = _
        exact q.sum_of_support_subset Finset.subset_union_right _ (by simp)
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      rw [hp, hq]

/-- Return package for the value-producing `blockShiftFinset` declaration. -/
structure BlockShiftFinsetData {d : Nat}
    {delta : IntVec d → RealVec d} (data : ModifiedFrequencyData delta)
    {hd : 0 < d} {hdelta : TendsToZeroAtIntVecInfinity delta} {mu0 : Real}
    {P : BlockParameters hd delta hdelta data mu0}
    (EC : ExceptionalConstants hd delta hdelta data P)
    (j : Nat) (r : Fin d) where
  coeff : Finsupp (IntVec d) Complex
  coeff_eq : coeff = blockShiftCoefficients data EC j r
  evaluation : ∀ xi,
    (coeff.support.sum fun a => coeff a * fourierChar xi (integerEmbed a)) =
      blockMultiplier data j r xi
  coeff_sq_le : (coeff.support.sum fun a => ‖coeff a‖ ^ 2) ≤ 4 * EC.upper ^ 2
  coeff_card_le : coeff.support.card ≤
    2 ^ ((exceptionalFinset data).card + 1)
  coordinate_bounds : ∀ a ∈ coeff.support, ∀ i,
    0 ≤ a i ∧
      a i ≤ (EC.shiftUpper i : Int) +
        (if i = r then dyadicStep j else 0)
  firstCoordinateUpper : Nat
  firstCoordinateUpper_spec : ∀ a ∈ coeff.support,
    a (firstCoordinate hd) ≤ (firstCoordinateUpper : Int)
  baseEnvelopeWidth : Nat
  baseEnvelopeWidth_eq : baseEnvelopeWidth = firstCoordinateUpper + 1
  differenceEnvelopeWidth : Nat
  differenceEnvelopeWidth_eq : differenceEnvelopeWidth = baseEnvelopeWidth + 1

/-- Existence theorem for the combined finite vector-shift expansion. -/
theorem blockShiftFinsetData_nonempty {d : Nat}
    {delta : IntVec d → RealVec d} (data : ModifiedFrequencyData delta)
    {hd : 0 < d} {hdelta : TendsToZeroAtIntVecInfinity delta} {mu0 : Real}
    {P : BlockParameters hd delta hdelta data mu0}
    (EC : ExceptionalConstants hd delta hdelta data P)
    (j : Nat) (r : Fin d) : Nonempty (BlockShiftFinsetData data EC j r) := by
  classical
  let s : IntVec d := dyadicShiftVector j r
  let shifted : Finsupp (IntVec d) Complex := shiftCoeff EC.coeff s
  let coeff : Finsupp (IntVec d) Complex := shifted - EC.coeff
  have hcoeff : coeff = blockShiftCoefficients data EC j r := by
    dsimp [coeff, shifted, s]
    rw [shiftCoeff_sub_eq_sum]
    rfl
  have hevaluation : ∀ xi,
      (coeff.support.sum fun a => coeff a * fourierChar xi (integerEmbed a)) =
        blockMultiplier data j r xi := by
    intro xi
    rw [← plainFourierEvaluation_apply]
    dsimp [coeff, shifted]
    rw [map_sub, plainFourierEvaluation_shift]
    rw [plainFourierEvaluation_apply, EC.coeff_evaluation]
    rw [show integerEmbed s = (dyadicStep j : Real) • basisVector r by
      simpa [s] using intEmbed_dyadicShift j r]
    simp only [blockMultiplier, dyadicMultiplier]
    ring
  have hsq : (coeff.support.sum fun a => ‖coeff a‖ ^ 2) ≤
      4 * EC.upper ^ 2 := by
    calc
      (coeff.support.sum fun a => ‖coeff a‖ ^ 2) ≤
          2 * shifted.support.sum (fun a => ‖shifted a‖ ^ 2) +
            2 * EC.coeff.support.sum (fun a => ‖EC.coeff a‖ ^ 2) := by
        simpa [coeff] using finsupp_sub_energy_le shifted EC.coeff
      _ = 4 * EC.coeff.support.sum (fun a => ‖EC.coeff a‖ ^ 2) := by
        rw [show shifted.support.sum (fun a => ‖shifted a‖ ^ 2) =
            EC.coeff.support.sum (fun a => ‖EC.coeff a‖ ^ 2) by
          simpa [shifted] using shiftCoeff_energy EC.coeff s]
        ring
      _ ≤ 4 * EC.upper ^ 2 :=
        mul_le_mul_of_nonneg_left EC.coeff_sq_le (by norm_num)
  have hcard : coeff.support.card ≤
      2 ^ ((exceptionalFinset data).card + 1) := by
    calc
      coeff.support.card ≤ (shifted.support ∪ EC.coeff.support).card := by
        apply Finset.card_le_card
        simpa [coeff] using (Finsupp.support_sub :
          (shifted - EC.coeff).support ⊆ shifted.support ∪ EC.coeff.support)
      _ ≤ shifted.support.card + EC.coeff.support.card :=
        Finset.card_union_le _ _
      _ = EC.coeff.support.card + EC.coeff.support.card := by
        rw [show shifted.support.card = EC.coeff.support.card by
          simpa [shifted] using shiftCoeff_card EC.coeff s]
      _ ≤ 2 ^ (exceptionalFinset data).card +
          2 ^ (exceptionalFinset data).card :=
        Nat.add_le_add EC.coeff_card_le EC.coeff_card_le
      _ = 2 ^ ((exceptionalFinset data).card + 1) := by
        rw [pow_succ]
        ring
  have hcoordinate : ∀ a ∈ coeff.support, ∀ i,
      0 ≤ a i ∧
        a i ≤ (EC.shiftUpper i : Int) +
          (if i = r then dyadicStep j else 0) := by
    intro v hv i
    have hv' : v ∈ shifted.support ∪ EC.coeff.support := by
      exact (Finsupp.support_sub (by simpa [coeff] using hv) :
        v ∈ shifted.support ∪ EC.coeff.support)
    rcases Finset.mem_union.mp hv' with hvShift | hvBase
    · obtain ⟨a, ha, hav⟩ := shiftCoeff_mem EC.coeff s v (by
        simpa [shifted] using hvShift)
      have haBounds := EC.coeff_coordinate_bounds a ha i
      have hs : s i = if i = r then dyadicStep j else 0 := by
        simp [s, dyadicShiftVector, intBasisVector_apply]
      have hvi : v i = a i + s i := congrFun hav.symm i
      constructor
      · rw [hvi, hs]
        exact add_nonneg haBounds.1 (by split <;> simp [dyadicStep])
      · rw [hvi, hs]
        simpa [add_comm] using add_le_add_right haBounds.2
          (if i = r then dyadicStep j else 0)
    · have hvBounds := EC.coeff_coordinate_bounds v hvBase i
      constructor
      · exact hvBounds.1
      · exact hvBounds.2.trans (le_add_of_nonneg_right (by
          split <;> simp [dyadicStep]))
  let firstUpper : Nat := EC.shiftUpper (firstCoordinate hd) + 2 ^ (j - 1)
  have hfirst : ∀ a ∈ coeff.support,
      a (firstCoordinate hd) ≤ (firstUpper : Int) := by
    intro a ha
    have h := (hcoordinate a ha (firstCoordinate hd)).2
    dsimp [firstUpper]
    split at h
    · simpa [dyadicStep] using h
    · have hbase : a (firstCoordinate hd) ≤
          (EC.shiftUpper (firstCoordinate hd) : Int) := by
        simpa using h
      exact hbase.trans (by
        exact_mod_cast Nat.le_add_right (EC.shiftUpper (firstCoordinate hd))
          (2 ^ (j - 1)))
  refine ⟨{
    coeff := coeff
    coeff_eq := hcoeff
    evaluation := hevaluation
    coeff_sq_le := hsq
    coeff_card_le := hcard
    coordinate_bounds := hcoordinate
    firstCoordinateUpper := firstUpper
    firstCoordinateUpper_spec := hfirst
    baseEnvelopeWidth := firstUpper + 1
    baseEnvelopeWidth_eq := rfl
    differenceEnvelopeWidth := (firstUpper + 1) + 1
    differenceEnvelopeWidth_eq := rfl }⟩

/-- Combined finite vector-shift expansion and absolute bounds. -/
noncomputable def blockShiftFinset {d : Nat}
    {delta : IntVec d → RealVec d} (data : ModifiedFrequencyData delta)
    {hd : 0 < d} {hdelta : TendsToZeroAtIntVecInfinity delta} {mu0 : Real}
    {P : BlockParameters hd delta hdelta data mu0}
    (EC : ExceptionalConstants hd delta hdelta data P)
    (j : Nat) (r : Fin d) : BlockShiftFinsetData data EC j r :=
  Classical.choice (blockShiftFinsetData_nonempty data EC j r)

end Internal

end AsymptoticallyIntegerHD
