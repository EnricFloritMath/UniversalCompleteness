import AsymptoticallyIntegerHD.Definitions

/-!
# Small vector perturbations of integer exponentials

Raw perturbed exponentials and their restricted-`Lp` representatives are
kept separate.
-/

noncomputable section

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal

namespace AsymptoticallyIntegerHD

/-- Dimension-normalized perturbation radius. -/
def perturbRadius (d : Nat) : Real :=
  1 / (16 * Real.pi * (d : Real))

/-- Dimension-independent perturbation error. -/
def perturbError : Real :=
  Real.exp (1 / 16 : Real) - 1

/-- Exact elementary bounds on `perturbError`. -/
theorem perturbError_bounds :
    0 ≤ perturbError ∧ perturbError < 1 ∧ 0 < 1 - perturbError := by
  have hexp_le : Real.exp ((1 : Real) / 16) ≤ 1 / (1 - (1 : Real) / 16) :=
    Real.exp_bound_div_one_sub_of_interval (by positivity) (by norm_num)
  have hexp_lt : Real.exp ((1 : Real) / 16) < 2 := by
    calc
      Real.exp ((1 : Real) / 16) ≤ 1 / (1 - (1 : Real) / 16) := hexp_le
      _ < 2 := by norm_num
  have hone : 1 ≤ Real.exp ((1 : Real) / 16) := by
    have := Real.add_one_le_exp ((1 : Real) / 16)
    linarith
  rw [perturbError]
  constructor
  · linarith
  constructor <;> linarith

namespace Internal

/-- Open centered product cube. -/
def centeredUnitCube (d : Nat) : Set (RealVec d) :=
  {x | ∀ i, x i ∈ Set.Ioo (-1 / 2 : Real) (1 / 2 : Real)}

private theorem centeredUnitCube_eq_pi (d : Nat) :
    centeredUnitCube d =
      Set.pi Set.univ (fun _ : Fin d ↦ Set.Ioo (-1 / 2 : Real) (1 / 2 : Real)) := by
  ext x
  simp [centeredUnitCube]

private theorem measurableSet_centeredUnitCube (d : Nat) :
    MeasurableSet (centeredUnitCube d) := by
  rw [centeredUnitCube_eq_pi]
  exact MeasurableSet.pi Set.finite_univ.countable (fun _ _ ↦ measurableSet_Ioo)

private theorem volume_centeredUnitCube (d : Nat) :
    volume (centeredUnitCube d) = 1 := by
  rw [centeredUnitCube_eq_pi, Real.volume_pi_Ioo]
  norm_num

private theorem centeredUnitCube_volume_ne_top (d : Nat) :
    volume (centeredUnitCube d) ≠ ∞ := by
  rw [volume_centeredUnitCube]
  exact ENNReal.one_ne_top

/-- Literal Banach space for every perturbation series. -/
abbrev CenteredCubeL2 (d : Nat) :=
  Lp Complex (2 : ENNReal) (volume.restrict (centeredUnitCube d))

/-- Raw negative-sign integer synthesis. -/
def integerSynthesisRaw {d : Nat} (D : Finset (IntVec d))
    (a : IntVec d → Complex) (x : RealVec d) : Complex :=
  ∑ n ∈ D, a n * starRingEnd Complex (fourierChar (integerEmbed n) x)

/-- The finite integer synthesis belongs to centered `L²`. -/
theorem integerSynthesisRaw_memLp {d : Nat} (D : Finset (IntVec d))
    (a : IntVec d → Complex) :
    MemLp (integerSynthesisRaw D a) (2 : ENNReal)
      (volume.restrict (centeredUnitCube d)) := by
  letI : IsFiniteMeasure (volume.restrict (centeredUnitCube d)) :=
    isFiniteMeasure_restrict.2 (centeredUnitCube_volume_ne_top d)
  apply MemLp.of_bound (p := (2 : ENNReal))
    (by
      apply Continuous.aestronglyMeasurable
      unfold integerSynthesisRaw fourierChar integerEmbed
      fun_prop)
    (∑ n ∈ D, ‖a n‖)
  apply Filter.Eventually.of_forall
  intro x
  unfold integerSynthesisRaw fourierChar
  calc
    ‖∑ n ∈ D, a n * starRingEnd Complex
        (Complex.exp
          (((2 * Real.pi : Real) : Complex) * Complex.I *
            ((∑ i : Fin d, integerEmbed n i * x i : Real) : Complex)))‖
        ≤ ∑ n ∈ D, ‖a n * starRingEnd Complex
          (Complex.exp
            (((2 * Real.pi : Real) : Complex) * Complex.I *
              ((∑ i : Fin d, integerEmbed n i * x i : Real) : Complex)))‖ :=
      norm_sum_le _ _
    _ = ∑ n ∈ D, ‖a n‖ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [norm_mul, Complex.norm_conj, Complex.norm_exp]
      norm_num

/-- Typed integer synthesis. -/
def integerSynthesisLp {d : Nat} (D : Finset (IntVec d))
    (a : IntVec d → Complex) : CenteredCubeL2 d :=
  (integerSynthesisRaw_memLp D a).toLp (integerSynthesisRaw D a)

/-- Raw coercion identity for integer synthesis. -/
theorem integerSynthesisLp_coeFn {d : Nat} (D : Finset (IntVec d))
    (a : IntVec d → Complex) :
    ⇑(integerSynthesisLp D a) =ᵐ[volume.restrict (centeredUnitCube d)]
      integerSynthesisRaw D a := by
  exact (integerSynthesisRaw_memLp D a).coeFn_toLp

private theorem integral_centered_integer_character_one (m : Int) :
    (∫ t in Set.Ioo (-1 / 2 : Real) (1 / 2),
      Complex.exp (((2 * Real.pi * (m : Real) * t : Real) : Complex) * Complex.I)) =
      if m = 0 then 1 else 0 := by
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 / 2 : Real) ≤ 1 / 2)]
  by_cases hm : m = 0
  · subst m
    simp
    norm_num
  · rw [if_neg hm]
    let c : Complex := (((2 * Real.pi * (m : Real) : Real) : Complex) * Complex.I)
    have hc : c ≠ 0 := by
      dsimp [c]
      exact mul_ne_zero
        (Complex.ofReal_ne_zero.mpr (mul_ne_zero
          (mul_ne_zero (by norm_num) Real.pi_ne_zero) (Int.cast_ne_zero.mpr hm)))
        Complex.I_ne_zero
    have hfun : (fun t : Real =>
        Complex.exp (((2 * Real.pi * (m : Real) * t : Real) : Complex) * Complex.I)) =
        fun t : Real => Complex.exp (c * (t : Complex)) := by
      funext t
      congr 1
      dsimp [c]
      push_cast
      ring
    rw [hfun, integral_exp_mul_complex hc]
    have hend : Complex.exp (c * ((1 / 2 : Real) : Complex)) =
        Complex.exp (c * ((-1 / 2 : Real) : Complex)) := by
      calc
        Complex.exp (c * ((1 / 2 : Real) : Complex)) =
            Complex.exp (c * ((-1 / 2 : Real) : Complex) +
              (m : Complex) * (2 * (Real.pi : Complex) * Complex.I)) := by
                congr 1
                dsimp [c]
                push_cast
                ring
        _ = Complex.exp (c * ((-1 / 2 : Real) : Complex)) *
              Complex.exp ((m : Complex) * (2 * (Real.pi : Complex) * Complex.I)) :=
            Complex.exp_add _ _
        _ = Complex.exp (c * ((-1 / 2 : Real) : Complex)) := by
            rw [Complex.exp_int_mul_two_pi_mul_I]
            simp
    rw [hend, sub_self, zero_div]

private theorem centered_integer_character_eq_prod {d : Nat}
    (m : IntVec d) (x : RealVec d) :
    Complex.exp
        ((((2 * Real.pi : Real) : Complex) * Complex.I) *
          ((∑ i : Fin d, (m i : Real) * x i : Real) : Complex)) =
      ∏ i : Fin d,
        Complex.exp (((2 * Real.pi * (m i : Real) * x i : Real) : Complex) * Complex.I) := by
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

private theorem integral_centered_integer_character_hd {d : Nat} (m : IntVec d) :
    (∫ x in centeredUnitCube d,
      Complex.exp
        ((((2 * Real.pi : Real) : Complex) * Complex.I) *
          ((∑ i : Fin d, (m i : Real) * x i : Real) : Complex))) =
      if m = 0 then 1 else 0 := by
  rw [← integral_indicator (measurableSet_centeredUnitCube d)]
  have hindicator :
      (centeredUnitCube d).indicator (fun x : RealVec d =>
        Complex.exp
          ((((2 * Real.pi : Real) : Complex) * Complex.I) *
            ((∑ i : Fin d, (m i : Real) * x i : Real) : Complex))) =
        fun x : RealVec d => ∏ i : Fin d,
          (Set.Ioo (-1 / 2 : Real) (1 / 2)).indicator
            (fun t : Real => Complex.exp
              (((2 * Real.pi * (m i : Real) * t : Real) : Complex) * Complex.I)) (x i) := by
    funext x
    classical
    by_cases hx : ∀ i : Fin d, x i ∈ Set.Ioo (-1 / 2 : Real) (1 / 2)
    · rw [Set.indicator_of_mem (show x ∈ centeredUnitCube d by exact hx)]
      simp only [Set.indicator_of_mem (hx _)]
      exact centered_integer_character_eq_prod m x
    · rw [Set.indicator_of_notMem (show x ∉ centeredUnitCube d by exact hx)]
      push Not at hx
      obtain ⟨i, hi⟩ := hx
      symm
      apply Finset.prod_eq_zero (i := i)
      · simp
      · exact Set.indicator_of_notMem hi _
  rw [hindicator, integral_fintype_prod_volume_eq_prod]
  have hone (i : Fin d) :
      (∫ t : Real,
        (Set.Ioo (-1 / 2 : Real) (1 / 2)).indicator
          (fun t : Real => Complex.exp
            (((2 * Real.pi * (m i : Real) * t : Real) : Complex) * Complex.I)) t) =
        if m i = 0 then 1 else 0 := by
    rw [integral_indicator measurableSet_Ioo]
    exact integral_centered_integer_character_one (m i)
  simp_rw [hone]
  by_cases hm : m = 0
  · subst m
    simp
  · rw [if_neg hm]
    have : ∃ i : Fin d, m i ≠ 0 := by
      by_contra h
      push Not at h
      exact hm (funext h)
    obtain ⟨i, hi⟩ := this
    apply Finset.prod_eq_zero (i := i)
    · simp
    · simp [hi]

private theorem inner_integer_character_hd {d : Nat}
    (n m : IntVec d) (x : RealVec d) :
    inner Complex
      (starRingEnd Complex (fourierChar (integerEmbed n) x))
      (starRingEnd Complex (fourierChar (integerEmbed m) x)) =
      Complex.exp
        ((((2 * Real.pi : Real) : Complex) * Complex.I) *
          ((∑ i : Fin d, ((n i - m i : Int) : Real) * x i : Real) : Complex)) := by
  rw [RCLike.inner_apply']
  unfold fourierChar integerEmbed
  simp
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp
  have hsum :
      (∑ i : Fin d, ((n i : Complex) - (m i : Complex)) * (x i : Complex)) =
        (∑ i : Fin d, (n i : Complex) * (x i : Complex)) -
          ∑ i : Fin d, (m i : Complex) * (x i : Complex) := by
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib]
  rw [hsum]
  simp only [map_ofNat]
  ring

private def integerAtomLp {d : Nat} (n : IntVec d) : CenteredCubeL2 d :=
  integerSynthesisLp {n} (fun _ ↦ 1)

private theorem integerAtomLp_coeFn {d : Nat} (n : IntVec d) :
    ⇑(integerAtomLp n) =ᵐ[volume.restrict (centeredUnitCube d)]
      fun x ↦ starRingEnd Complex (fourierChar (integerEmbed n) x) := by
  filter_upwards [integerSynthesisLp_coeFn {n} (fun _ ↦ 1)] with x hx
  rw [integerAtomLp, hx]
  simp [integerSynthesisRaw]

private theorem integerAtomLp_orthonormal {d : Nat} :
    Orthonormal Complex (integerAtomLp (d := d)) := by
  rw [orthonormal_iff_ite]
  intro n m
  rw [MeasureTheory.L2.inner_def]
  calc
    (∫ x,
        inner Complex (⇑(integerAtomLp n) x) (⇑(integerAtomLp m) x)
          ∂volume.restrict (centeredUnitCube d)) =
        ∫ x in centeredUnitCube d,
          Complex.exp
            ((((2 * Real.pi : Real) : Complex) * Complex.I) *
              ((∑ i : Fin d, ((n i - m i : Int) : Real) * x i : Real) : Complex)) := by
      apply integral_congr_ae
      filter_upwards [integerAtomLp_coeFn n, integerAtomLp_coeFn m] with x hn hm
      rw [hn, hm, inner_integer_character_hd]
    _ = if n = m then 1 else 0 := by
      have hzero : (fun i ↦ n i - m i) = (0 : IntVec d) ↔ n = m := by
        constructor
        · intro h
          funext i
          have hi := congrFun h i
          simp only [Pi.zero_apply, sub_eq_zero] at hi
          exact hi
        · intro h
          subst m
          ext i
          simp
      simpa only [hzero] using
        integral_centered_integer_character_hd (fun i ↦ n i - m i)

/-- Product-cube Parseval for integer-vector characters. -/
theorem integerSynthesisLp_norm_sq {d : Nat} (D : Finset (IntVec d))
    (a : IntVec d → Complex) :
    ‖integerSynthesisLp D a‖ ^ 2 = ∑ n ∈ D, ‖a n‖ ^ 2 := by
  have hatoms : ∀ᵐ x ∂volume.restrict (centeredUnitCube d),
      ∀ n ∈ D, ⇑(integerAtomLp n) x =
        starRingEnd Complex (fourierChar (integerEmbed n) x) := by
    rw [eventually_all_finset]
    intro n hn
    exact integerAtomLp_coeFn n
  have hsmuls : ∀ᵐ x ∂volume.restrict (centeredUnitCube d),
      ∀ n ∈ D, ⇑(a n • integerAtomLp n) x = a n • ⇑(integerAtomLp n) x := by
    rw [eventually_all_finset]
    intro n hn
    exact Lp.coeFn_smul (a n) (integerAtomLp n)
  have hrepr : integerSynthesisLp D a =
      ∑ n ∈ D, a n • integerAtomLp n := by
    apply Lp.ext
    filter_upwards [integerSynthesisLp_coeFn D a,
      Lp.coeFn_finsetSum D (fun n ↦ a n • integerAtomLp n),
      hatoms, hsmuls] with x hlhs hrhs hatom hsmul
    rw [hlhs, hrhs]
    unfold integerSynthesisRaw
    simp only [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro n hn
    rw [hsmul n hn, hatom n hn]
    simp only [smul_eq_mul]
  rw [hrepr]
  simpa only [LinearIsometry.toSpanSingleton_apply] using
    (integerAtomLp_orthonormal (d := d)).orthogonalFamily.norm_sum (fun n ↦ a n) D

/-- Raw negative-sign perturbed synthesis. -/
def perturbedSynthesisRaw {d : Nat} (D : Finset (IntVec d))
    (a : IntVec d → Complex) (nu : IntVec d → RealVec d)
    (x : RealVec d) : Complex :=
  ∑ n ∈ D, a n * starRingEnd Complex (fourierChar (nu n) x)

/-- The finite perturbed synthesis belongs to centered `L²`. -/
theorem perturbedSynthesisRaw_memLp {d : Nat} (D : Finset (IntVec d))
    (a : IntVec d → Complex) (nu : IntVec d → RealVec d) :
    MemLp (perturbedSynthesisRaw D a nu) (2 : ENNReal)
      (volume.restrict (centeredUnitCube d)) := by
  letI : IsFiniteMeasure (volume.restrict (centeredUnitCube d)) :=
    isFiniteMeasure_restrict.2 (centeredUnitCube_volume_ne_top d)
  apply MemLp.of_bound (p := (2 : ENNReal))
    (by
      apply Continuous.aestronglyMeasurable
      unfold perturbedSynthesisRaw fourierChar
      fun_prop)
    (∑ n ∈ D, ‖a n‖)
  apply Filter.Eventually.of_forall
  intro x
  unfold perturbedSynthesisRaw fourierChar
  calc
    ‖∑ n ∈ D, a n * starRingEnd Complex
        (Complex.exp
          (((2 * Real.pi : Real) : Complex) * Complex.I *
            ((∑ i : Fin d, nu n i * x i : Real) : Complex)))‖
        ≤ ∑ n ∈ D, ‖a n * starRingEnd Complex
          (Complex.exp
            (((2 * Real.pi : Real) : Complex) * Complex.I *
              ((∑ i : Fin d, nu n i * x i : Real) : Complex)))‖ :=
      norm_sum_le _ _
    _ = ∑ n ∈ D, ‖a n‖ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [norm_mul, Complex.norm_conj, Complex.norm_exp]
      norm_num

/-- Typed perturbed synthesis. -/
def perturbedSynthesisLp {d : Nat} (D : Finset (IntVec d))
    (a : IntVec d → Complex) (nu : IntVec d → RealVec d) :
    CenteredCubeL2 d :=
  (perturbedSynthesisRaw_memLp D a nu).toLp
    (perturbedSynthesisRaw D a nu)

/-- Raw coercion identity for perturbed synthesis. -/
theorem perturbedSynthesisLp_coeFn {d : Nat} (D : Finset (IntVec d))
    (a : IntVec d → Complex) (nu : IntVec d → RealVec d) :
    ⇑(perturbedSynthesisLp D a nu) =ᵐ[volume.restrict (centeredUnitCube d)]
      perturbedSynthesisRaw D a nu := by
  exact (perturbedSynthesisRaw_memLp D a nu).coeFn_toLp

/-- Ordered-coordinate-word expansion of a dot-product power. -/
theorem dotPower_coordinateWords {d : Nat}
    (epsilon : IntVec d → RealVec d) (n : IntVec d)
    (x : RealVec d) (k : Nat) :
    (∑ i : Fin d, epsilon n i * x i) ^ k =
      ∑ w : Fin k → Fin d,
        (∏ s : Fin k, epsilon n (w s)) * (∏ s : Fin k, x (w s)) := by
  simpa only [Finset.prod_mul_distrib] using
    (Fintype.sum_pow (fun i : Fin d ↦ epsilon n i * x i) k)

/-- Raw `k`th vector perturbation term. -/
def perturbationPowerTermRaw {d : Nat} (D : Finset (IntVec d))
    (a : IntVec d → Complex) (epsilon : IntVec d → RealVec d)
    (k : Nat) (x : RealVec d) : Complex :=
  (((((-2 * Real.pi : Real) : Complex) * Complex.I) ^ k) /
      (k.factorial : Complex)) *
    ∑ n ∈ D, a n *
      (((∑ i : Fin d, epsilon n i * x i : Real) ^ k : Real) : Complex) *
      starRingEnd Complex (fourierChar (integerEmbed n) x)

/-- One raw power term belongs to centered `L²`. -/
theorem perturbationPowerTermRaw_memLp {d : Nat}
    (D : Finset (IntVec d)) (a : IntVec d → Complex)
    (epsilon : IntVec d → RealVec d) (k : Nat) :
    MemLp (perturbationPowerTermRaw D a epsilon k) (2 : ENNReal)
      (volume.restrict (centeredUnitCube d)) := by
  letI : IsFiniteMeasure (volume.restrict (centeredUnitCube d)) :=
    isFiniteMeasure_restrict.2 (centeredUnitCube_volume_ne_top d)
  have hcont : Continuous (perturbationPowerTermRaw D a epsilon k) := by
    unfold perturbationPowerTermRaw fourierChar integerEmbed
    fun_prop
  let C : Real :=
    ‖(((((-2 * Real.pi : Real) : Complex) * Complex.I) ^ k) /
      (k.factorial : Complex))‖ *
      ∑ n ∈ D, ‖a n‖ *
        (∑ i : Fin d, ‖epsilon n i‖ / 2) ^ k
  apply MemLp.of_bound (p := (2 : ENNReal)) hcont.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem (measurableSet_centeredUnitCube d)] with x hx
  unfold perturbationPowerTermRaw
  rw [norm_mul]
  dsimp [C]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    ‖∑ n ∈ D, a n *
        (((∑ i : Fin d, epsilon n i * x i : Real) ^ k : Real) : Complex) *
          starRingEnd Complex (fourierChar (integerEmbed n) x)‖
        ≤ ∑ n ∈ D, ‖a n *
          (((∑ i : Fin d, epsilon n i * x i : Real) ^ k : Real) : Complex) *
            starRingEnd Complex (fourierChar (integerEmbed n) x)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ D, ‖a n‖ * (∑ i : Fin d, ‖epsilon n i‖ / 2) ^ k := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_conj]
      have hchar : ‖fourierChar (integerEmbed n) x‖ = 1 := by
        unfold fourierChar
        rw [Complex.norm_exp]
        norm_num
      rw [hchar, mul_one, abs_pow]
      gcongr
      calc
        |∑ i : Fin d, epsilon n i * x i| ≤
            ∑ i : Fin d, |epsilon n i * x i| :=
          Finset.abs_sum_le_sum_abs (fun i : Fin d ↦ epsilon n i * x i) Finset.univ
        _ ≤ ∑ i : Fin d, ‖epsilon n i‖ / 2 := by
          apply Finset.sum_le_sum
          intro i hi
          rw [abs_mul]
          have hxi : |x i| ≤ (1 : Real) / 2 := by
            have h := hx i
            rw [abs_le]
            constructor <;> linarith [h.1, h.2]
          calc
            |epsilon n i| * |x i| ≤ |epsilon n i| * ((1 : Real) / 2) := by gcongr
            _ = ‖epsilon n i‖ / 2 := by rw [Real.norm_eq_abs]; ring

/-- Typed `k`th vector perturbation term. -/
def perturbationPowerTermLp {d : Nat} (D : Finset (IntVec d))
    (a : IntVec d → Complex) (epsilon : IntVec d → RealVec d)
    (k : Nat) : CenteredCubeL2 d :=
  (perturbationPowerTermRaw_memLp D a epsilon k).toLp
    (perturbationPowerTermRaw D a epsilon k)

/-- Raw coercion identity for a typed power term. -/
theorem perturbationPowerTermLp_coeFn {d : Nat}
    (D : Finset (IntVec d)) (a : IntVec d → Complex)
    (epsilon : IntVec d → RealVec d) (k : Nat) :
    ⇑(perturbationPowerTermLp D a epsilon k) =ᵐ[
      volume.restrict (centeredUnitCube d)]
        perturbationPowerTermRaw D a epsilon k := by
  exact (perturbationPowerTermRaw_memLp D a epsilon k).coeFn_toLp

private def coordinateWordRaw {d : Nat} (D : Finset (IntVec d))
    (a : IntVec d → Complex) (epsilon : IntVec d → RealVec d)
    (k : Nat) (w : Fin k → Fin d) (x : RealVec d) : Complex :=
  ((∏ s : Fin k, x (w s) : Real) : Complex) *
    integerSynthesisRaw D (fun n ↦
      a n * ((∏ s : Fin k, epsilon n (w s) : Real) : Complex)) x

private theorem coordinateWordRaw_memLp {d : Nat} (D : Finset (IntVec d))
    (a : IntVec d → Complex) (epsilon : IntVec d → RealVec d)
    (k : Nat) (w : Fin k → Fin d) :
    MemLp (coordinateWordRaw D a epsilon k w) (2 : ENNReal)
      (volume.restrict (centeredUnitCube d)) := by
  letI : IsFiniteMeasure (volume.restrict (centeredUnitCube d)) :=
    isFiniteMeasure_restrict.2 (centeredUnitCube_volume_ne_top d)
  have hcont : Continuous (coordinateWordRaw D a epsilon k w) := by
    unfold coordinateWordRaw integerSynthesisRaw fourierChar integerEmbed
    fun_prop
  let C : Real := ∑ n ∈ D,
    ‖a n * ((∏ s : Fin k, epsilon n (w s) : Real) : Complex)‖
  apply MemLp.of_bound (p := (2 : ENNReal)) hcont.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem (measurableSet_centeredUnitCube d)] with x hx
  unfold coordinateWordRaw
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hxprod : |∏ s : Fin k, x (w s)| ≤ 1 := by
    rw [← Real.norm_eq_abs, norm_prod]
    calc
      (∏ s : Fin k, |x (w s)|) ≤ ∏ _s : Fin k, (1 : Real) := by
        apply Finset.prod_le_prod
        · intro s hs
          positivity
        · intro s hs
          have hxs := hx (w s)
          rw [abs_le]
          constructor <;> linarith [hxs.1, hxs.2]
      _ = 1 := by simp
  calc
    |∏ s : Fin k, x (w s)| *
        ‖integerSynthesisRaw D (fun n ↦
          a n * ↑(∏ s : Fin k, epsilon n (w s))) x‖ ≤
        1 * ‖integerSynthesisRaw D (fun n ↦
          a n * ↑(∏ s : Fin k, epsilon n (w s))) x‖ := by gcongr
    _ ≤ C := by
      dsimp [C]
      rw [one_mul]
      unfold integerSynthesisRaw
      calc
        ‖∑ n ∈ D,
            (a n * ↑(∏ s : Fin k, epsilon n (w s))) *
              starRingEnd Complex (fourierChar (integerEmbed n) x)‖ ≤
            ∑ n ∈ D, ‖(a n * ↑(∏ s : Fin k, epsilon n (w s))) *
              starRingEnd Complex (fourierChar (integerEmbed n) x)‖ :=
          norm_sum_le _ _
        _ = ∑ n ∈ D, ‖a n * ↑(∏ s : Fin k, epsilon n (w s))‖ := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [norm_mul, Complex.norm_conj]
          have hchar : ‖fourierChar (integerEmbed n) x‖ = 1 := by
            unfold fourierChar
            rw [Complex.norm_exp]
            norm_num
          rw [hchar, mul_one]

private def coordinateWordLp {d : Nat} (D : Finset (IntVec d))
    (a : IntVec d → Complex) (epsilon : IntVec d → RealVec d)
    (k : Nat) (w : Fin k → Fin d) : CenteredCubeL2 d :=
  (coordinateWordRaw_memLp D a epsilon k w).toLp
    (coordinateWordRaw D a epsilon k w)

private theorem coordinateWordLp_coeFn {d : Nat} (D : Finset (IntVec d))
    (a : IntVec d → Complex) (epsilon : IntVec d → RealVec d)
    (k : Nat) (w : Fin k → Fin d) :
    ⇑(coordinateWordLp D a epsilon k w) =ᵐ[
      volume.restrict (centeredUnitCube d)]
        coordinateWordRaw D a epsilon k w := by
  exact (coordinateWordRaw_memLp D a epsilon k w).coeFn_toLp

private theorem coordinateWordLp_norm_le {d : Nat} (D : Finset (IntVec d))
    (a : IntVec d → Complex) (epsilon : IntVec d → RealVec d)
    (k : Nat) (w : Fin k → Fin d) :
    ‖coordinateWordLp D a epsilon k w‖ ≤
      ((1 : Real) / 2) ^ k *
        ‖integerSynthesisLp D (fun n ↦
          a n * ((∏ s : Fin k, epsilon n (w s) : Real) : Complex))‖ := by
  have hpoint : ∀ᵐ x ∂volume.restrict (centeredUnitCube d),
      ‖⇑(coordinateWordLp D a epsilon k w) x‖ ≤
        ((1 : Real) / 2) ^ k *
          ‖⇑(integerSynthesisLp D (fun n ↦
            a n * ((∏ s : Fin k, epsilon n (w s) : Real) : Complex))) x‖ := by
    filter_upwards [coordinateWordLp_coeFn D a epsilon k w,
      integerSynthesisLp_coeFn D (fun n ↦
        a n * ((∏ s : Fin k, epsilon n (w s) : Real) : Complex)),
      ae_restrict_mem (measurableSet_centeredUnitCube d)] with x hword hsyn hx
    rw [hword, hsyn]
    unfold coordinateWordRaw
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    gcongr
    rw [← Real.norm_eq_abs, norm_prod]
    calc
      (∏ s : Fin k, |x (w s)|) ≤
          ∏ _s : Fin k, ((1 : Real) / 2) := by
        apply Finset.prod_le_prod
        · intro s hs
          positivity
        · intro s hs
          have hxs := hx (w s)
          rw [abs_le]
          constructor <;> linarith [hxs.1, hxs.2]
      _ = ((1 : Real) / 2) ^ k := by simp
  exact Lp.norm_le_mul_norm_of_ae_le_mul hpoint

private theorem perturbationPowerTermLp_eq_coordinateWords {d : Nat}
    (D : Finset (IntVec d)) (a : IntVec d → Complex)
    (epsilon : IntVec d → RealVec d) (k : Nat) :
    perturbationPowerTermLp D a epsilon k =
      (((((-2 * Real.pi : Real) : Complex) * Complex.I) ^ k) /
        (k.factorial : Complex)) •
        ∑ w : Fin k → Fin d, coordinateWordLp D a epsilon k w := by
  let c : Complex :=
    (((((-2 * Real.pi : Real) : Complex) * Complex.I) ^ k) /
      (k.factorial : Complex))
  apply Lp.ext
  have hwords : ∀ᵐ x ∂volume.restrict (centeredUnitCube d),
      ∀ w ∈ (Finset.univ : Finset (Fin k → Fin d)),
        ⇑(coordinateWordLp D a epsilon k w) x =
          coordinateWordRaw D a epsilon k w x := by
    rw [eventually_all_finset]
    intro w hw
    exact coordinateWordLp_coeFn D a epsilon k w
  filter_upwards [perturbationPowerTermLp_coeFn D a epsilon k,
    Lp.coeFn_smul c (∑ w : Fin k → Fin d, coordinateWordLp D a epsilon k w),
    Lp.coeFn_finsetSum (Finset.univ : Finset (Fin k → Fin d))
      (fun w ↦ coordinateWordLp D a epsilon k w), hwords] with x hterm hsmul hsum hword
  rw [hterm, hsmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hsum]
  simp only [Finset.sum_apply]
  have hsumraw :
      (∑ w : Fin k → Fin d, ⇑(coordinateWordLp D a epsilon k w) x) =
        ∑ w : Fin k → Fin d, coordinateWordRaw D a epsilon k w x := by
    apply Finset.sum_congr rfl
    intro w hw
    exact hword w (by simp)
  rw [hsumraw]
  change perturbationPowerTermRaw D a epsilon k x =
    c * ∑ w : Fin k → Fin d, coordinateWordRaw D a epsilon k w x
  unfold perturbationPowerTermRaw coordinateWordRaw integerSynthesisRaw
  simp_rw [dotPower_coordinateWords]
  dsimp [c]
  congr 1
  push_cast
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w hw
  apply Finset.sum_congr rfl
  intro n hn
  ring

private theorem integerSynthesisLp_coordinateWord_norm_le {d : Nat}
    (D : Finset (IntVec d)) (a : IntVec d → Complex)
    (epsilon : IntVec d → RealVec d) (k : Nat) (w : Fin k → Fin d)
    (L : Real) (hL : 0 ≤ L) (hepsilon : ∀ n ∈ D, ‖epsilon n‖ ≤ L) :
    ‖integerSynthesisLp D (fun n ↦
      a n * ((∏ s : Fin k, epsilon n (w s) : Real) : Complex))‖ ≤
      L ^ k * Real.sqrt (∑ n ∈ D, ‖a n‖ ^ 2) := by
  let b : IntVec d → Complex := fun n ↦
    a n * ((∏ s : Fin k, epsilon n (w s) : Real) : Complex)
  have heprod (n : IntVec d) (hn : n ∈ D) :
      |∏ s : Fin k, epsilon n (w s)| ≤ L ^ k := by
    rw [← Real.norm_eq_abs, norm_prod]
    calc
      (∏ s : Fin k, ‖epsilon n (w s)‖) ≤ ∏ _s : Fin k, L := by
        apply Finset.prod_le_prod
        · intro s hs
          positivity
        · intro s hs
          exact (norm_le_pi_norm (epsilon n) (w s)).trans (hepsilon n hn)
      _ = L ^ k := by simp
  have henergy : (∑ n ∈ D, ‖b n‖ ^ 2) ≤
      L ^ (2 * k) * (∑ n ∈ D, ‖a n‖ ^ 2) := by
    calc
      (∑ n ∈ D, ‖b n‖ ^ 2) ≤
          ∑ n ∈ D, (L ^ k * ‖a n‖) ^ 2 := by
        apply Finset.sum_le_sum
        intro n hn
        have hbn : ‖b n‖ ≤ L ^ k * ‖a n‖ := by
          dsimp [b]
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          calc
            ‖a n‖ * |∏ s : Fin k, epsilon n (w s)| ≤
                ‖a n‖ * L ^ k :=
              mul_le_mul_of_nonneg_left (heprod n hn) (norm_nonneg _)
            _ = L ^ k * ‖a n‖ := mul_comm _ _
        nlinarith [norm_nonneg (b n),
          mul_nonneg (pow_nonneg hL k) (norm_nonneg (a n))]
      _ = L ^ (2 * k) * (∑ n ∈ D, ‖a n‖ ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        ring
  have hsum_nonneg : 0 ≤ ∑ n ∈ D, ‖a n‖ ^ 2 := by positivity
  have hsyn_nonneg : 0 ≤ ‖integerSynthesisLp D b‖ := norm_nonneg _
  have htarget_nonneg :
      0 ≤ L ^ k * Real.sqrt (∑ n ∈ D, ‖a n‖ ^ 2) := by positivity
  have hsq := integerSynthesisLp_norm_sq D b
  have hsqrt := Real.sq_sqrt hsum_nonneg
  have hsq_le : ‖integerSynthesisLp D b‖ ^ 2 ≤
      (L ^ k * Real.sqrt (∑ n ∈ D, ‖a n‖ ^ 2)) ^ 2 := by
    calc
      ‖integerSynthesisLp D b‖ ^ 2 = ∑ n ∈ D, ‖b n‖ ^ 2 := hsq
      _ ≤ L ^ (2 * k) * (∑ n ∈ D, ‖a n‖ ^ 2) := henergy
      _ = (L ^ k * Real.sqrt (∑ n ∈ D, ‖a n‖ ^ 2)) ^ 2 := by
        rw [mul_pow, hsqrt, ← pow_mul]
        congr 2
        omega
  exact (sq_le_sq₀ hsyn_nonneg htarget_nonneg).mp hsq_le

/-- Exact norm majorant for one HD power term. -/
theorem perturbationPowerTermLp_norm_le {d : Nat}
    (D : Finset (IntVec d)) (a : IntVec d → Complex)
    (epsilon : IntVec d → RealVec d) (k : Nat) (L : Real)
    (hL : 0 ≤ L) (hepsilon : ∀ n ∈ D, ‖epsilon n‖ ≤ L) :
    ‖perturbationPowerTermLp D a epsilon k‖ ≤
      (Real.pi * (d : Real) * L) ^ k / (k.factorial : Real) *
        Real.sqrt (∑ n ∈ D, ‖a n‖ ^ 2) := by
  let c : Complex :=
    (((((-2 * Real.pi : Real) : Complex) * Complex.I) ^ k) /
      (k.factorial : Complex))
  let A : Real := Real.sqrt (∑ n ∈ D, ‖a n‖ ^ 2)
  have hc : ‖c‖ = (2 * Real.pi) ^ k / (k.factorial : Real) := by
    dsimp [c]
    rw [norm_div, norm_pow, norm_mul, Complex.norm_real, Complex.norm_I, mul_one]
    have hfact : ‖(k.factorial : Complex)‖ = (k.factorial : Real) := by norm_num
    rw [hfact, Real.norm_eq_abs]
    simp [abs_of_pos Real.pi_pos]
  have hsum :
      ‖∑ w : Fin k → Fin d, coordinateWordLp D a epsilon k w‖ ≤
        (d : Real) ^ k * (((1 : Real) / 2) ^ k * (L ^ k * A)) := by
    calc
      ‖∑ w : Fin k → Fin d, coordinateWordLp D a epsilon k w‖ ≤
          ∑ w : Fin k → Fin d, ‖coordinateWordLp D a epsilon k w‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _w : Fin k → Fin d,
          ((1 : Real) / 2) ^ k * (L ^ k * A) := by
        apply Finset.sum_le_sum
        intro w hw
        calc
          ‖coordinateWordLp D a epsilon k w‖ ≤
              ((1 : Real) / 2) ^ k *
                ‖integerSynthesisLp D (fun n ↦
                  a n * ((∏ s : Fin k, epsilon n (w s) : Real) : Complex))‖ :=
            coordinateWordLp_norm_le D a epsilon k w
          _ ≤ ((1 : Real) / 2) ^ k * (L ^ k * A) := by
            gcongr
            exact integerSynthesisLp_coordinateWord_norm_le
              D a epsilon k w L hL hepsilon
      _ = (d : Real) ^ k * (((1 : Real) / 2) ^ k * (L ^ k * A)) := by
        simp [Nat.cast_pow]
  rw [perturbationPowerTermLp_eq_coordinateWords]
  change ‖c • ∑ w : Fin k → Fin d, coordinateWordLp D a epsilon k w‖ ≤ _
  rw [norm_smul, hc]
  calc
    (2 * Real.pi) ^ k / (k.factorial : Real) *
        ‖∑ w : Fin k → Fin d, coordinateWordLp D a epsilon k w‖ ≤
      (2 * Real.pi) ^ k / (k.factorial : Real) *
        ((d : Real) ^ k * (((1 : Real) / 2) ^ k * (L ^ k * A))) := by
      gcongr
    _ = (Real.pi * (d : Real) * L) ^ k / (k.factorial : Real) * A := by
      have hhalf : ((1 : Real) / 2) ^ k * 2 ^ k = 1 := by
        rw [← mul_pow]
        norm_num
      have hcancel (B : Real) : B * ((1 : Real) / 2) ^ k * 2 ^ k = B := by
        rw [mul_assoc, hhalf, mul_one]
      ring_nf
      exact hcancel _

private theorem star_fourierChar_eq_exp_neg {d : Nat}
    (xi x : RealVec d) :
    starRingEnd Complex (fourierChar xi x) =
      Complex.exp
        ((((-2 * Real.pi : Real) : Complex) * Complex.I) *
          ((∑ i : Fin d, xi i * x i : Real) : Complex)) := by
  unfold fourierChar
  rw [← Complex.exp_conj]
  congr 1
  simp
  simp only [map_ofNat]
  simp

private theorem perturbationPowerTermRaw_hasSum {d : Nat}
    (D : Finset (IntVec d)) (a : IntVec d → Complex)
    (nu : IntVec d → RealVec d) (x : RealVec d) :
    HasSum
      (fun k : Nat ↦ perturbationPowerTermRaw D a
        (fun n ↦ nu n - integerEmbed n) (k + 1) x)
      (perturbedSynthesisRaw D a nu x - integerSynthesisRaw D a x) := by
  let X : Complex := (((-2 * Real.pi : Real) : Complex) * Complex.I)
  let dotError : IntVec d → Real := fun n ↦
    ∑ i : Fin d, (nu n i - integerEmbed n i) * x i
  let z : IntVec d → Complex := fun n ↦ X * (dotError n : Complex)
  let base : IntVec d → Complex := fun n ↦
    starRingEnd Complex (fourierChar (integerEmbed n) x)
  let f : IntVec d → Nat → Complex := fun n k ↦
    a n * base n * (z n) ^ (k + 1) / ((k + 1).factorial : Complex)
  let g : IntVec d → Complex := fun n ↦
    a n * base n * (Complex.exp (z n) - 1)
  have hsingle (n : IntVec d) : HasSum (f n) (g n) := by
    have hz := (hasSum_nat_add_iff' 1).mpr
      (NormedSpace.expSeries_div_hasSum_exp (z n))
    have htail : HasSum
        (fun k : Nat ↦ (z n) ^ (k + 1) / ((k + 1).factorial : Complex))
        (Complex.exp (z n) - 1) := by
      simpa only [Complex.exp_eq_exp_ℂ, Finset.range_one, Finset.sum_singleton,
        pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] using hz
    simpa [f, g, mul_assoc, mul_div_assoc] using
      htail.mul_left (a n * base n)
  have hfin : HasSum (fun k : Nat ↦ ∑ n ∈ D, f n k) (∑ n ∈ D, g n) := by
    classical
    induction D using Finset.induction_on with
    | empty => simp
    | @insert n D hn ih =>
        simpa [Finset.sum_insert hn] using (hsingle n).add ih
  convert hfin using 1
  · funext k
    unfold perturbationPowerTermRaw
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    change X ^ (k + 1) / ((k + 1).factorial : Complex) *
      (a n * (((dotError n) ^ (k + 1) : Real) : Complex) * base n) = f n k
    dsimp only [f, z]
    push_cast
    rw [mul_pow]
    ring
  · unfold perturbedSynthesisRaw integerSynthesisRaw
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    dsimp [g, z, X, base, dotError]
    rw [star_fourierChar_eq_exp_neg, star_fourierChar_eq_exp_neg]
    have hdot :
        (∑ i : Fin d, (nu n i - (n i : Real)) * x i) =
          (∑ i : Fin d, nu n i * x i) -
            ∑ i : Fin d, (n i : Real) * x i := by
      simp_rw [sub_mul]
      rw [Finset.sum_sub_distrib]
    rw [hdot]
    have hexp :
        Complex.exp
            ((((-2 * Real.pi : Real) : Complex) * Complex.I) *
              ((∑ i : Fin d, nu n i * x i : Real) : Complex)) =
          Complex.exp
              ((((-2 * Real.pi : Real) : Complex) * Complex.I) *
                ((∑ i : Fin d, integerEmbed n i * x i : Real) : Complex)) *
            Complex.exp
              ((((-2 * Real.pi : Real) : Complex) * Complex.I) *
                (((∑ i : Fin d, nu n i * x i : Real) -
                  ∑ i : Fin d, integerEmbed n i * x i : Real) : Complex)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hexp]
    simp only [integerEmbed_apply]
    ring

/-- Typed perturbation power series in `CenteredCubeL2 d`. -/
theorem perturbedSynthesisLp_hasSum_powerTerms {d : Nat}
    (D : Finset (IntVec d)) (a : IntVec d → Complex)
    (nu : IntVec d → RealVec d) :
    HasSum
      (fun k : Nat ↦ perturbationPowerTermLp D a
        (fun n ↦ nu n - integerEmbed n) (k + 1))
      (perturbedSynthesisLp D a nu - integerSynthesisLp D a) := by
  let epsilon : IntVec d → RealVec d := fun n ↦ nu n - integerEmbed n
  let L : Real := ∑ n ∈ D, ‖epsilon n‖
  let A : Real := Real.sqrt (∑ n ∈ D, ‖a n‖ ^ 2)
  let u : Nat → CenteredCubeL2 d := fun k ↦
    perturbationPowerTermLp D a epsilon (k + 1)
  have hL : 0 ≤ L := by
    dsimp [L]
    positivity
  have hepsilon : ∀ n ∈ D, ‖epsilon n‖ ≤ L := by
    intro n hn
    dsimp [L]
    exact Finset.single_le_sum (fun m hm ↦ norm_nonneg (epsilon m)) hn
  have hmajor : Summable (fun k : Nat ↦
      (Real.pi * (d : Real) * L) ^ (k + 1) /
        ((k + 1).factorial : Real) * A) := by
    have hbase := Real.summable_pow_div_factorial (Real.pi * (d : Real) * L)
    have htail : Summable (fun k : Nat ↦
        (Real.pi * (d : Real) * L) ^ (k + 1) /
          ((k + 1).factorial : Real)) := by
      exact (summable_nat_add_iff 1).mpr hbase
    exact htail.mul_right A
  have hnorm : Summable (fun k ↦ ‖u k‖) := by
    apply hmajor.of_nonneg_of_le (fun k ↦ norm_nonneg (u k))
    intro k
    exact perturbationPowerTermLp_norm_le
      D a epsilon (k + 1) L hL hepsilon
  have hu : Summable u := hnorm.of_norm
  let s : CenteredCubeL2 d := ∑' k, u k
  have hus : HasSum u s := hu.hasSum
  have hLp : Tendsto (fun N : Nat ↦ ∑ k ∈ Finset.range N, u k)
      atTop (𝓝 s) := hus.tendsto_sum_nat
  have hLpMeasure : TendstoInMeasure
      (volume.restrict (centeredUnitCube d))
      (fun N : Nat ↦ ⇑(∑ k ∈ Finset.range N, u k)) atTop ⇑s :=
    tendstoInMeasure_of_tendsto_Lp hLp
  let rawPartial : Nat → RealVec d → Complex := fun N x ↦
    ∑ k ∈ Finset.range N, perturbationPowerTermRaw D a epsilon (k + 1) x
  have hcoePartial (N : Nat) :
      ⇑(∑ k ∈ Finset.range N, u k) =ᵐ[
        volume.restrict (centeredUnitCube d)] rawPartial N := by
    have hterms : ∀ᵐ x ∂volume.restrict (centeredUnitCube d),
        ∀ k ∈ Finset.range N, ⇑(u k) x =
          perturbationPowerTermRaw D a epsilon (k + 1) x := by
      rw [eventually_all_finset]
      intro k hk
      exact perturbationPowerTermLp_coeFn D a epsilon (k + 1)
    filter_upwards [Lp.coeFn_finsetSum (Finset.range N) u, hterms] with x hsum hterm
    rw [hsum]
    simp only [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro k hk
    exact hterm k hk
  have hLpRaw : TendstoInMeasure (volume.restrict (centeredUnitCube d))
      rawPartial atTop ⇑s := hLpMeasure.congr_left hcoePartial
  let rawTarget : RealVec d → Complex := fun x ↦
    perturbedSynthesisRaw D a nu x - integerSynthesisRaw D a x
  letI : IsFiniteMeasure (volume.restrict (centeredUnitCube d)) :=
    isFiniteMeasure_restrict.2 (centeredUnitCube_volume_ne_top d)
  have hrawMeas : ∀ N, AEStronglyMeasurable (rawPartial N)
      (volume.restrict (centeredUnitCube d)) := by
    intro N
    apply Continuous.aestronglyMeasurable
    dsimp [rawPartial, epsilon]
    unfold perturbationPowerTermRaw fourierChar integerEmbed
    fun_prop
  have hrawAe : ∀ᵐ x ∂volume.restrict (centeredUnitCube d),
      Tendsto (fun N ↦ rawPartial N x) atTop (𝓝 (rawTarget x)) := by
    apply Filter.Eventually.of_forall
    intro x
    exact (perturbationPowerTermRaw_hasSum D a nu x).tendsto_sum_nat
  have hrawMeasure : TendstoInMeasure (volume.restrict (centeredUnitCube d))
      rawPartial atTop rawTarget :=
    tendstoInMeasure_of_tendsto_ae hrawMeas hrawAe
  have hs_coe : ⇑s =ᵐ[volume.restrict (centeredUnitCube d)] rawTarget :=
    tendstoInMeasure_ae_unique hLpRaw hrawMeasure
  have htarget_coe :
      ⇑(perturbedSynthesisLp D a nu - integerSynthesisLp D a) =ᵐ[
        volume.restrict (centeredUnitCube d)] rawTarget := by
    filter_upwards [Lp.coeFn_sub (perturbedSynthesisLp D a nu)
        (integerSynthesisLp D a),
      perturbedSynthesisLp_coeFn D a nu,
      integerSynthesisLp_coeFn D a] with x hsub hp hi
    rw [hsub]
    simp only [Pi.sub_apply, hp, hi, rawTarget]
  have hs_eq : s = perturbedSynthesisLp D a nu - integerSynthesisLp D a := by
    apply Lp.ext
    exact hs_coe.trans htarget_coe.symm
  simpa only [u, epsilon, hs_eq] using hus

/-- Exact raw-function interpretation of the typed series. -/
theorem perturbedSynthesis_powerSeries_coe_ae {d : Nat}
    (D : Finset (IntVec d)) (a : IntVec d → Complex)
    (nu : IntVec d → RealVec d) :
    (⇑(perturbedSynthesisLp D a nu - integerSynthesisLp D a) =ᵐ[
        volume.restrict (centeredUnitCube d)]
      fun x ↦ perturbedSynthesisRaw D a nu x - integerSynthesisRaw D a x) ∧
    ∀ k : Nat,
      ⇑(perturbationPowerTermLp D a (fun n ↦ nu n - integerEmbed n)
        (k + 1)) =ᵐ[volume.restrict (centeredUnitCube d)]
          perturbationPowerTermRaw D a (fun n ↦ nu n - integerEmbed n)
            (k + 1) := by
  constructor
  · filter_upwards [Lp.coeFn_sub (perturbedSynthesisLp D a nu)
        (integerSynthesisLp D a),
      perturbedSynthesisLp_coeFn D a nu,
      integerSynthesisLp_coeFn D a] with x hsub hp hi
    rw [hsub]
    simp only [Pi.sub_apply, hp, hi]
  · intro k
    exact perturbationPowerTermLp_coeFn D a
      (fun n ↦ nu n - integerEmbed n) (k + 1)

/-- Summed typed perturbation norm estimate. -/
theorem perturbedSynthesisLp_sub_norm_le {d : Nat}
    (D : Finset (IntVec d)) (a : IntVec d → Complex)
    (nu : IntVec d → RealVec d) (L : Real) (hL : 0 ≤ L)
    (hnu : ∀ n ∈ D, ‖nu n - integerEmbed n‖ ≤ L) :
    ‖perturbedSynthesisLp D a nu - integerSynthesisLp D a‖ ≤
      (Real.exp (Real.pi * (d : Real) * L) - 1) *
        Real.sqrt (∑ n ∈ D, ‖a n‖ ^ 2) := by
  let epsilon : IntVec d → RealVec d := fun n ↦ nu n - integerEmbed n
  let A : Real := Real.sqrt (∑ n ∈ D, ‖a n‖ ^ 2)
  let u : Nat → CenteredCubeL2 d := fun k ↦
    perturbationPowerTermLp D a epsilon (k + 1)
  have hu : HasSum u (perturbedSynthesisLp D a nu - integerSynthesisLp D a) :=
    perturbedSynthesisLp_hasSum_powerTerms D a nu
  have htail : HasSum
      (fun k : Nat ↦ (Real.pi * (d : Real) * L) ^ (k + 1) /
        ((k + 1).factorial : Real))
      (Real.exp (Real.pi * (d : Real) * L) - 1) := by
    have h := (hasSum_nat_add_iff' 1).mpr
      (NormedSpace.expSeries_div_hasSum_exp (Real.pi * (d : Real) * L))
    simpa only [Real.exp_eq_exp_ℝ, Finset.range_one, Finset.sum_singleton,
      pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] using h
  have hmajor : HasSum
      (fun k : Nat ↦ (Real.pi * (d : Real) * L) ^ (k + 1) /
        ((k + 1).factorial : Real) * A)
      ((Real.exp (Real.pi * (d : Real) * L) - 1) * A) := htail.mul_right A
  apply hu.norm_le_of_bounded hmajor
  intro k
  exact perturbationPowerTermLp_norm_le D a epsilon (k + 1) L hL hnu

private theorem unitCube_eq_pi (d : Nat) :
    unitCube d = Set.pi Set.univ (fun _ : Fin d ↦ Set.Ioo (0 : Real) 1) := by
  ext x
  simp [unitCube]

private theorem measurableSet_unitCube (d : Nat) : MeasurableSet (unitCube d) := by
  rw [unitCube_eq_pi]
  exact MeasurableSet.pi Set.finite_univ.countable (fun _ _ ↦ measurableSet_Ioo)

private theorem volume_unitCube (d : Nat) : volume (unitCube d) = 1 := by
  rw [unitCube_eq_pi, Real.volume_pi_Ioo]
  norm_num

private theorem unitCube_volume_ne_top (d : Nat) : volume (unitCube d) ≠ ∞ := by
  rw [volume_unitCube]
  exact ENNReal.one_ne_top

private theorem star_fourierChar_add {d : Nat} (xi x y : RealVec d) :
    starRingEnd Complex (fourierChar xi (x + y)) =
      starRingEnd Complex (fourierChar xi y) *
        starRingEnd Complex (fourierChar xi x) := by
  rw [star_fourierChar_eq_exp_neg, star_fourierChar_eq_exp_neg,
    star_fourierChar_eq_exp_neg, ← Complex.exp_add]
  congr 1
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  push_cast
  ring

private theorem toLp_norm_sq_eq_sqNorm_hd {d : Nat}
    (S : Set (RealVec d)) (F : RealVec d → Complex)
    (hF : MemLp F (2 : ENNReal) (volume.restrict S)) :
    ‖hF.toLp F‖ ^ 2 = sqNormOn S F := by
  unfold sqNormOn
  calc
    ‖hF.toLp F‖ ^ 2 = (inner Complex (hF.toLp F) (hF.toLp F)).re := by
      rw [inner_self_eq_norm_sq_to_K]
      simp [pow_two, Complex.mul_re]
    _ = (∫ x, inner Complex (⇑(hF.toLp F) x) (⇑(hF.toLp F) x)
        ∂volume.restrict S).re := by
      rw [MeasureTheory.L2.inner_def]
    _ = ∫ x, (inner Complex (⇑(hF.toLp F) x) (⇑(hF.toLp F) x)).re
        ∂volume.restrict S := by
      exact (integral_re (𝕜 := Complex) (MeasureTheory.L2.integrable_inner
        (hF.toLp F) (hF.toLp F))).symm
    _ = ∫ x, ‖F x‖ ^ 2 ∂volume.restrict S := by
      apply integral_congr_ae
      filter_upwards [hF.coeFn_toLp] with x hx
      rw [hx, RCLike.inner_apply', Complex.conj_mul']
      simp [pow_two, Complex.mul_re]

/-- Unit-cube finite synthesis bounds. -/
theorem perturbed_synthesis_bounds_unitCube {d : Nat} (hd : 0 < d)
    (nu : IntVec d → RealVec d)
    (hnu : ∀ n, ‖nu n - integerEmbed n‖ ≤ perturbRadius d) :
    ∀ (D : Finset (IntVec d)) (a : IntVec d → Complex),
      AEStronglyMeasurable (perturbedSynthesisRaw D a nu)
        (volume.restrict (unitCube d)) ∧
      MemLp (perturbedSynthesisRaw D a nu) (2 : ENNReal)
        (volume.restrict (unitCube d)) ∧
      (1 - perturbError) ^ 2 * (∑ n ∈ D, ‖a n‖ ^ 2) ≤
        sqNormOn (unitCube d) (perturbedSynthesisRaw D a nu) ∧
      sqNormOn (unitCube d) (perturbedSynthesisRaw D a nu) ≤
        (1 + perturbError) ^ 2 * (∑ n ∈ D, ‖a n‖ ^ 2) := by
  intro D a
  let half : RealVec d := fun _ ↦ (1 : Real) / 2
  let shift : RealVec d → RealVec d := fun x ↦ x + half
  let b : IntVec d → Complex := fun n ↦
    a n * starRingEnd Complex (fourierChar (nu n) half)
  have hb_energy : (∑ n ∈ D, ‖b n‖ ^ 2) = ∑ n ∈ D, ‖a n‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro n hn
    dsimp [b]
    rw [norm_mul, Complex.norm_conj]
    have hchar : ‖fourierChar (nu n) half‖ = 1 := by
      unfold fourierChar
      rw [Complex.norm_exp]
      norm_num
    rw [hchar, mul_one]
  have htranslate (x : RealVec d) :
      perturbedSynthesisRaw D a nu (shift x) =
        perturbedSynthesisRaw D b nu x := by
    unfold perturbedSynthesisRaw
    apply Finset.sum_congr rfl
    intro n hn
    dsimp [shift, b]
    rw [star_fourierChar_add]
    ring
  have hpre : shift ⁻¹' unitCube d = centeredUnitCube d := by
    ext x
    constructor
    · intro hx i
      have hi := hx i
      dsimp [shift, half] at hi
      constructor <;> linarith [hi.1, hi.2]
    · intro hx i
      have hi := hx i
      dsimp [shift, half]
      constructor <;> linarith [hi.1, hi.2]
  have hEmb : MeasurableEmbedding shift := by
    exact (MeasurableEquiv.addRight half).measurableEmbedding
  have hmp : MeasurePreserving shift
      (volume.restrict (centeredUnitCube d))
      (volume.restrict (unitCube d)) := by
    have h := (measurePreserving_add_right volume half).restrict_preimage_emb
      hEmb (unitCube d)
    rwa [hpre] at h
  have hsq_translate :
      sqNormOn (unitCube d) (perturbedSynthesisRaw D a nu) =
        sqNormOn (centeredUnitCube d) (perturbedSynthesisRaw D b nu) := by
    unfold sqNormOn
    symm
    calc
      (∫ x, ‖perturbedSynthesisRaw D b nu x‖ ^ 2
          ∂volume.restrict (centeredUnitCube d)) =
          ∫ x, ‖perturbedSynthesisRaw D a nu (shift x)‖ ^ 2
            ∂volume.restrict (centeredUnitCube d) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x ↦
          congrArg (fun z : Complex ↦ ‖z‖ ^ 2) (htranslate x).symm
      _ = ∫ y, ‖perturbedSynthesisRaw D a nu y‖ ^ 2
            ∂volume.restrict (unitCube d) :=
        hmp.integral_comp hEmb
          (fun y : RealVec d ↦ ‖perturbedSynthesisRaw D a nu y‖ ^ 2)
  have hmeas : AEStronglyMeasurable (perturbedSynthesisRaw D a nu)
      (volume.restrict (unitCube d)) := by
    apply Continuous.aestronglyMeasurable
    unfold perturbedSynthesisRaw fourierChar
    fun_prop
  letI : IsFiniteMeasure (volume.restrict (unitCube d)) :=
    isFiniteMeasure_restrict.2 (unitCube_volume_ne_top d)
  have hmem : MemLp (perturbedSynthesisRaw D a nu) (2 : ENNReal)
      (volume.restrict (unitCube d)) := by
    apply MemLp.of_bound (p := (2 : ENNReal)) hmeas (∑ n ∈ D, ‖a n‖)
    apply Filter.Eventually.of_forall
    intro x
    unfold perturbedSynthesisRaw
    calc
      ‖∑ n ∈ D, a n * starRingEnd Complex (fourierChar (nu n) x)‖ ≤
          ∑ n ∈ D, ‖a n * starRingEnd Complex (fourierChar (nu n) x)‖ :=
        norm_sum_le _ _
      _ = ∑ n ∈ D, ‖a n‖ := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [norm_mul, Complex.norm_conj]
        have hchar : ‖fourierChar (nu n) x‖ = 1 := by
          unfold fourierChar
          rw [Complex.norm_exp]
          norm_num
        rw [hchar, mul_one]
  have hcenter_sq : ‖perturbedSynthesisLp D b nu‖ ^ 2 =
      sqNormOn (centeredUnitCube d) (perturbedSynthesisRaw D b nu) :=
    toLp_norm_sq_eq_sqNorm_hd (centeredUnitCube d)
      (perturbedSynthesisRaw D b nu) (perturbedSynthesisRaw_memLp D b nu)
  have hradius_pos : 0 < perturbRadius d := by
    unfold perturbRadius
    positivity
  have hscale : Real.pi * (d : Real) * perturbRadius d = (1 : Real) / 16 := by
    unfold perturbRadius
    have hdreal : (d : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
    field_simp
  have hdiff : ‖perturbedSynthesisLp D b nu - integerSynthesisLp D b‖ ≤
      perturbError * Real.sqrt (∑ n ∈ D, ‖a n‖ ^ 2) := by
    have h := perturbedSynthesisLp_sub_norm_le D b nu (perturbRadius d)
      (le_of_lt hradius_pos) (fun n hn ↦ hnu n)
    simpa only [perturbError, hscale, hb_energy] using h
  have hint_sq : ‖integerSynthesisLp D b‖ ^ 2 = ∑ n ∈ D, ‖a n‖ ^ 2 := by
    simpa only [hb_energy] using integerSynthesisLp_norm_sq D b
  have hA_nonneg : 0 ≤ ∑ n ∈ D, ‖a n‖ ^ 2 := by positivity
  have hint_norm : ‖integerSynthesisLp D b‖ =
      Real.sqrt (∑ n ∈ D, ‖a n‖ ^ 2) := by
    have hsqrt := Real.sq_sqrt hA_nonneg
    apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [hint_sq, hsqrt]
  have herr := perturbError_bounds
  have hupper : ‖perturbedSynthesisLp D b nu‖ ≤
      (1 + perturbError) * Real.sqrt (∑ n ∈ D, ‖a n‖ ^ 2) := by
    calc
      ‖perturbedSynthesisLp D b nu‖ ≤
          ‖perturbedSynthesisLp D b nu - integerSynthesisLp D b‖ +
            ‖integerSynthesisLp D b‖ := by
        simpa [sub_add_cancel] using norm_add_le
          (perturbedSynthesisLp D b nu - integerSynthesisLp D b)
          (integerSynthesisLp D b)
      _ ≤ perturbError * Real.sqrt (∑ n ∈ D, ‖a n‖ ^ 2) +
          Real.sqrt (∑ n ∈ D, ‖a n‖ ^ 2) :=
        add_le_add hdiff (le_of_eq hint_norm)
      _ = (1 + perturbError) * Real.sqrt (∑ n ∈ D, ‖a n‖ ^ 2) := by ring
  have hlower : (1 - perturbError) * Real.sqrt (∑ n ∈ D, ‖a n‖ ^ 2) ≤
      ‖perturbedSynthesisLp D b nu‖ := by
    have htri : ‖integerSynthesisLp D b‖ ≤
        ‖perturbedSynthesisLp D b nu - integerSynthesisLp D b‖ +
          ‖perturbedSynthesisLp D b nu‖ := by
      have h := norm_add_le
        (integerSynthesisLp D b - perturbedSynthesisLp D b nu)
        (perturbedSynthesisLp D b nu)
      rw [sub_add_cancel] at h
      simpa [norm_sub_rev] using h
    rw [hint_norm] at htri
    nlinarith
  refine ⟨hmeas, hmem, ?_, ?_⟩
  · rw [hsq_translate, ← hcenter_sq]
    have hlo_nonneg : 0 ≤
        (1 - perturbError) * Real.sqrt (∑ n ∈ D, ‖a n‖ ^ 2) :=
      mul_nonneg (le_of_lt herr.2.2) (Real.sqrt_nonneg _)
    have h := (sq_le_sq₀ hlo_nonneg (norm_nonneg _)).mpr hlower
    simpa [mul_pow, Real.sq_sqrt hA_nonneg] using h
  · rw [hsq_translate, ← hcenter_sq]
    have hup_nonneg : 0 ≤
        (1 + perturbError) * Real.sqrt (∑ n ∈ D, ‖a n‖ ^ 2) :=
      mul_nonneg (by linarith [herr.1]) (Real.sqrt_nonneg _)
    have h := (sq_le_sq₀ (norm_nonneg _) hup_nonneg).mpr hupper
    simpa [mul_pow, Real.sq_sqrt hA_nonneg] using h

end Internal

/-- Exact finite synthesis and restricted-analysis bounds. -/
structure ExponentialBoundsHD {d : Nat} (nu : IntVec d → RealVec d) where
  lower : Real
  upper : Real
  lower_pos : 0 < lower
  upper_pos : 0 < upper
  synthesis_lower : ∀ (D : Finset (IntVec d)) (a : IntVec d → Complex),
    lower * (∑ n ∈ D, ‖a n‖ ^ 2) ≤
      sqNormOn (unitCube d) (Internal.perturbedSynthesisRaw D a nu)
  synthesis_upper : ∀ (D : Finset (IntVec d)) (a : IntVec d → Complex),
    sqNormOn (unitCube d) (Internal.perturbedSynthesisRaw D a nu) ≤
      upper * (∑ n ∈ D, ‖a n‖ ^ 2)
  analysis_upper : ∀ (D : Finset (IntVec d)) (H : RealVec d → Complex),
    AEStronglyMeasurable H (volume.restrict (unitCube d)) →
    MemLp H (2 : ENNReal) (volume.restrict (unitCube d)) →
    (∑ n ∈ D, ‖inverseSampleOn (unitCube d) H (nu n)‖ ^ 2) ≤
      upper * sqNormOn (unitCube d) H

/-- Existence certificate for explicit bounds on a globally sanitized perturbation. -/
theorem smallPerturbation_exponentialBounds_hd_nonempty {d : Nat}
    (hd : 0 < d) (nu : IntVec d → RealVec d)
    (hnu : ∀ n, ‖nu n - integerEmbed n‖ ≤ perturbRadius d) :
    Nonempty {K : ExponentialBoundsHD nu //
      K.lower = (1 - perturbError) ^ 2 ∧
      K.upper = (1 + perturbError) ^ 2} := by
  have herr := perturbError_bounds
  let lower : Real := (1 - perturbError) ^ 2
  let upper : Real := (1 + perturbError) ^ 2
  have hlower : 0 < lower := by
    dsimp [lower]
    exact sq_pos_of_pos herr.2.2
  have hupper : 0 < upper := by
    dsimp [upper]
    exact sq_pos_of_pos (by linarith [herr.1])
  let K : ExponentialBoundsHD nu :=
    { lower := lower
      upper := upper
      lower_pos := hlower
      upper_pos := hupper
      synthesis_lower := fun D a ↦
        (Internal.perturbed_synthesis_bounds_unitCube hd nu hnu D a).2.2.1
      synthesis_upper := fun D a ↦
        (Internal.perturbed_synthesis_bounds_unitCube hd nu hnu D a).2.2.2
      analysis_upper := by
        intro D H hHmeas hHLp
        letI : IsFiniteMeasure (volume.restrict (unitCube d)) :=
          isFiniteMeasure_restrict.2 (Internal.unitCube_volume_ne_top d)
        let c : IntVec d → Complex := fun n ↦
          inverseSampleOn (unitCube d) H (nu n)
        let A : Real := ∑ n ∈ D, ‖c n‖ ^ 2
        let syn : RealVec d → Complex := Internal.perturbedSynthesisRaw D c nu
        have hsynth_data :=
          Internal.perturbed_synthesis_bounds_unitCube hd nu hnu D c
        have hsynMem : MemLp syn (2 : ENNReal)
            (volume.restrict (unitCube d)) := hsynth_data.2.1
        let synLp : Lp Complex (2 : ENNReal)
            (volume.restrict (unitCube d)) := hsynMem.toLp syn
        let HLp : Lp Complex (2 : ENNReal)
            (volume.restrict (unitCube d)) := hHLp.toLp H
        have hHint : Integrable H (volume.restrict (unitCube d)) :=
          hHLp.integrable one_le_two
        have hpoint (x : RealVec d) : inner Complex (syn x) (H x) =
            ∑ n ∈ D, starRingEnd Complex (c n) *
              (H x * fourierChar (nu n) x) := by
          unfold syn Internal.perturbedSynthesisRaw
          rw [RCLike.inner_apply', map_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro n hn
          rw [map_mul]
          simp
          ring
        have htermInt (n : IntVec d) : Integrable
            (fun x ↦ starRingEnd Complex (c n) *
              (H x * fourierChar (nu n) x))
            (volume.restrict (unitCube d)) := by
          apply Integrable.const_mul
          refine hHint.mul_bdd (c := 1) (by
            apply Continuous.aestronglyMeasurable
            unfold fourierChar
            fun_prop) ?_
          apply Filter.Eventually.of_forall
          intro x
          show ‖fourierChar (nu n) x‖ ≤ (1 : Real)
          unfold fourierChar
          rw [Complex.norm_exp]
          norm_num
        have hintegral :
            (∫ x, inner Complex (syn x) (H x)
              ∂volume.restrict (unitCube d)) = (A : Complex) := by
          rw [integral_congr_ae (ae_of_all _ hpoint)]
          rw [integral_finsetSum D (fun n hn ↦ htermInt n)]
          change (∑ i ∈ D, ∫ x in unitCube d,
            starRingEnd Complex (c i) * (H x * fourierChar (nu i) x)) =
              ((∑ n ∈ D, ‖c n‖ ^ 2 : Real) : Complex)
          have hcast : ((∑ n ∈ D, ‖c n‖ ^ 2 : Real) : Complex) =
              ∑ n ∈ D, ((‖c n‖ ^ 2 : Real) : Complex) := by norm_cast
          rw [hcast]
          apply Finset.sum_congr rfl
          intro n hn
          rw [integral_const_mul]
          change starRingEnd Complex (c n) *
              inverseSampleOn (unitCube d) H (nu n) =
            ((‖c n‖ ^ 2 : Real) : Complex)
          rw [show inverseSampleOn (unitCube d) H (nu n) = c n from rfl,
            Complex.conj_mul']
          norm_cast
        have hinner : inner Complex synLp HLp = (A : Complex) := by
          rw [MeasureTheory.L2.inner_def]
          calc
            (∫ x, inner Complex (⇑synLp x) (⇑HLp x)
                ∂volume.restrict (unitCube d)) =
                ∫ x, inner Complex (syn x) (H x)
                  ∂volume.restrict (unitCube d) := by
              apply integral_congr_ae
              filter_upwards [hsynMem.coeFn_toLp, hHLp.coeFn_toLp] with x hs hH
              rw [hs, hH]
            _ = (A : Complex) := hintegral
        have hA : 0 ≤ A := by
          dsimp [A]
          positivity
        have hinner_bound : A ≤ ‖synLp‖ * ‖HLp‖ := by
          calc
            A = ‖(A : Complex)‖ := by simp [abs_of_nonneg hA]
            _ = ‖inner Complex synLp HLp‖ := by rw [hinner]
            _ ≤ ‖synLp‖ * ‖HLp‖ := norm_inner_le_norm _ _
        have hsyn_sq : ‖synLp‖ ^ 2 = sqNormOn (unitCube d) syn :=
          Internal.toLp_norm_sq_eq_sqNorm_hd (unitCube d) syn hsynMem
        have hH_sq : ‖HLp‖ ^ 2 = sqNormOn (unitCube d) H :=
          Internal.toLp_norm_sq_eq_sqNorm_hd (unitCube d) H hHLp
        have hsyn_upper : sqNormOn (unitCube d) syn ≤ upper * A :=
          hsynth_data.2.2.2
        have hsq : A ^ 2 ≤ A * (upper * sqNormOn (unitCube d) H) := by
          calc
            A ^ 2 ≤ (‖synLp‖ * ‖HLp‖) ^ 2 :=
              (sq_le_sq₀ hA
                (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hinner_bound
            _ = sqNormOn (unitCube d) syn * sqNormOn (unitCube d) H := by
              rw [mul_pow, hsyn_sq, hH_sq]
            _ ≤ (upper * A) * sqNormOn (unitCube d) H := by
              gcongr
              rw [← hH_sq]
              positivity
            _ = A * (upper * sqNormOn (unitCube d) H) := by ring
        by_cases hAz : A = 0
        · change A ≤ upper * sqNormOn (unitCube d) H
          rw [hAz, ← hH_sq]
          positivity
        · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hAz)
          change A ≤ upper * sqNormOn (unitCube d) H
          nlinarith [hsq] }
  refine ⟨⟨K, ?_, ?_⟩⟩
  · rfl
  · rfl

/-- Explicit bounds for a globally sanitized perturbation. -/
noncomputable def smallPerturbation_exponentialBounds_hd {d : Nat}
    (hd : 0 < d) (nu : IntVec d → RealVec d)
    (hnu : ∀ n, ‖nu n - integerEmbed n‖ ≤ perturbRadius d) :
    ExponentialBoundsHD nu :=
  (Classical.choice
    (smallPerturbation_exponentialBounds_hd_nonempty hd nu hnu)).val

/-- Finite analysis bounds yield full lattice summability. -/
theorem ExponentialBoundsHD.analysis_summable {d : Nat}
    {nu : IntVec d → RealVec d} (K : ExponentialBoundsHD nu)
    (H : RealVec d → Complex)
    (hHmeas : AEStronglyMeasurable H (volume.restrict (unitCube d)))
    (hHLp : MemLp H (2 : ENNReal) (volume.restrict (unitCube d))) :
    Summable (fun n : IntVec d ↦
      ‖inverseSampleOn (unitCube d) H (nu n)‖ ^ 2) ∧
      ∑' n : IntVec d, ‖inverseSampleOn (unitCube d) H (nu n)‖ ^ 2 ≤
        K.upper * sqNormOn (unitCube d) H := by
  let f : IntVec d → Real := fun n ↦
    ‖inverseSampleOn (unitCube d) H (nu n)‖ ^ 2
  have hf : 0 ≤ f := fun n ↦ sq_nonneg _
  have hfin : ∀ D : Finset (IntVec d), ∑ n ∈ D, f n ≤
      K.upper * sqNormOn (unitCube d) H := by
    intro D
    exact K.analysis_upper D H hHmeas hHLp
  have hsum : Summable f := summable_of_sum_le hf hfin
  exact ⟨hsum, hsum.tsum_le_of_sum_le hfin⟩

end AsymptoticallyIntegerHD
