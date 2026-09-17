import Theorem12.GenericAuxiliary
import Theorem12.FourierUniqueness
import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

noncomputable section

open MeasureTheory Set
open scoped BigOperators Topology

namespace Theorem12.Generic

/- Proof idea: transparently encode the centered sinc coefficient with the real sine
in the numerator and the complexified frequency difference in the denominator. -/
def sincCoeff (t : ℝ) (q : ℤ) : ℂ :=
  (Real.sin (Real.pi * t) : ℂ) /
    ((Real.pi : ℂ) * ((t - (q : ℝ) : ℝ) : ℂ))

/- Proof idea: transparently use the cancelled inverse-difference formula from the one-dimensional argument,
which is later identified with `sincCoeff t (q-k) - sincCoeff t q`. -/
def sincShiftCoeff (k : ℤ) (t : ℝ) (q : ℤ) : ℂ :=
  (Real.sin (Real.pi * t) : ℂ) / (Real.pi : ℂ) *
    (((t - (q : ℝ) + (k : ℝ) : ℝ) : ℂ)⁻¹ -
      ((t - (q : ℝ) : ℝ) : ℂ)⁻¹)

private theorem abs_sin_pi_le_pi_mul_abs_sub_int (t : ℝ) (q : ℤ) :
    |Real.sin (Real.pi * t)| ≤ Real.pi * |t - (q : ℝ)| := by
  have hperiod :
      |Real.sin (Real.pi * t)| =
        |Real.sin (Real.pi * (t - (q : ℝ)))| := by
    rw [show Real.pi * (t - (q : ℝ)) =
        Real.pi * t - (q : ℝ) * Real.pi by ring,
      Real.sin_sub_int_mul_pi]
    simp
  rw [hperiod]
  calc
    |Real.sin (Real.pi * (t - (q : ℝ)))| ≤
        |Real.pi * (t - (q : ℝ))| := Real.abs_sin_le_abs
    _ = Real.pi * |t - (q : ℝ)| := by
      rw [abs_mul, abs_of_pos Real.pi_pos]

private theorem norm_sincCoeff_le_one (t : ℝ)
    (htInt : ∀ ell : ℤ, t ≠ (ell : ℝ)) (q : ℤ) :
    ‖sincCoeff t q‖ ≤ 1 := by
  have htq : t - (q : ℝ) ≠ 0 := sub_ne_zero.mpr (htInt q)
  have hden : 0 < Real.pi * |t - (q : ℝ)| :=
    mul_pos Real.pi_pos (abs_pos.mpr htq)
  rw [sincCoeff, norm_div, norm_mul]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  have hsin := abs_sin_pi_le_pi_mul_abs_sub_int t q
  rw [abs_of_pos Real.pi_pos]
  rw [div_le_iff₀ hden]
  simpa only [one_mul] using hsin

private theorem sincShiftCoeff_eq_sub (k q : ℤ) (t : ℝ)
    (htInt : ∀ ell : ℤ, t ≠ (ell : ℝ)) :
    sincShiftCoeff k t q = sincCoeff t (q - k) - sincCoeff t q := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hq : ((t - (q : ℝ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast sub_ne_zero.mpr (htInt q)
  have hqk : ((t - ((q - k : ℤ) : ℝ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast sub_ne_zero.mpr (htInt (q - k))
  rw [sincShiftCoeff, sincCoeff, sincCoeff]
  push_cast
  field_simp
  ring

private theorem norm_sincShiftCoeff_le_two (k q : ℤ) (t : ℝ)
    (htInt : ∀ ell : ℤ, t ≠ (ell : ℝ)) :
    ‖sincShiftCoeff k t q‖ ≤ 2 := by
  rw [sincShiftCoeff_eq_sub k q t htInt]
  calc
    ‖sincCoeff t (q - k) - sincCoeff t q‖ ≤
        ‖sincCoeff t (q - k)‖ + ‖sincCoeff t q‖ := norm_sub_le _ _
    _ ≤ 1 + 1 := add_le_add
      (norm_sincCoeff_le_one t htInt (q - k))
      (norm_sincCoeff_le_one t htInt q)
    _ = 2 := by norm_num

private theorem norm_sincShiftCoeff_tail (k q : ℤ) (t : ℝ)
    (ht : |t| < 3 / 2) (htInt : ∀ ell : ℤ, t ≠ (ell : ℝ))
    (hq : 4 * (|(k : ℝ)| + 2) ≤ |(q : ℝ)|) :
    ‖sincShiftCoeff k t q‖ ≤ 4 * |(k : ℝ)| / (q : ℝ) ^ 2 := by
  let a : ℝ := t - (q : ℝ) + (k : ℝ)
  let b : ℝ := t - (q : ℝ)
  have ha : a ≠ 0 := by
    dsimp [a]
    rw [show t - (q : ℝ) + (k : ℝ) = t - ((q - k : ℤ) : ℝ) by push_cast; ring]
    exact sub_ne_zero.mpr (htInt (q - k))
  have hb : b ≠ 0 := by
    exact sub_ne_zero.mpr (htInt q)
  have hinv : ((a : ℂ)⁻¹ - (b : ℂ)⁻¹) = (-(k : ℝ) : ℂ) / ((a : ℂ) * (b : ℂ)) := by
    rw [inv_sub_inv (by exact_mod_cast ha) (by exact_mod_cast hb)]
    congr 1
    have hba : b - a = -(k : ℝ) := by
      dsimp [a, b]
      ring
    exact_mod_cast hba
  have hqabs : 0 < |(q : ℝ)| := by
    have hk0 : 0 ≤ |(k : ℝ)| := abs_nonneg _
    linarith
  have hbLower : |(q : ℝ)| / 2 ≤ |b| := by
    have hrev := abs_sub_abs_le_abs_sub (q : ℝ) t
    rw [abs_sub_comm] at hrev
    dsimp [b]
    nlinarith [abs_nonneg (k : ℝ)]
  have hqk : |(q : ℝ)| - |(k : ℝ)| ≤ |((q : ℝ) - (k : ℝ))| :=
    abs_sub_abs_le_abs_sub (q : ℝ) (k : ℝ)
  have hqt : |((q : ℝ) - (k : ℝ))| - |t| ≤
      |((q : ℝ) - (k : ℝ)) - t| :=
    abs_sub_abs_le_abs_sub ((q : ℝ) - (k : ℝ)) t
  have haLower : |(q : ℝ)| / 2 ≤ |a| := by
    have heqabs : |((q : ℝ) - (k : ℝ)) - t| = |a| := by
      dsimp [a]
      rw [abs_sub_comm]
      congr 1
      ring
    rw [heqabs] at hqt
    nlinarith
  have hprod : (q : ℝ) ^ 2 / 4 ≤ |a| * |b| := by
    have ha0 : 0 ≤ |a| := abs_nonneg _
    have hb0 : 0 ≤ |b| := abs_nonneg _
    have hhalf0 : 0 ≤ |(q : ℝ)| / 2 := by positivity
    calc
      (q : ℝ) ^ 2 / 4 = (|(q : ℝ)| / 2) * (|(q : ℝ)| / 2) := by
        rw [← sq_abs (q : ℝ)]
        ring
      _ ≤ (|(q : ℝ)| / 2) * |b| :=
        mul_le_mul_of_nonneg_left hbLower hhalf0
      _ ≤ |a| * |b| := mul_le_mul_of_nonneg_right haLower hb0
  have hprodpos : 0 < |a| * |b| := mul_pos (abs_pos.mpr ha) (abs_pos.mpr hb)
  have hqSqPos : 0 < (q : ℝ) ^ 2 := by
    rw [← sq_abs]
    exact sq_pos_of_pos hqabs
  have hfrac : |(k : ℝ)| / (|a| * |b|) ≤
      4 * |(k : ℝ)| / (q : ℝ) ^ 2 := by
    have hden : (q : ℝ) ^ 2 / 4 ≤ |a| * |b| := hprod
    have hbase := div_le_div_of_nonneg_left (abs_nonneg (k : ℝ))
      (by positivity : 0 < (q : ℝ) ^ 2 / 4) hden
    calc
      |(k : ℝ)| / (|a| * |b|) ≤ |(k : ℝ)| / ((q : ℝ) ^ 2 / 4) := hbase
      _ = 4 * |(k : ℝ)| / (q : ℝ) ^ 2 := by field_simp
  have hsinpi : |Real.sin (Real.pi * t)| / Real.pi ≤ 1 := by
    rw [div_le_iff₀ Real.pi_pos]
    exact (Real.abs_sin_le_one _).trans (by linarith [Real.two_le_pi])
  rw [sincShiftCoeff]
  change ‖(Real.sin (Real.pi * t) : ℂ) / (Real.pi : ℂ) *
    (((a : ℂ)⁻¹ - (b : ℂ)⁻¹))‖ ≤ _
  rw [hinv, norm_mul, norm_div, norm_div, norm_mul]
  simp only [Complex.norm_real, Real.norm_eq_abs, norm_neg,
    abs_of_pos Real.pi_pos]
  have hfrac0 : 0 ≤ |(k : ℝ)| / (|a| * |b|) := by positivity
  calc
    |Real.sin (Real.pi * t)| / Real.pi *
        (|(k : ℝ)| / (|a| * |b|)) ≤
      1 * (|(k : ℝ)| / (|a| * |b|)) :=
        mul_le_mul_of_nonneg_right hsinpi hfrac0
    _ ≤ 4 * |(k : ℝ)| / (q : ℝ) ^ 2 := by simpa using hfrac

/- Proof idea: rewrite the inverse difference with numerator `-k*sin(pi*t)`, use two
denominators away from finitely many central indices, and use sine-distance cancellation there. -/
theorem norm_sincShiftCoeff_le (k : ℤ) :
    ∃ Ck : ℝ, 0 ≤ Ck ∧ ∀ t : ℝ, |t| < 3 / 2 →
      (∀ ell : ℤ, t ≠ (ell : ℝ)) → ∀ q : ℤ,
        ‖sincShiftCoeff k t q‖ ≤ Ck / (1 + (q : ℝ) ^ 2) := by
  let Q : ℝ := 4 * (|(k : ℝ)| + 2)
  let Ck : ℝ := 2 * (1 + Q ^ 2) + 4 * |(k : ℝ)|
  have hQpos : 0 < Q := by
    dsimp [Q]
    positivity
  have hCnonneg : 0 ≤ Ck := by
    dsimp [Ck]
    positivity
  refine ⟨Ck, hCnonneg, ?_⟩
  intro t ht htInt q
  by_cases hcentral : |(q : ℝ)| < Q
  · have hqSq : (q : ℝ) ^ 2 < Q ^ 2 := by
      rw [← sq_abs (q : ℝ)]
      exact (sq_lt_sq₀ (abs_nonneg _) hQpos.le).mpr hcentral
    have htwo := norm_sincShiftCoeff_le_two k q t htInt
    have hdenpos : 0 < 1 + (q : ℝ) ^ 2 := by positivity
    rw [le_div_iff₀ hdenpos]
    dsimp [Ck]
    nlinarith [sq_nonneg Q, abs_nonneg (k : ℝ)]
  · have htail : Q ≤ |(q : ℝ)| := le_of_not_gt hcentral
    have htail' : 4 * (|(k : ℝ)| + 2) ≤ |(q : ℝ)| := by
      simpa [Q] using htail
    have hraw := norm_sincShiftCoeff_tail k q t ht htInt htail'
    have hqabs : 0 < |(q : ℝ)| := hQpos.trans_le htail
    have hqSqPos : 0 < (q : ℝ) ^ 2 := by
      rw [← sq_abs]
      positivity
    have hqSqOne : 1 ≤ (q : ℝ) ^ 2 := by
      have hQeight : 8 ≤ Q := by
        dsimp [Q]
        nlinarith [abs_nonneg (k : ℝ)]
      have : 8 ≤ |(q : ℝ)| := hQeight.trans htail
      rw [← sq_abs]
      nlinarith
    have hCbig : 8 * |(k : ℝ)| ≤ Ck := by
      dsimp [Ck, Q]
      nlinarith [sq_nonneg (4 * (|(k : ℝ)| + 2)), abs_nonneg (k : ℝ)]
    have hfrac : 4 * |(k : ℝ)| / (q : ℝ) ^ 2 ≤
        Ck / (1 + (q : ℝ) ^ 2) := by
      rw [div_le_div_iff₀ hqSqPos (by positivity : 0 < 1 + (q : ℝ) ^ 2)]
      nlinarith [abs_nonneg (k : ℝ)]
    exact hraw.trans hfrac

/- Proof idea: transparently define the integer-indexed complex `tsum` with the positive
AddCircle character written through the canonical representative. -/
def sincShiftSeries (k : ℤ) (t : ℝ) (y : AddCircle (1 : ℝ)) : ℂ :=
  ∑' q : ℤ, sincShiftCoeff k t q *
    Complex.exp
      (((2 * Real.pi : ℝ) : ℂ) * Complex.I * (q : ℂ) * (unitRep y : ℂ))

private theorem fourier_eq_exp_unitRep (q : ℤ) (y : AddCircle (1 : ℝ)) :
    fourier q y = Complex.exp
      (((2 * Real.pi : ℝ) : ℂ) * Complex.I * (q : ℂ) * (unitRep y : ℂ)) := by
  calc
    fourier q y = fourier q ((unitRep y : ℝ) : AddCircle (1 : ℝ)) := by
      rw [coe_unitRep]
    _ = _ := by
      rw [fourier_coe_apply]
      norm_num

private theorem integrable_of_continuous_addCircle
    {f : AddCircle (1 : ℝ) → ℂ} (hf : Continuous f) :
    Integrable f AddCircle.haarAddCircle := by
  rw [← MeasureTheory.integrableOn_univ]
  exact ContinuousOn.integrableOn_compact isCompact_univ hf.continuousOn

/- Proof idea: apply the Weierstrass M-test using `norm_sincShiftCoeff_le` and quadratic summability,
then identify each representative exponential with the native continuous integer character. -/
theorem continuous_sincShiftSeries (k : ℤ) (t : ℝ) (ht : |t| < 3 / 2)
    (htInt : ∀ ell : ℤ, t ≠ (ell : ℝ)) :
    HasSumUniformlyOn
        (fun q : ℤ => fun y : AddCircle (1 : ℝ) => sincShiftCoeff k t q *
          Complex.exp
            (((2 * Real.pi : ℝ) : ℂ) * Complex.I * (q : ℂ) * (unitRep y : ℂ)))
        (sincShiftSeries k t) Set.univ ∧
      Continuous (sincShiftSeries k t) := by
  obtain ⟨Ck, hCk, hbound⟩ := norm_sincShiftCoeff_le k
  let u : ℤ → ℝ := fun q => Ck / (1 + (q : ℝ) ^ 2)
  let term : ℤ → AddCircle (1 : ℝ) → ℂ := fun q y =>
    sincShiftCoeff k t q *
      Complex.exp
        (((2 * Real.pi : ℝ) : ℂ) * Complex.I * (q : ℂ) * (unitRep y : ℂ))
  have hu : Summable u := by
    simpa only [u, div_eq_mul_inv] using
      summable_one_add_int_sq_inv.mul_left Ck
  have hmajor : ∀ q y, y ∈ (Set.univ : Set (AddCircle (1 : ℝ))) →
      ‖term q y‖ ≤ u q := by
    intro q y _
    have hchar : ‖fourier q y‖ = 1 := by
      rw [fourier_apply]
      exact Circle.norm_coe _
    change ‖sincShiftCoeff k t q * Complex.exp
      (((2 * Real.pi : ℝ) : ℂ) * Complex.I * (q : ℂ) * (unitRep y : ℂ))‖ ≤
        Ck / (1 + (q : ℝ) ^ 2)
    rw [← fourier_eq_exp_unitRep q y, norm_mul, hchar, mul_one]
    exact hbound t ht htInt q
  have htend : TendstoUniformlyOn
      (fun s y => ∑ q ∈ s, term q y)
      (fun y => ∑' q, term q y) Filter.atTop Set.univ :=
    tendstoUniformlyOn_tsum hu hmajor
  have hsum : HasSumUniformlyOn term (sincShiftSeries k t) Set.univ := by
    rw [hasSumUniformlyOn_iff_tendstoUniformlyOn]
    change TendstoUniformlyOn (fun s y => ∑ q ∈ s, term q y)
      (fun y => ∑' q, term q y) Filter.atTop Set.univ
    exact htend
  refine ⟨hsum, ?_⟩
  rw [← continuousOn_univ]
  apply htend.continuousOn
  apply Filter.Eventually.frequently
  filter_upwards with s
  apply Continuous.continuousOn
  apply continuous_finsetSum
  intro q _
  have hfourier : Continuous fun y : AddCircle (1 : ℝ) => fourier q y :=
    map_continuous (fourier q)
  change Continuous fun y : AddCircle (1 : ℝ) => sincShiftCoeff k t q *
    Complex.exp
      (((2 * Real.pi : ℝ) : ℂ) * Complex.I * (q : ℂ) * (unitRep y : ℂ))
  have hexp : (fun y : AddCircle (1 : ℝ) => Complex.exp
      (((2 * Real.pi : ℝ) : ℂ) * Complex.I * (q : ℂ) * (unitRep y : ℂ))) =
      fun y => fourier q y := by
    funext y
    exact (fourier_eq_exp_unitRep q y).symm
  have hexpcont : Continuous fun y : AddCircle (1 : ℝ) => Complex.exp
      (((2 * Real.pi : ℝ) : ℂ) * Complex.I * (q : ℂ) * (unitRep y : ℂ)) := by
    rw [hexp]
    exact hfourier
  exact continuous_const.mul hexpcont

/- Proof idea: interchange the uniformly absolutely convergent series and Haar integral,
apply integer-character orthogonality, and retain only the term with index `q=n`. -/
theorem fourierCoeff_sincShiftSeries (k n : ℤ) (t : ℝ) (ht : |t| < 3 / 2)
    (htInt : ∀ ell : ℤ, t ≠ (ell : ℝ)) :
    fourierCoeff (sincShiftSeries k t) n = sincShiftCoeff k t n := by
  let term : ℤ → AddCircle (1 : ℝ) → ℂ := fun q y =>
    sincShiftCoeff k t q * fourier q y
  let F : ℤ → AddCircle (1 : ℝ) → ℂ := fun q y => fourier (-n) y * term q y
  obtain ⟨Ck, hCk, hbound⟩ := norm_sincShiftCoeff_le k
  let u : ℤ → ℝ := fun q => Ck / (1 + (q : ℝ) ^ 2)
  have hu : Summable u := by
    simpa only [u, div_eq_mul_inv] using
      summable_one_add_int_sq_inv.mul_left Ck
  have hcoeff : Summable fun q : ℤ => ‖sincShiftCoeff k t q‖ :=
    hu.of_norm_bounded fun q => by
      simpa only [Real.norm_eq_abs, abs_norm] using hbound t ht htInt q
  have hFint : ∀ q, Integrable (F q) AddCircle.haarAddCircle := by
    intro q
    apply integrable_of_continuous_addCircle
    dsimp [F, term]
    fun_prop
  have hFnorm (q : ℤ) :
      (∫ y : AddCircle (1 : ℝ), ‖F q y‖ ∂AddCircle.haarAddCircle) =
        ‖sincShiftCoeff k t q‖ := by
    have hnorm : ∀ y : AddCircle (1 : ℝ),
        ‖F q y‖ = ‖sincShiftCoeff k t q‖ := by
      intro y
      simp only [F, term, norm_mul, fourier_apply, Circle.norm_coe,
        one_mul, mul_one]
    simp_rw [hnorm]
    simp
  have hFnormSum : Summable fun q : ℤ =>
      ∫ y : AddCircle (1 : ℝ), ‖F q y‖ ∂AddCircle.haarAddCircle := by
    simpa only [hFnorm] using hcoeff
  have hinter := MeasureTheory.integral_tsum_of_summable_integral_norm hFint hFnormSum
  have hpoint (y : AddCircle (1 : ℝ)) :
      fourier (-n) y * sincShiftSeries k t y = ∑' q, F q y := by
    have hterm : Summable fun q => term q y := by
      apply hcoeff.of_norm_bounded
      intro q
      simp only [term, norm_mul, fourier_apply, Circle.norm_coe, mul_one]
      exact le_rfl
    rw [sincShiftSeries]
    simp_rw [← fourier_eq_exp_unitRep]
    exact (hterm.tsum_mul_left (fourier (-n) y)).symm
  have hfourierCoeff (q : ℤ) :
      fourierCoeff (fun y : AddCircle (1 : ℝ) => fourier q y) n =
        if n = q then 1 else 0 := by
    change fourierCoeff (fourier q) n = if n = q then 1 else 0
    have h := congrFun (fourierCoeff_fourier (T := (1 : ℝ)) q) n
    simpa [Pi.single_apply] using h
  rw [fourierCoeff]
  simp only [smul_eq_mul]
  calc
    (∫ y, fourier (-n) y * sincShiftSeries k t y
        ∂AddCircle.haarAddCircle) =
        ∫ y, ∑' q, F q y ∂AddCircle.haarAddCircle :=
      integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = ∑' q, ∫ y, F q y ∂AddCircle.haarAddCircle := hinter.symm
    _ = ∑' q, sincShiftCoeff k t q * (if n = q then 1 else 0) := by
      congr 1
      funext q
      rw [show (∫ y, F q y ∂AddCircle.haarAddCircle) =
          fourierCoeff (fun y => sincShiftCoeff k t q * fourier q y) n by rfl,
        fourierCoeff.const_mul, hfourierCoeff]
    _ = sincShiftCoeff k t n := by
      simp

/- Proof idea: transparently exponentiate `2*pi*I*t*(unitRep y-1/2)`; no continuity
claim is made because a noninteger frequency generally jumps at the AddCircle seam. -/
def centeredExp (t : ℝ) (y : AddCircle (1 : ℝ)) : ℂ :=
  Complex.exp
    (((2 * Real.pi : ℝ) : ℂ) * Complex.I * (t : ℂ) *
      ((unitRep y - 1 / 2 : ℝ) : ℂ))

private theorem centeredExp_eq_liftIco (t : ℝ) :
    centeredExp t = AddCircle.liftIco (1 : ℝ) 0 (fun u : ℝ =>
      Complex.exp
        (((2 * Real.pi : ℝ) : ℂ) * Complex.I * (t : ℂ) *
          (((u - 1 / 2 : ℝ) : ℂ)))) := by
  funext y
  rw [← coe_unitRep y,
    AddCircle.liftIco_zero_coe_apply (unitRep_mem_Ico y)]
  rw [centeredExp, unitRep_coe_eq_fract,
    Int.fract_eq_self.mpr (unitRep_mem_Ico y)]

private theorem intervalIntegral_exp_mul_complex_local {a b : ℝ} {c : ℂ}
    (hc : c ≠ 0) :
    (∫ x in a..b, Complex.exp (c * x)) =
      (Complex.exp (c * b) - Complex.exp (c * a)) / c := by
  have D : ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => Complex.exp (c * y) / c)
        (Complex.exp (c * x)) x := by
    intro x
    conv => congr
    rw [← mul_div_cancel_right₀ (Complex.exp (c * x)) hc]
    apply ((Complex.hasDerivAt_exp _).comp x _).div_const c
    simpa only [mul_one] using!
      ((hasDerivAt_id (x : ℂ)).const_mul _).comp_ofReal
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => D x) ((by fun_prop : Continuous
        (fun x : ℝ => Complex.exp (c * x))).intervalIntegrable a b)]
  ring

/- Proof idea: move the Haar integral to `Ico 0 1`, integrate the complex exponential
explicitly, and simplify the endpoint factor to the centered sine coefficient. -/
theorem fourierCoeff_centeredExp (t : ℝ)
    (htInt : ∀ ell : ℤ, t ≠ (ell : ℝ)) (n : ℤ) :
    fourierCoeff (centeredExp t) n = sincCoeff t n := by
  let raw : ℝ → ℂ := fun u => Complex.exp
    (((2 * Real.pi : ℝ) : ℂ) * Complex.I * (t : ℂ) *
      (((u - 1 / 2 : ℝ) : ℂ)))
  let c : ℂ := ((2 * Real.pi : ℝ) : ℂ) * Complex.I *
    ((t - (n : ℝ) : ℝ) : ℂ)
  let phase : ℂ := -((Real.pi : ℂ) * Complex.I * (t : ℂ))
  have hc : c ≠ 0 := by
    dsimp [c]
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact_mod_cast (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero)
      · exact Complex.I_ne_zero
    · exact_mod_cast sub_ne_zero.mpr (htInt n)
  have hintegrand (x : ℝ) :
      fourier (-n) (x : AddCircle (1 : ℝ)) * raw x =
        Complex.exp phase * Complex.exp (c * x) := by
    rw [fourier_coe_apply]
    norm_num
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    dsimp [raw, phase, c]
    push_cast
    ring
  have hint :
      (∫ x in (0 : ℝ)..1, fourier (-n) (x : AddCircle (1 : ℝ)) * raw x) =
        Complex.exp phase *
          ((Complex.exp c - 1) / c) := by
    calc
      (∫ x in (0 : ℝ)..1, fourier (-n) (x : AddCircle (1 : ℝ)) * raw x) =
          ∫ x in (0 : ℝ)..1, Complex.exp phase * Complex.exp (c * x) := by
        apply intervalIntegral.integral_congr
        intro x _
        exact hintegrand x
      _ = Complex.exp phase *
          (∫ x in (0 : ℝ)..1, Complex.exp (c * x)) :=
        intervalIntegral.integral_const_mul _ _
      _ = Complex.exp phase * ((Complex.exp c - 1) / c) := by
        rw [intervalIntegral_exp_mul_complex_local hc]
        simp
  rw [centeredExp_eq_liftIco, fourierCoeff_liftIco_eq,
    fourierCoeffOn_eq_integral]
  norm_num
  norm_num [raw] at hint
  rw [hint]
  dsimp [sincCoeff, phase, c]
  have hnexp : Complex.exp
      (((2 * Real.pi : ℝ) : ℂ) * Complex.I * (n : ℂ)) = 1 := by
    rw [show ((2 * Real.pi : ℝ) : ℂ) * Complex.I * (n : ℂ) =
        (n : ℤ) * (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring]
    simpa using Complex.exp_int_mul_two_pi_mul_I n
  have hcexp : Complex.exp
      (((2 * Real.pi : ℝ) : ℂ) * Complex.I *
        ((t - (n : ℝ) : ℝ) : ℂ)) =
      Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I * (t : ℂ)) := by
    rw [show ((2 * Real.pi : ℝ) : ℂ) * Complex.I *
        ((t - (n : ℝ) : ℝ) : ℂ) =
      ((2 * Real.pi : ℝ) : ℂ) * Complex.I * (t : ℂ) -
        ((2 * Real.pi : ℝ) : ℂ) * Complex.I * (n : ℂ) by push_cast; ring,
      Complex.exp_sub]
    rw [hnexp]
    simp
  rw [hcexp]
  have htrig : Complex.exp (-((Real.pi : ℂ) * Complex.I * (t : ℂ))) *
      (Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I * (t : ℂ)) - 1) =
      2 * (Real.sin (Real.pi * t) : ℂ) * Complex.I := by
    rw [show -((Real.pi : ℂ) * Complex.I * (t : ℂ)) =
        ((-(Real.pi * t) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      show ((2 * Real.pi : ℝ) : ℂ) * Complex.I * (t : ℂ) =
        (((Real.pi * t : ℝ) : ℂ) * Complex.I) +
          (((Real.pi * t : ℝ) : ℂ) * Complex.I) by push_cast; ring,
      Complex.exp_add, Complex.exp_mul_I, Complex.exp_mul_I]
    push_cast
    simp only [Complex.cos_neg, Complex.sin_neg]
    have hunit : Complex.cos ((Real.pi : ℂ) * (t : ℂ)) ^ 2 +
        Complex.sin ((Real.pi : ℂ) * (t : ℂ)) ^ 2 = 1 :=
      Complex.cos_sq_add_sin_sq ((Real.pi : ℂ) * (t : ℂ))
    calc
      (Complex.cos ((Real.pi : ℂ) * (t : ℂ)) +
            (-Complex.sin ((Real.pi : ℂ) * (t : ℂ))) * Complex.I) *
          ((Complex.cos ((Real.pi : ℂ) * (t : ℂ)) +
              Complex.sin ((Real.pi : ℂ) * (t : ℂ)) * Complex.I) *
            (Complex.cos ((Real.pi : ℂ) * (t : ℂ)) +
              Complex.sin ((Real.pi : ℂ) * (t : ℂ)) * Complex.I) - 1) =
          2 * Complex.sin ((Real.pi : ℂ) * (t : ℂ)) * Complex.I *
            (Complex.cos ((Real.pi : ℂ) * (t : ℂ)) ^ 2 +
              Complex.sin ((Real.pi : ℂ) * (t : ℂ)) ^ 2) := by
            rw [← hunit]
            ring_nf
            rw [Complex.I_sq]
            rw [show Complex.I ^ 3 = -Complex.I by
              rw [pow_succ, Complex.I_sq]
              ring]
            ring
      _ = 2 * Complex.sin ((Real.pi : ℂ) * (t : ℂ)) * Complex.I := by
        rw [hunit, mul_one]
  rw [← mul_div_assoc, htrig]
  push_cast
  have htn : ((t : ℂ) - (n : ℂ)) ≠ 0 := by
    exact_mod_cast sub_ne_zero.mpr (htInt n)
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

/- Proof idea: transparently multiply the centered exponential by the positive integer
character minus one, using the canonical representative only as its evaluated normal form. -/
def shiftedCenteredExp (k : ℤ) (t : ℝ) (y : AddCircle (1 : ℝ)) : ℂ :=
  (Complex.exp
      (((2 * Real.pi : ℝ) : ℂ) * Complex.I * (k : ℂ) * (unitRep y : ℂ)) - 1) *
    centeredExp t y

private theorem measurable_unitRep : Measurable unitRep := by
  change Measurable (fun x : AddCircle (1 : ℝ) =>
    (((AddCircle.measurableEquivIco (1 : ℝ) 0) x :
      Set.Ico (0 : ℝ) (0 + 1)) : ℝ))
  exact measurable_subtype_coe.comp
    (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable

private theorem integrable_centeredExp (t : ℝ) :
    Integrable (centeredExp t) AddCircle.haarAddCircle := by
  have hmeas : Measurable (centeredExp t) := by
    unfold centeredExp
    exact Complex.continuous_exp.measurable.comp
      (((measurable_const.mul measurable_const).mul measurable_const).mul
        (Complex.measurable_ofReal.comp
          (measurable_unitRep.sub measurable_const)))
  refine Integrable.of_bound hmeas.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun y => ?_)
  rw [centeredExp, Complex.norm_exp]
  simp

private theorem fourierCoeff_fourier_mul (f : AddCircle (1 : ℝ) → ℂ)
    (k n : ℤ) :
    fourierCoeff (fun y => fourier k y * f y) n =
      fourierCoeff f (n - k) := by
  unfold fourierCoeff
  apply integral_congr_ae
  filter_upwards with y
  simp only [smul_eq_mul]
  rw [show fourier (-n) y * (fourier k y * f y) =
      (fourier (-n) y * fourier k y) * f y by ring,
    ← fourier_add]
  congr 2
  ring

private theorem fourierCoeff_sub_of_integrable
    (f g : AddCircle (1 : ℝ) → ℂ)
    (hf : Integrable f AddCircle.haarAddCircle)
    (hg : Integrable g AddCircle.haarAddCircle) (n : ℤ) :
    fourierCoeff (fun y => f y - g y) n =
      fourierCoeff f n - fourierCoeff g n := by
  unfold fourierCoeff
  simp only [smul_sub]
  exact integral_sub (hf.fourier_smul (-n)) (hg.fourier_smul (-n))

/- Proof idea: expand both Fourier integrals, shift the negative coefficient index from
`n` to `n-k`, apply `fourierCoeff_centeredExp` twice, and normalize to `sincShiftCoeff`. -/
theorem fourierCoeff_shiftedCenteredExp (k n : ℤ) (t : ℝ)
    (htInt : ∀ ell : ℤ, t ≠ (ell : ℝ)) :
    fourierCoeff (shiftedCenteredExp k t) n = sincShiftCoeff k t n := by
  have hcenter : Integrable (centeredExp t) AddCircle.haarAddCircle :=
    integrable_centeredExp t
  have hmul : Integrable
      (fun y : AddCircle (1 : ℝ) => fourier k y * centeredExp t y)
      AddCircle.haarAddCircle := by
    simpa only [smul_eq_mul] using hcenter.fourier_smul k
  have hshift : shiftedCenteredExp k t = fun y =>
      fourier k y * centeredExp t y - centeredExp t y := by
    funext y
    rw [shiftedCenteredExp, fourier_eq_exp_unitRep]
    ring
  rw [hshift, fourierCoeff_sub_of_integrable _ _ hmul hcenter n,
    fourierCoeff_fourier_mul, fourierCoeff_centeredExp t htInt (n - k),
    fourierCoeff_centeredExp t htInt n]
  exact (sincShiftCoeff_eq_sub k n t htInt).symm

private theorem integrable_shiftedCenteredExp (k : ℤ) (t : ℝ) :
    Integrable (shiftedCenteredExp k t) AddCircle.haarAddCircle := by
  have hcenter : Integrable (centeredExp t) AddCircle.haarAddCircle :=
    integrable_centeredExp t
  have hmul : Integrable
      (fun y : AddCircle (1 : ℝ) => fourier k y * centeredExp t y)
      AddCircle.haarAddCircle := by
    simpa only [smul_eq_mul] using hcenter.fourier_smul k
  have hshift : shiftedCenteredExp k t = fun y =>
      fourier k y * centeredExp t y - centeredExp t y := by
    funext y
    rw [shiftedCenteredExp, fourier_eq_exp_unitRep]
    ring
  rw [hshift]
  exact hmul.sub hcenter

/- Proof idea: subtract the two integrable functions, use `fourierCoeff_sincShiftSeries` and `fourierCoeff_shiftedCenteredExp` to annihilate
every Fourier coefficient, and apply the generic L1 Fourier uniqueness theorem `ae_eq_zero_of_all_fourierCoeff_eq_zero`. -/
theorem sincShiftSeries_ae_eq (k : ℤ) (t : ℝ) (ht : |t| < 3 / 2)
    (htInt : ∀ ell : ℤ, t ≠ (ell : ℝ)) :
    sincShiftSeries k t =ᵐ[AddCircle.haarAddCircle] shiftedCenteredExp k t := by
  have hseries : Integrable (sincShiftSeries k t)
      AddCircle.haarAddCircle :=
    integrable_of_continuous_addCircle
      (continuous_sincShiftSeries k t ht htInt).2
  have hshift : Integrable (shiftedCenteredExp k t)
      AddCircle.haarAddCircle := integrable_shiftedCenteredExp k t
  have hdiff : Integrable
      (fun y => sincShiftSeries k t y - shiftedCenteredExp k t y)
      AddCircle.haarAddCircle := hseries.sub hshift
  have hcoeff : ∀ n : ℤ,
      fourierCoeff
          (fun y => sincShiftSeries k t y - shiftedCenteredExp k t y) n = 0 := by
    intro n
    rw [fourierCoeff_sub_of_integrable _ _ hseries hshift n,
      fourierCoeff_sincShiftSeries k n t ht htInt,
      fourierCoeff_shiftedCenteredExp k n t htInt, sub_self]
  have hzero := ae_eq_zero_of_all_fourierCoeff_eq_zero _ hdiff hcoeff
  filter_upwards [hzero] with y hy
  change sincShiftSeries k t y - shiftedCenteredExp k t y = 0 at hy
  exact sub_eq_zero.mp hy

/- Proof idea: define the product continuously on `[0,1]`, note that both endpoint values
are zero because the integer-character difference vanishes, and descend through AddCircle. -/
theorem continuous_shiftedCenteredExp (k : ℤ) (t : ℝ) :
    Continuous (shiftedCenteredExp k t) := by
  let raw : ℝ → ℂ := fun u =>
    (Complex.exp
        (((2 * Real.pi : ℝ) : ℂ) * Complex.I * (k : ℂ) * (u : ℂ)) - 1) *
      Complex.exp
        (((2 * Real.pi : ℝ) : ℂ) * Complex.I * (t : ℂ) *
          (((u - 1 / 2 : ℝ) : ℂ)))
  have hraw_cont : Continuous raw := by
    dsimp [raw]
    fun_prop
  have hraw_zero : raw 0 = raw 1 := by
    have hkexp :
        Complex.exp
          (((2 * Real.pi : ℝ) : ℂ) * Complex.I * (k : ℂ) * (1 : ℂ)) = 1 := by
      rw [show ((2 * Real.pi : ℝ) : ℂ) * Complex.I * (k : ℂ) * (1 : ℂ) =
          (k : ℤ) * (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring]
      simpa using Complex.exp_int_mul_two_pi_mul_I k
    have hzero0 : raw 0 = 0 := by
      simp [raw]
    have hzero1 : raw 1 = 0 := by
      dsimp [raw]
      rw [hkexp]
      simp
    exact hzero0.trans hzero1.symm
  have hlift : Continuous (AddCircle.liftIco (1 : ℝ) 0 raw) :=
    AddCircle.liftIco_zero_continuous hraw_zero hraw_cont.continuousOn
  have heq : shiftedCenteredExp k t = AddCircle.liftIco (1 : ℝ) 0 raw := by
    funext y
    rw [← coe_unitRep y,
      AddCircle.liftIco_zero_coe_apply (unitRep_mem_Ico y)]
    rw [shiftedCenteredExp, centeredExp, unitRep_coe_eq_fract,
      Int.fract_eq_self.mpr (unitRep_mem_Ico y)]
  rw [heq]
  exact hlift

/- Proof idea: combine continuity of both sides with their AE equality; full support of
AddCircle Haar measure rules out any nonempty open set on which the values differ. -/
theorem sinc_shift_identity (k : ℤ) (t : ℝ) (ht : |t| < 3 / 2)
    (htInt : ∀ ell : ℤ, t ≠ (ell : ℝ)) :
    ∀ y : AddCircle (1 : ℝ),
      sincShiftSeries k t y = shiftedCenteredExp k t y := by
  have hfun : sincShiftSeries k t = shiftedCenteredExp k t :=
    MeasureTheory.Measure.eq_of_ae_eq
      (sincShiftSeries_ae_eq k t ht htInt)
      (continuous_sincShiftSeries k t ht htInt).2
      (continuous_shiftedCenteredExp k t)
  exact fun y => congrFun hfun y

end Theorem12.Generic
