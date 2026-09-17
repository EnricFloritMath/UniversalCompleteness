import UniversalCompletenessHD.PoleCoordinates
import Theorem12.SincIdentity

/-!
# Arbitrary-phase noninteger shifted-sinc identity

The raw coefficient and descended
shifted exponential are exact aliases of the proved one-dimensional
closure.  Every semantic theorem retains an explicit nonintegrality premise.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators Topology

namespace UniversalCompletenessHD.Internal

/- Apply floor inequalities to `t + 1/2`; the remainder is in
the exact half-open centered interval. -/
private theorem sincCenteredPhase_mem (t : Real) :
    (-1 / 2 : Real) ≤ sincCenteredPhase t ∧
      sincCenteredPhase t < 1 / 2 := by
  have hfloor := Int.floor_le (t + 1 / 2)
  have hlt := Int.lt_floor_add_one (t + 1 / 2)
  unfold sincCenteredPhase sincCenterIndex
  constructor <;> linarith

/- An integer equality for the centered remainder would write
the original phase as a sum of two integers. -/
private theorem sincCenteredPhase_noninteger (t : Real)
    (ht : ∀ r : Int, t ≠ (r : Real)) :
    ∀ r : Int, sincCenteredPhase t ≠ (r : Real) := by
  intro r hr
  apply ht (sincCenterIndex t + r)
  unfold sincCenteredPhase at hr
  push_cast
  linarith

/- Translate sine by the integer center, normalize both
nonzero denominators, and retain the exact parity orientation. -/
private theorem sincShiftCoeffHD_center_covariance (k : Int) (t : Real)
    (ht : ∀ r : Int, t ≠ (r : Real)) (q : Int) :
    sincShiftCoeffHD k t (sincCenterIndex t + q) =
      intParityHD (sincCenterIndex t) *
        sincShiftCoeffHD k (sincCenteredPhase t) q := by
  let m : Int := sincCenterIndex t
  let s : Real := sincCenteredPhase t
  have ht_decomp : t = s + (m : Real) := by
    simp [m, s, sincCenteredPhase]
  have hsin : Real.sin (Real.pi * t) =
      ((-1 : Real) ^ m) * Real.sin (Real.pi * s) := by
    rw [ht_decomp]
    rw [show Real.pi * (s + (m : Real)) =
        Real.pi * s + (m : Real) * Real.pi by ring]
    exact Real.sin_add_int_mul_pi _ _
  change Theorem12.Generic.sincShiftCoeff k t (m + q) =
    ((-1 : Complex) ^ m) * Theorem12.Generic.sincShiftCoeff k s q
  unfold Theorem12.Generic.sincShiftCoeff
  rw [hsin, ht_decomp]
  push_cast
  ring

/- Reindex by the center, use parity norm one, and apply the
proved bounded-phase quadratic majorant.  The witness is uniform in every
noninteger phase. -/
theorem sincShiftCoeff_uniform_l1 (k : Int) :
    ∃ Ck : Real, 0 ≤ Ck ∧
      ∀ t : Real, (∀ r : Int, t ≠ (r : Real)) →
        Summable (fun q : Int ↦ ‖sincShiftCoeffHD k t q‖) ∧
          (∑' q : Int, ‖sincShiftCoeffHD k t q‖) ≤ Ck := by
  obtain ⟨C, hC, hbound⟩ := Theorem12.Generic.norm_sincShiftCoeff_le k
  let majorant : Int → Real := fun q ↦ C / (1 + (q : Real) ^ 2)
  have hmajorant : Summable majorant := by
    simpa only [majorant, div_eq_mul_inv] using
      Theorem12.Generic.summable_one_add_int_sq_inv.mul_left C
  let Ck : Real := ∑' q : Int, majorant q
  have hCk : 0 ≤ Ck := by
    apply tsum_nonneg
    intro q
    exact div_nonneg hC (by positivity)
  refine ⟨Ck, hCk, ?_⟩
  intro t ht
  let m : Int := sincCenterIndex t
  let s : Real := sincCenteredPhase t
  have hs_mem := sincCenteredPhase_mem t
  have hs : |s| < 3 / 2 := by
    rw [abs_lt]
    dsimp [s]
    constructor <;> linarith [hs_mem.1, hs_mem.2]
  have hsNonint : ∀ r : Int, s ≠ (r : Real) := by
    simpa only [s] using sincCenteredPhase_noninteger t ht
  have hcenter_bound (q : Int) :
      ‖sincShiftCoeffHD k s q‖ ≤ majorant q := by
    exact hbound s hs hsNonint q
  have hcenter : Summable (fun q : Int ↦ ‖sincShiftCoeffHD k s q‖) := by
    apply hmajorant.of_norm_bounded
    intro q
    simpa only [Real.norm_eq_abs, abs_norm] using hcenter_bound q
  have hnorm (q : Int) :
      ‖sincShiftCoeffHD k t (m + q)‖ =
        ‖sincShiftCoeffHD k s q‖ := by
    rw [show m = sincCenterIndex t by rfl,
      sincShiftCoeffHD_center_covariance k t ht q]
    simp [intParityHD, s]
  have htSummable : Summable (fun q : Int ↦ ‖sincShiftCoeffHD k t q‖) := by
    apply (Equiv.addLeft m).summable_iff.mp
    exact hcenter.congr fun q ↦ (hnorm q).symm
  refine ⟨htSummable, ?_⟩
  calc
    (∑' q : Int, ‖sincShiftCoeffHD k t q‖) =
        ∑' q : Int, ‖sincShiftCoeffHD k t (m + q)‖ :=
      (Equiv.tsum_eq (Equiv.addLeft m)
        (fun q : Int ↦ ‖sincShiftCoeffHD k t q‖)).symm
    _ = ∑' q : Int, ‖sincShiftCoeffHD k s q‖ := tsum_congr hnorm
    _ ≤ ∑' q : Int, majorant q :=
      hcenter.tsum_le_tsum hcenter_bound hmajorant
    _ = Ck := rfl

/- Package the exact proved bounded-phase pointwise
identity as a `HasSum`, normalizing only the native AddCircle character. -/
private theorem sinc_shift_identity_bounded_hasSumHD (k : Int) (s : Real)
    (hs : |s| < 3 / 2) (hsNonint : ∀ r : Int, s ≠ (r : Real))
    (y : AddCircle (1 : Real)) :
    HasSum
      (fun q : Int ↦ sincShiftCoeffHD k s q * fourier q y)
      (shiftedCenteredExpHD k s y) := by
  have hsum :=
    (Theorem12.Generic.continuous_sincShiftSeries k s hs hsNonint).1.hasSum
      (Set.mem_univ y)
  have hfourier (q : Int) :
      fourier q y = Complex.exp
        (((2 * Real.pi : Real) : Complex) * Complex.I * (q : Complex) *
          (Theorem12.Generic.unitRep y : Complex)) := by
    calc
      fourier q y = fourier q
          ((Theorem12.Generic.unitRep y : Real) : AddCircle (1 : Real)) := by
        rw [Theorem12.Generic.coe_unitRep]
      _ = _ := by
        rw [fourier_coe_apply]
        norm_num
  have hsum' : HasSum
      (fun q : Int ↦ Theorem12.Generic.sincShiftCoeff k s q * fourier q y)
      (Theorem12.Generic.sincShiftSeries k s y) := by
    simpa only [← hfourier] using hsum
  rw [Theorem12.Generic.sinc_shift_identity k s hs hsNonint y] at hsum'
  simpa only [sincShiftCoeffHD, shiftedCenteredExpHD] using hsum'

/- Expand the descended shifted exponential, substitute
`t = center + remainder`, and rewrite the integer factor as parity times the
native character. -/
private theorem shiftedCenteredExpHD_center_covariance (k : Int) (t : Real)
    (y : AddCircle (1 : Real)) :
    shiftedCenteredExpHD k t y =
      intParityHD (sincCenterIndex t) *
        fourier (sincCenterIndex t) y *
          shiftedCenteredExpHD k (sincCenteredPhase t) y := by
  let m : Int := sincCenterIndex t
  let s : Real := sincCenteredPhase t
  let u : Complex := (Theorem12.Generic.unitRep y : Complex)
  let v : Complex :=
    ((Theorem12.Generic.unitRep y - 1 / 2 : Real) : Complex)
  let A : Complex := ((2 * Real.pi : Real) : Complex) * Complex.I
  have ht_decomp : t = s + (m : Real) := by
    simp [m, s, sincCenteredPhase]
  have hfourier : Complex.exp (A * (m : Complex) * u) = fourier m y := by
    symm
    calc
      fourier m y = fourier m
          ((Theorem12.Generic.unitRep y : Real) : AddCircle (1 : Real)) := by
        rw [Theorem12.Generic.coe_unitRep]
      _ = Complex.exp (A * (m : Complex) * u) := by
        rw [fourier_coe_apply]
        norm_num [A, u]
  have hparity :
      Complex.exp ((m : Complex) * (-((Real.pi : Complex) * Complex.I))) =
        (-1 : Complex) ^ m := by
    rw [Complex.exp_int_mul, Complex.exp_neg_pi_mul_I]
  have hcenter :
      Complex.exp (A * (t : Complex) * v) =
        (-1 : Complex) ^ m * fourier m y *
          Complex.exp (A * (s : Complex) * v) := by
    rw [ht_decomp]
    push_cast
    rw [show A * ((s : Complex) + (m : Complex)) * v =
        (m : Complex) * (-((Real.pi : Complex) * Complex.I)) +
          A * (m : Complex) * u +
            A * (s : Complex) * v by
      dsimp [A, u, v]
      push_cast
      ring]
    rw [Complex.exp_add, Complex.exp_add, hparity, hfourier]
  simp only [shiftedCenteredExpHD, Theorem12.Generic.shiftedCenteredExp,
    Theorem12.Generic.centeredExp, intParityHD]
  change
    (Complex.exp (A * (k : Complex) * u) - 1) *
        Complex.exp (A * (t : Complex) * v) =
      (-1 : Complex) ^ m * fourier m y *
        ((Complex.exp (A * (k : Complex) * u) - 1) *
          Complex.exp (A * (s : Complex) * v))
  rw [hcenter]
  ring

/- Center the arbitrary phase, invoke the exact bounded
`HasSum`, multiply by parity and the center character, and transport through
the integer translation equivalence. -/
theorem sinc_shift_identity_arbitrary (k : Int) (t : Real)
    (ht : ∀ r : Int, t ≠ (r : Real)) (y : AddCircle (1 : Real)) :
    HasSum
      (fun q : Int ↦ sincShiftCoeffHD k t q * fourier q y)
      (shiftedCenteredExpHD k t y) := by
  let m : Int := sincCenterIndex t
  let s : Real := sincCenteredPhase t
  have hs_mem := sincCenteredPhase_mem t
  have hs : |s| < 3 / 2 := by
    rw [abs_lt]
    dsimp [s]
    constructor <;> linarith [hs_mem.1, hs_mem.2]
  have hsNonint : ∀ r : Int, s ≠ (r : Real) := by
    simpa only [s] using sincCenteredPhase_noninteger t ht
  have hsum := sinc_shift_identity_bounded_hasSumHD k s hs hsNonint y
  let P : Complex := intParityHD m * fourier m y
  have hmul : HasSum
      (fun q : Int ↦ P *
        (sincShiftCoeffHD k s q * fourier q y))
      (P * shiftedCenteredExpHD k s y) :=
    hsum.mul_left P
  have hterm (q : Int) :
      P * (sincShiftCoeffHD k s q * fourier q y) =
        sincShiftCoeffHD k t (m + q) * fourier (m + q) y := by
    rw [show m = sincCenterIndex t by rfl,
      sincShiftCoeffHD_center_covariance k t ht q, fourier_add]
    dsimp [P, s]
    ring
  have hvalue :
      P * shiftedCenteredExpHD k s y = shiftedCenteredExpHD k t y := by
    symm
    simpa only [P, m, s] using
      shiftedCenteredExpHD_center_covariance k t y
  have htranslated : HasSum
      (fun q : Int ↦ sincShiftCoeffHD k t (m + q) * fourier (m + q) y)
      (shiftedCenteredExpHD k t y) := by
    simpa only [hterm, hvalue] using hmul
  apply (Equiv.addLeft m).hasSum_iff.mp
  simpa [Function.comp_def, Equiv.addLeft, add_comm] using htranslated

end UniversalCompletenessHD.Internal
