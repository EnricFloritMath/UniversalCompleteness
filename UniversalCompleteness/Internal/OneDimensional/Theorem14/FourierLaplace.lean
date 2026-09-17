import Theorem14.Definitions
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! # Theorem 1.4: Fourier--Laplace analysis -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace Theorem14.Internal

private theorem fourier_eq_exp_unitRep (q : ℤ) (y : AddCircle (1 : ℝ)) :
    fourier q y = Complex.exp
      (((2 * Real.pi : ℝ) : ℂ) * Complex.I * (q : ℂ) *
        (Theorem12.Generic.unitRep y : ℂ)) := by
  calc
    fourier q y = fourier q
        ((Theorem12.Generic.unitRep y : ℝ) : AddCircle (1 : ℝ)) := by
      rw [Theorem12.Generic.coe_unitRep]
    _ = _ := by
      rw [fourier_coe_apply]
      norm_num

/- Proof idea: unfold both integrals and normalize the negative-sign exponent. -/
theorem fourierLaplace_intCast
    {g : AddCircle (1 : ℝ) → ℂ}
    (hg : Integrable g AddCircle.haarAddCircle) (n : ℤ) :
    fourierLaplace g (n : ℂ) = fourierCoeff g n := by
  /- Proof idea: Unfold both integrals and normalize casts/multiplication. -/
  rw [fourierLaplace, fourierCoeff]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    change g x * Complex.exp
      (-2 * Real.pi * Complex.I * (n : ℂ) *
        (Theorem12.Generic.unitRep x : ℂ)) =
      fourier (-n) x • g x
    rw [fourier_eq_exp_unitRep]
    simp only [smul_eq_mul]
    conv_rhs => rw [mul_comm]
    congr 2
    push_cast
    ring

/- Proof idea: use ball z 1 and the explicit bounded-unitRep integrable dominator. -/
private theorem measurable_unitRep :
    Measurable Theorem12.Generic.unitRep :=
  (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable.subtype_val

private lemma norm_fourierLaplacePhase_le
    (w : ℂ) (x : AddCircle (1 : ℝ)) :
    ‖Complex.exp (-2 * Real.pi * Complex.I * w *
      (Theorem12.Generic.unitRep x : ℂ))‖ ≤
      Real.exp (2 * Real.pi * ‖w‖) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  calc
    (-2 * Real.pi * Complex.I * w *
        (Theorem12.Generic.unitRep x : ℂ)).re ≤
        ‖-2 * Real.pi * Complex.I * w *
          (Theorem12.Generic.unitRep x : ℂ)‖ := Complex.re_le_norm _
    _ ≤ 2 * Real.pi * ‖w‖ := by
      rw [norm_mul, norm_mul, norm_mul]
      norm_num [norm_mul, abs_of_pos Real.pi_pos]
      have hu := Theorem12.Generic.unitRep_mem_Ico x
      rw [abs_of_nonneg hu.1]
      exact mul_le_of_le_one_right
        (mul_nonneg (mul_nonneg (by positivity) Real.pi_pos.le) (norm_nonneg w)) hu.2.le

private lemma hasDerivAt_fourierLaplaceIntegrand
    (g : AddCircle (1 : ℝ) → ℂ) (x : AddCircle (1 : ℝ)) (w : ℂ) :
    HasDerivAt
      (fun z : ℂ => g x * Complex.exp
        (-2 * Real.pi * Complex.I * z *
          (Theorem12.Generic.unitRep x : ℂ)))
      (fourierLaplaceDerivIntegrand g w x) w := by
  dsimp only [fourierLaplaceDerivIntegrand]
  let c : ℂ := -2 * Real.pi * Complex.I *
    (Theorem12.Generic.unitRep x : ℂ)
  have hexp : HasDerivAt (fun z : ℂ => Complex.exp (z * c))
      (c * Complex.exp (w * c)) w := by
    simpa only [Complex.exp_eq_exp_ℂ, smul_eq_mul] using
      hasDerivAt_exp_smul_const' c w
  have hout := HasDerivAt.const_mul (g x) hexp
  simpa only [c, mul_assoc, mul_comm, mul_left_comm] using hout

private lemma hasDerivAt_fourierLaplace
    {g : AddCircle (1 : ℝ) → ℂ}
    (hg : Integrable g AddCircle.haarAddCircle) (z : ℂ) :
    HasDerivAt (fourierLaplace g)
      (∫ x, fourierLaplaceDerivIntegrand g z x ∂AddCircle.haarAddCircle) z := by
  /- Proof idea: At `z0`, use the literal neighborhood `Metric.ball z0 1`. Since `0<=unitRep<1`, dominate
  derivative norms by `2*pi*exp(2*pi*(‖z0‖+1))*‖g x‖`, verify all
  measurability/differentiability hypotheses, apply the theorem, and project its
  `HasDerivAt` conjunct. -/
  let C : ℝ := 2 * Real.pi * Real.exp (2 * Real.pi * (‖z‖ + 1))
  let bound : AddCircle (1 : ℝ) → ℝ := fun x => C * ‖g x‖
  have hunitComplex : Measurable
      (fun x : AddCircle (1 : ℝ) =>
        (Theorem12.Generic.unitRep x : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp measurable_unitRep
  have hphaseMeas (w : ℂ) : StronglyMeasurable
      (fun x : AddCircle (1 : ℝ) =>
        Complex.exp (-2 * Real.pi * Complex.I * w *
          (Theorem12.Generic.unitRep x : ℂ))) :=
    (Complex.continuous_exp.measurable.comp
      (measurable_const.mul hunitComplex)).stronglyMeasurable
  have hFMeas : ∀ᶠ w in nhds z, AEStronglyMeasurable
      (fun x : AddCircle (1 : ℝ) =>
        g x * Complex.exp (-2 * Real.pi * Complex.I * w *
          (Theorem12.Generic.unitRep x : ℂ)))
        AddCircle.haarAddCircle := by
    exact Filter.Eventually.of_forall fun w =>
      hg.aestronglyMeasurable.mul (hphaseMeas w).aestronglyMeasurable
  have hFInt : Integrable
      (fun x : AddCircle (1 : ℝ) =>
        g x * Complex.exp (-2 * Real.pi * Complex.I * z *
          (Theorem12.Generic.unitRep x : ℂ)))
        AddCircle.haarAddCircle := by
    apply hg.mul_bdd (hphaseMeas z).aestronglyMeasurable
    exact ae_of_all _ fun x => norm_fourierLaplacePhase_le z x
  have hF'Meas : AEStronglyMeasurable
      (fourierLaplaceDerivIntegrand g z) AddCircle.haarAddCircle := by
    change AEStronglyMeasurable
      (fun x : AddCircle (1 : ℝ) =>
        g x * (-2 * Real.pi * Complex.I *
          (Theorem12.Generic.unitRep x : ℂ)) *
            Complex.exp (-2 * Real.pi * Complex.I * z *
              (Theorem12.Generic.unitRep x : ℂ)))
        AddCircle.haarAddCircle
    exact (hg.aestronglyMeasurable.mul
      ((measurable_const.mul hunitComplex).stronglyMeasurable.aestronglyMeasurable)).mul
        (hphaseMeas z).aestronglyMeasurable
  have hBound : ∀ᵐ x ∂AddCircle.haarAddCircle,
      ∀ w ∈ Metric.ball z 1,
        ‖fourierLaplaceDerivIntegrand g w x‖ ≤ bound x := by
    exact ae_of_all _ fun x w hw => by
      have hu := Theorem12.Generic.unitRep_mem_Ico x
      have hwsub : ‖w - z‖ < 1 := by
        simpa only [Metric.mem_ball, dist_eq_norm] using hw
      have hwNorm : ‖w‖ ≤ ‖z‖ + 1 := by
        calc
          ‖w‖ = ‖(w - z) + z‖ := by rw [sub_add_cancel]
          _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
          _ ≤ ‖z‖ + 1 := by linarith
      have hlinear :
          ‖-2 * Real.pi * Complex.I *
            (Theorem12.Generic.unitRep x : ℂ)‖ ≤ 2 * Real.pi := by
        rw [norm_mul, norm_mul, norm_mul]
        norm_num [norm_mul, abs_of_pos Real.pi_pos]
        rw [abs_of_nonneg hu.1]
        exact mul_le_of_le_one_right
          (mul_nonneg (by positivity) Real.pi_pos.le) hu.2.le
      have hexp :
          ‖Complex.exp (-2 * Real.pi * Complex.I * w *
            (Theorem12.Generic.unitRep x : ℂ))‖ ≤
              Real.exp (2 * Real.pi * (‖z‖ + 1)) :=
        (norm_fourierLaplacePhase_le w x).trans
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hwNorm
            (mul_nonneg (by positivity) Real.pi_pos.le)))
      dsimp only [fourierLaplaceDerivIntegrand, bound, C]
      rw [norm_mul, norm_mul]
      calc
        ‖g x‖ *
              ‖-2 * Real.pi * Complex.I *
                (Theorem12.Generic.unitRep x : ℂ)‖ *
            ‖Complex.exp (-2 * Real.pi * Complex.I * w *
              (Theorem12.Generic.unitRep x : ℂ))‖ ≤
            ‖g x‖ * (2 * Real.pi) *
              Real.exp (2 * Real.pi * (‖z‖ + 1)) := by gcongr
        _ = 2 * Real.pi * Real.exp (2 * Real.pi * (‖z‖ + 1)) * ‖g x‖ := by
          ring
  have hBoundInt : Integrable bound AddCircle.haarAddCircle := by
    dsimp only [bound]
    exact hg.norm.const_mul C
  have hDiff : ∀ᵐ x ∂AddCircle.haarAddCircle,
      ∀ w ∈ Metric.ball z 1,
        HasDerivAt
          (fun z : ℂ => g x * Complex.exp
            (-2 * Real.pi * Complex.I * z *
              (Theorem12.Generic.unitRep x : ℂ)))
          (fourierLaplaceDerivIntegrand g w x) w :=
    ae_of_all _ fun x w _ => hasDerivAt_fourierLaplaceIntegrand g x w
  have main := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun w x => g x * Complex.exp
      (-2 * Real.pi * Complex.I * w *
        (Theorem12.Generic.unitRep x : ℂ)))
    (F' := fourierLaplaceDerivIntegrand g)
    (bound := bound) (Metric.ball_mem_nhds z one_pos)
    hFMeas hFInt hF'Meas hBound hBoundInt hDiff
  simpa only [fourierLaplace] using! main.2

/- Proof idea: assemble differentiability pointwise and apply the equivalence. -/
theorem analyticOnNhd_fourierLaplace
    {g : AddCircle (1 : ℝ) → ℂ}
    (hg : Integrable g AddCircle.haarAddCircle) :
    AnalyticOnNhd ℂ (fourierLaplace g) Set.univ := by
  /- Proof idea: `measurable_unitRep` supplies differentiability at every point; assemble `Differentiable Complex
  (fourierLaplace g)` and apply the fully qualified entire/differentiable equivalence. -/
  rw [Complex.analyticOnNhd_univ_iff_differentiable]
  intro z
  exact (hasDerivAt_fourierLaplace hg z).differentiableAt

/- Proof idea: use 0≤unitRep≤L wherever g is nonzero and maximize by max z.im 0. -/
private lemma norm_fourierLaplace_le
    {g : AddCircle (1 : ℝ) → ℂ} {L : ℝ}
    (hg : Integrable g AddCircle.haarAddCircle)
    (hL0 : 0 ≤ L) (hsupp : SupportedInInitialArc g L) (z : ℂ) :
    ‖fourierLaplace g z‖ ≤
      (∫ x, ‖g x‖ ∂AddCircle.haarAddCircle) *
        Real.exp (2 * Real.pi * L * max z.im 0) := by
  /- Proof idea: Bound the integral norm pointwise; if `g x!=0`, support and representative range give
  `0<=unitRep x<=L`; maximize the exponential factor according to the sign of `z.im`. -/
  have hunitComplex : Measurable
      (fun x : AddCircle (1 : ℝ) =>
        (Theorem12.Generic.unitRep x : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp measurable_unitRep
  have hphaseMeas : StronglyMeasurable
      (fun x : AddCircle (1 : ℝ) =>
        Complex.exp (-2 * Real.pi * Complex.I * z *
          (Theorem12.Generic.unitRep x : ℂ))) :=
    (Complex.continuous_exp.measurable.comp
      (measurable_const.mul hunitComplex)).stronglyMeasurable
  have hintegrand : Integrable
      (fun x : AddCircle (1 : ℝ) =>
        g x * Complex.exp (-2 * Real.pi * Complex.I * z *
          (Theorem12.Generic.unitRep x : ℂ)))
        AddCircle.haarAddCircle := by
    apply hg.mul_bdd hphaseMeas.aestronglyMeasurable
    exact ae_of_all _ fun x => norm_fourierLaplacePhase_le z x
  have hmajorant : Integrable
      (fun x : AddCircle (1 : ℝ) =>
        ‖g x‖ * Real.exp (2 * Real.pi * L * max z.im 0))
        AddCircle.haarAddCircle :=
    hg.norm.mul_const _
  have hpoint (x : AddCircle (1 : ℝ)) :
      ‖g x * Complex.exp (-2 * Real.pi * Complex.I * z *
        (Theorem12.Generic.unitRep x : ℂ))‖ ≤
        ‖g x‖ * Real.exp (2 * Real.pi * L * max z.im 0) := by
    by_cases hgx : g x = 0
    · simp [hgx]
    · have hu := Theorem12.Generic.unitRep_mem_Ico x
      have huL : Theorem12.Generic.unitRep x ≤ L := by
        by_contra hnot
        apply hgx
        apply hsupp x
        intro hmem
        exact hnot hmem.2
      have him :
          z.im * Theorem12.Generic.unitRep x ≤ L * max z.im 0 := by
        by_cases hz : 0 ≤ z.im
        · rw [max_eq_left hz]
          nlinarith [mul_le_mul_of_nonneg_left huL hz]
        · rw [max_eq_right (le_of_not_ge hz), mul_zero]
          exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hz) hu.1
      rw [norm_mul, Complex.norm_exp]
      gcongr
      have hre :
          (-2 * Real.pi * Complex.I * z *
            (Theorem12.Generic.unitRep x : ℂ)).re =
              2 * Real.pi *
                (z.im * Theorem12.Generic.unitRep x) := by
        simp [Complex.mul_re]
        ring
      rw [hre]
      calc
        2 * Real.pi * (z.im * Theorem12.Generic.unitRep x) ≤
            2 * Real.pi * (L * max z.im 0) :=
          mul_le_mul_of_nonneg_left him
            (mul_nonneg (by norm_num) Real.pi_pos.le)
        _ = 2 * Real.pi * L * max z.im 0 := by ring
  rw [fourierLaplace]
  calc
    ‖∫ x, g x * Complex.exp (-2 * Real.pi * Complex.I * z *
        (Theorem12.Generic.unitRep x : ℂ))
          ∂AddCircle.haarAddCircle‖ ≤
        ∫ x, ‖g x * Complex.exp (-2 * Real.pi * Complex.I * z *
          (Theorem12.Generic.unitRep x : ℂ))‖
            ∂AddCircle.haarAddCircle := norm_integral_le_integral_norm _
    _ ≤ ∫ x, ‖g x‖ * Real.exp
        (2 * Real.pi * L * max z.im 0)
          ∂AddCircle.haarAddCircle :=
      integral_mono hintegrand.norm hmajorant hpoint
    _ = (∫ x, ‖g x‖ ∂AddCircle.haarAddCircle) *
        Real.exp (2 * Real.pi * L * max z.im 0) :=
      integral_mul_const _ _

/- Proof idea: split at pi and integrate sine exactly. -/
private lemma integral_max_sin_zero
    {R : ℝ} (hR : 0 ≤ R) :
    (2 * Real.pi)⁻¹ *
        (∫ theta in Set.Ioc (0 : ℝ) (2 * Real.pi),
          max (R * Real.sin theta) 0) = R / Real.pi ∧
      (∫ theta in Set.Ioc (0 : ℝ) (2 * Real.pi),
        max (R * Real.sin theta) 0) = 2 * R := by
  /- Proof idea: Split at `pi`, simplify the max on each interval, and integrate sine exactly. -/
  let φ : ℝ → ℝ := fun theta => max (R * Real.sin theta) 0
  have hφcont : Continuous φ :=
    (continuous_const.mul Real.continuous_sin).max continuous_const
  have hfirst : (∫ theta in (0 : ℝ)..Real.pi, φ theta) = 2 * R := by
    calc
      (∫ theta in (0 : ℝ)..Real.pi, φ theta) =
          ∫ theta in (0 : ℝ)..Real.pi, R * Real.sin theta := by
        apply intervalIntegral.integral_congr
        intro theta htheta
        rw [uIcc_of_le Real.pi_pos.le] at htheta
        dsimp only [φ]
        rw [max_eq_left]
        exact mul_nonneg hR
          (Real.sin_nonneg_of_nonneg_of_le_pi htheta.1 htheta.2)
      _ = R * ∫ theta in (0 : ℝ)..Real.pi, Real.sin theta :=
        intervalIntegral.integral_const_mul R Real.sin
      _ = 2 * R := by
        have hsin :
            (∫ theta in (0 : ℝ)..Real.pi, Real.sin theta) = 2 := by
          rw [intervalIntegral.integral_deriv_eq_sub'
            (fun x : ℝ => -Real.cos x)]
          · simp
            norm_num
          · funext x
            simp
          · intro x _
            fun_prop
          · exact Real.continuous_sin.continuousOn
        rw [hsin]
        ring
  have hsecond :
      (∫ theta in Real.pi..2 * Real.pi, φ theta) = 0 := by
    calc
      (∫ theta in Real.pi..2 * Real.pi, φ theta) =
          ∫ _theta in Real.pi..2 * Real.pi, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro theta htheta
        have hpi2 : Real.pi ≤ 2 * Real.pi := by linarith [Real.pi_pos]
        rw [uIcc_of_le hpi2] at htheta
        dsimp only [φ]
        rw [max_eq_right]
        apply mul_nonpos_of_nonneg_of_nonpos hR
        have hsin := Real.sin_nonneg_of_nonneg_of_le_pi
          (show 0 ≤ 2 * Real.pi - theta by linarith [htheta.2])
          (show 2 * Real.pi - theta ≤ Real.pi by linarith [htheta.1])
        rw [Real.sin_two_pi_sub] at hsin
        linarith
      _ = 0 := by simp
  have htotal : (∫ theta in (0 : ℝ)..2 * Real.pi, φ theta) = 2 * R := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hφcont.intervalIntegrable 0 Real.pi)
      (hφcont.intervalIntegrable Real.pi (2 * Real.pi)), hfirst, hsecond, add_zero]
  have hset :
      (∫ theta in Set.Ioc (0 : ℝ) (2 * Real.pi),
        max (R * Real.sin theta) 0) = 2 * R := by
    change (∫ theta in Set.Ioc (0 : ℝ) (2 * Real.pi), φ theta) = 2 * R
    rw [← intervalIntegral.integral_of_le Real.two_pi_pos.le]
    exact htotal
  constructor
  · rw [hset]
    field_simp [Real.pi_ne_zero]
  · exact hset

/- Proof idea: take logs of the sharp one-sided estimate only on a nonvanishing boundary. -/
theorem circleLogMean_shiftedFourierLaplace_le_of_clean
    {g : AddCircle (1 : ℝ) → ℂ} {L R : ℝ} {m : ℤ}
    (hg : Integrable g AddCircle.haarAddCircle)
    (hsupp : SupportedInInitialArc g L) (hL0 : 0 ≤ L) (hR0 : 0 < R)
    (hclean : ∀ z : ℂ, ‖z‖ = R → shiftedFourierLaplace g m z ≠ 0) :
    Theorem12.Generic.circleLogMean (shiftedFourierLaplace g m) R ≤
      2 * L * R +
        Real.log (max 1 (∫ x, ‖g x‖ ∂AddCircle.haarAddCircle)) := by
  /- Proof idea: Use `norm_fourierLaplace_le` for the shifted transform and exact imaginary-part invariance; take logs
  pointwise on the clean circle; integrate and apply `integral_max_sin_zero`. The integer shift contributes
  no error. -/
  let A : ℝ := ∫ x, ‖g x‖ ∂AddCircle.haarAddCircle
  let K : ℝ := max 1 A
  let circle : ℝ → ℂ := fun theta =>
    (R : ℂ) * Complex.exp (Complex.I * (theta : ℂ))
  let p : ℝ → ℝ := fun theta => max (R * Real.sin theta) 0
  let lhs : ℝ → ℝ := fun theta =>
    Real.log ‖shiftedFourierLaplace g m (circle theta)‖
  let rhs : ℝ → ℝ := fun theta =>
    2 * Real.pi * L * p theta + Real.log K
  have hcircleNorm (theta : ℝ) : ‖circle theta‖ = R := by
    dsimp only [circle]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR0,
      Complex.norm_exp]
    simp [Complex.mul_re]
  have hcircleIm (theta : ℝ) :
      (circle theta + (m : ℂ)).im = R * Real.sin theta := by
    dsimp only [circle]
    rw [mul_comm Complex.I (theta : ℂ), Complex.exp_mul_I]
    simp [Complex.mul_im, Complex.sin_ofReal_re]
  have hKpos : 0 < K := by
    exact lt_of_lt_of_le zero_lt_one (le_max_left 1 A)
  have hpoint (theta : ℝ) : lhs theta ≤ rhs theta := by
    have hnonzero : shiftedFourierLaplace g m (circle theta) ≠ 0 :=
      hclean (circle theta) (hcircleNorm theta)
    have hnormpos : 0 < ‖shiftedFourierLaplace g m (circle theta)‖ :=
      norm_pos_iff.mpr hnonzero
    have hraw := norm_fourierLaplace_le hg hL0 hsupp
      (circle theta + (m : ℂ))
    have htype :
        ‖shiftedFourierLaplace g m (circle theta)‖ ≤
          A * Real.exp (2 * Real.pi * L * p theta) := by
      simpa only [shiftedFourierLaplace, A, p, hcircleIm] using hraw
    have hAK : A ≤ K := le_max_right 1 A
    have hupper :
        ‖shiftedFourierLaplace g m (circle theta)‖ ≤
          K * Real.exp (2 * Real.pi * L * p theta) :=
      htype.trans (mul_le_mul_of_nonneg_right hAK (Real.exp_pos _).le)
    dsimp only [lhs, rhs]
    calc
      Real.log ‖shiftedFourierLaplace g m (circle theta)‖ ≤
          Real.log (K * Real.exp (2 * Real.pi * L * p theta)) :=
        Real.log_le_log hnormpos hupper
      _ = 2 * Real.pi * L * p theta + Real.log K := by
        rw [Real.log_mul hKpos.ne' (Real.exp_pos _).ne', Real.log_exp]
        ring
  have hcircleCont : Continuous circle := by
    dsimp only [circle]
    fun_prop
  have hshiftCont : Continuous (shiftedFourierLaplace g m) := by
    have hFL := (analyticOnNhd_fourierLaplace hg).continuous
    change Continuous (fun z : ℂ => fourierLaplace g (z + (m : ℂ)))
    exact hFL.comp (continuous_id.add continuous_const)
  have hlhsCont : ContinuousOn lhs (Set.Icc (0 : ℝ) (2 * Real.pi)) := by
    dsimp only [lhs]
    apply ContinuousOn.log
    · exact (hshiftCont.comp hcircleCont).norm.continuousOn
    · intro theta _
      exact norm_ne_zero_iff.mpr
        (hclean (circle theta) (hcircleNorm theta))
  have hpCont : Continuous p := by
    dsimp only [p]
    exact (continuous_const.mul Real.continuous_sin).max continuous_const
  have hrhsCont : Continuous rhs := by
    dsimp only [rhs]
    fun_prop
  have hlhsInt : IntervalIntegrable lhs volume (0 : ℝ) (2 * Real.pi) :=
    by
      apply ContinuousOn.intervalIntegrable
      simpa [uIcc_of_le Real.two_pi_pos.le] using hlhsCont
  have hrhsInt : IntervalIntegrable rhs volume (0 : ℝ) (2 * Real.pi) :=
    hrhsCont.intervalIntegrable _ _
  have hint :
      (∫ theta in (0 : ℝ)..2 * Real.pi, lhs theta) ≤
        ∫ theta in (0 : ℝ)..2 * Real.pi, rhs theta :=
    intervalIntegral.integral_mono_on Real.two_pi_pos.le hlhsInt hrhsInt
      (fun theta _ => hpoint theta)
  have hpInterval :
      (∫ theta in (0 : ℝ)..2 * Real.pi, p theta) = 2 * R := by
    rw [intervalIntegral.integral_of_le Real.two_pi_pos.le]
    exact (integral_max_sin_zero hR0.le).2
  have htermInt : IntervalIntegrable
      (fun theta => 2 * Real.pi * L * p theta) volume
      (0 : ℝ) (2 * Real.pi) :=
    (continuous_const.mul hpCont).intervalIntegrable _ _
  have hconstInt : IntervalIntegrable
      (fun _theta : ℝ => Real.log K) volume
      (0 : ℝ) (2 * Real.pi) :=
    continuous_const.intervalIntegrable _ _
  have hrhsIntegral :
      (2 * Real.pi)⁻¹ *
          (∫ theta in (0 : ℝ)..2 * Real.pi, rhs theta) =
        2 * L * R + Real.log K := by
    dsimp only [rhs]
    rw [intervalIntegral.integral_add htermInt hconstInt,
      intervalIntegral.integral_const_mul, hpInterval,
      intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
    field_simp [Real.pi_ne_zero]
  rw [Theorem12.Generic.circleLogMean,
    ← intervalIntegral.integral_of_le Real.two_pi_pos.le]
  calc
    (2 * Real.pi)⁻¹ *
        (∫ theta in (0 : ℝ)..2 * Real.pi, lhs theta) ≤
      (2 * Real.pi)⁻¹ *
        (∫ theta in (0 : ℝ)..2 * Real.pi, rhs theta) :=
      mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr
        (mul_nonneg (by norm_num) Real.pi_pos.le))
    _ = 2 * L * R + Real.log K := hrhsIntegral

end Theorem14.Internal
