import Theorem12.Summability
import Theorem12.MeromorphicSeries
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace Theorem12.Internal

/- Proof idea: use the source logarithm away from sine zeros and assign the irrelevant value zero
at the singular angles to obtain a total real function. -/
def logSineMajorant (t : ℝ) : ℝ :=
  if Real.sin t = 0 then 0 else Real.log (1 + |Real.sin t|⁻¹)

/- Proof idea: split away from the three sine zeros and compare locally with the integrable
logarithmic endpoint singularity. -/
theorem integrableOn_logSineMajorant : IntegrableOn logSineMajorant (Set.Ioc (0 : ℝ) (2 * Real.pi)) := by
  have hupper : IntervalIntegrable
      (fun t : ℝ => Real.log (1 + |Real.sin t|)) volume 0 (2 * Real.pi) :=
    ((continuous_const.add Real.continuous_sin.abs).log
      (fun t => by
        change 1 + |Real.sin t| ≠ 0
        nlinarith [abs_nonneg (Real.sin t)])).intervalIntegrable _ _
  have hlower : IntervalIntegrable
      (fun t : ℝ => Real.log ‖Real.sin t‖) volume 0 (2 * Real.pi) :=
    Real.analyticOnNhd_sin.meromorphicOn.intervalIntegrable_log_norm
  have hdiff := hupper.sub hlower
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)] at hdiff
  refine hdiff.congr_fun ?_ measurableSet_Ioc
  intro t ht
  by_cases hs : Real.sin t = 0
  · simp [logSineMajorant, hs]
  · have habs : |Real.sin t| ≠ 0 := abs_ne_zero.mpr hs
    have hfrac : 1 + |Real.sin t|⁻¹ = (1 + |Real.sin t|) / |Real.sin t| := by
      field_simp
      ring
    rw [logSineMajorant, if_neg hs, hfrac,
      Real.log_div (by positivity) habs]
    simp only [Real.norm_eq_abs]

/- Proof idea: take the positive minimum of the finite poles in `[-1,1]`, using one outside that
interval when the finite set is empty; off-badness excludes zero. -/
theorem exists_pos_le_abs_realPole {alpha : ℝ} {beta : ℚ} {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f) (x : AddCircle (1 : ℝ)) (hx : AnalyticParameter data x) (hactive : Nonempty (ActiveIndex data x)) : ∃ rho : ℝ, 0 < rho ∧ ∀ p : ℝ, p ∈ realPoleSet data x → rho ≤ |p| := by
  classical
  have hpole_ne_zero {p : ℝ} (hp : p ∈ realPoleSet data x) : p ≠ 0 := by
    rcases hp with ⟨a, rfl⟩
    change poleCoord alpha beta x a.1.1 a.1.2 ≠ 0
    simpa only [Int.cast_zero] using
      poleCoord_not_int_of_not_sineBad alpha beta x hx.1 a.1.1 a.1.2 0
  let P : Finset ℝ :=
    (finite_realPoleSet_inter_Icc data x hx 1 zero_le_one).toFinset
  let A : Finset ℝ := insert 1 (P.image abs)
  have hA : A.Nonempty := by simp [A]
  let rho : ℝ := A.min' hA
  have hrho_mem : rho ∈ A := by
    exact A.min'_mem hA
  have hrho_pos : 0 < rho := by
    rcases Finset.mem_insert.mp hrho_mem with hrho | hrho
    · simpa only [← hrho] using (zero_lt_one : (0 : ℝ) < 1)
    · rcases Finset.mem_image.mp hrho with ⟨p, hpP, hpabs⟩
      have hpIcc : p ∈ realPoleSet data x ∩ Set.Icc (-1 : ℝ) 1 := by
        exact (finite_realPoleSet_inter_Icc data x hx 1 zero_le_one).mem_toFinset.mp hpP
      rw [← hpabs]
      exact abs_pos.mpr (hpole_ne_zero hpIcc.1)
  refine ⟨rho, hrho_pos, ?_⟩
  intro p hp
  by_cases hp1 : |p| ≤ 1
  · apply A.min'_le |p|
    refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨p, ?_, rfl⟩)
    apply (finite_realPoleSet_inter_Icc data x hx 1 zero_le_one).mem_toFinset.mpr
    exact ⟨hp, abs_le.mp hp1⟩
  · exact (A.min'_le 1 (by simp [A])).trans (le_of_not_ge hp1)

/- Proof idea: split active poles at `|p| ≤ 2R`; use `|Re^{it}-p| ≥ R|sin t|` for near poles,
quadratic tail decay for far poles, and the fixed weighted residue summability. -/
theorem norm_activeM_circle_le_ae {alpha : ℝ} {beta : ℚ} {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f) (x : AddCircle (1 : ℝ)) (hx : AnalyticParameter data x) (hactive : Nonempty (ActiveIndex data x)) : ∃ Cx : ℝ, 0 < Cx ∧ ∀ R : ℝ, 1 ≤ R → ∀ᵐ t : ℝ ∂volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi)), ‖activeM data x ((R : ℂ) * Complex.exp (Complex.I * (t : ℂ)))‖ ≤ Cx * R * (1 + |Real.sin t|⁻¹) := by
  classical
  rcases exists_pos_le_abs_realPole data x hx hactive with ⟨rho, hrho, hpole⟩
  let w : ActiveIndex data x → ℝ := fun a =>
    ‖residueCoord data alpha beta x a.1.1 a.1.2‖ /
      (1 + (poleCoord alpha beta x a.1.1 a.1.2) ^ 2)
  have hw : Summable w := by
    have hfull := (summable_residue_and_indicator_weight data x hx.2).1
    simpa only [w, Function.comp_def, ActiveIndex] using
      hfull.subtype (fun a : ℤ × ℤ => residueCoord data alpha beta x a.1 a.2 ≠ 0)
  let W : ℝ := ∑' a : ActiveIndex data x, w a
  let Cx : ℝ := max 1 ((rho⁻¹ + 4) * W)
  have hCx : 0 < Cx := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨Cx, hCx, ?_⟩
  intro R hR
  have hzero_countable : Set.Countable {t : ℝ | Real.sin t = 0} := by
    refine (Set.countable_range (fun n : ℤ => (n : ℝ) * Real.pi)).mono ?_
    intro t ht
    rcases Real.sin_eq_zero_iff.mp ht with ⟨n, hn⟩
    exact ⟨n, hn⟩
  have hsin_ae_volume : ∀ᵐ t : ℝ ∂volume, Real.sin t ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not] using hzero_countable.measure_zero volume
  have hsin_ae : ∀ᵐ t : ℝ ∂volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi)),
      Real.sin t ≠ 0 :=
    Filter.Eventually.filter_mono ae_restrict_le hsin_ae_volume
  filter_upwards [hsin_ae] with t hsin
  let p : ActiveIndex data x → ℝ := fun a => poleCoord alpha beta x a.1.1 a.1.2
  let z : ℂ := (R : ℂ) * Complex.exp (Complex.I * (t : ℂ))
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hspos : 0 < |Real.sin t| := abs_pos.mpr hsin
  have hznorm : ‖z‖ = R := by
    simp [z, Complex.norm_exp_I_mul_ofReal, abs_of_pos hRpos]
  have hzim : z.im = R * Real.sin t := by
    simp [z, Complex.mul_im, Complex.exp_im]
  have hterm (a : ActiveIndex data x) :
      ‖activeTerm data x a z‖ ≤
        (rho⁻¹ + 4) * R * (1 + |Real.sin t|⁻¹) * w a := by
    have hp_mem : p a ∈ realPoleSet data x := ⟨a, rfl⟩
    have hpabs : rho ≤ |p a| := hpole (p a) hp_mem
    have hpabspos : 0 < |p a| := hrho.trans_le hpabs
    have hp0 : p a ≠ 0 := abs_pos.mp hpabspos
    have hdist_sin : R * |Real.sin t| ≤ ‖z - (p a : ℂ)‖ := by
      have him := Complex.abs_im_le_norm (z - (p a : ℂ))
      rw [Complex.sub_im, Complex.ofReal_im, sub_zero, hzim, abs_mul,
        abs_of_pos hRpos] at him
      exact him
    have hdistpos : 0 < ‖z - (p a : ℂ)‖ :=
      (mul_pos hRpos hspos).trans_le hdist_sin
    have hnorm :
        ‖activeTerm data x a z‖ =
          ‖residueCoord data alpha beta x a.1.1 a.1.2‖ * R /
            (|p a| * ‖z - (p a : ℂ)‖) := by
      simp only [activeTerm, regularizedKernel, norm_mul, norm_div,
        Complex.norm_real, Real.norm_eq_abs]
      rw [hznorm]
      simp only [p]
      ring
    have hw_nonneg : 0 ≤ w a := by simp only [w]; positivity
    have hconst_nonneg : 0 ≤ rho⁻¹ + 4 := by positivity
    by_cases hnear : |p a| ≤ 2 * R
    · have hdist_inv : ‖z - (p a : ℂ)‖⁻¹ ≤ (R * |Real.sin t|)⁻¹ :=
        (inv_le_inv₀ hdistpos (mul_pos hRpos hspos)).2 hdist_sin
      have hp_inv : |p a|⁻¹ ≤ rho⁻¹ :=
        (inv_le_inv₀ hpabspos hrho).2 hpabs
      have hratio : (1 + (p a) ^ 2) / |p a| ≤ (rho⁻¹ + 2) * R := by
        have heq : (1 + (p a) ^ 2) / |p a| = |p a|⁻¹ + |p a| := by
          rw [div_eq_iff hpabspos.ne']
          field_simp
          nlinarith [sq_abs (p a)]
        rw [heq]
        calc
          |p a|⁻¹ + |p a| ≤ rho⁻¹ + 2 * R := add_le_add hp_inv hnear
          _ ≤ (rho⁻¹ + 2) * R := by
            have : 0 ≤ rho⁻¹ := (inv_pos.mpr hrho).le
            nlinarith
      have hres : ‖residueCoord data alpha beta x a.1.1 a.1.2‖ =
          w a * (1 + (p a) ^ 2) := by
        simp only [w, p]
        field_simp
      rw [hnorm, hres]
      calc
        w a * (1 + (p a) ^ 2) * R / (|p a| * ‖z - (p a : ℂ)‖) =
            w a * ((1 + (p a) ^ 2) / |p a|) * R * ‖z - (p a : ℂ)‖⁻¹ := by
              field_simp
        _ ≤ w a * ((rho⁻¹ + 2) * R) * R * (R * |Real.sin t|)⁻¹ := by
              gcongr
        _ = w a * (rho⁻¹ + 2) * R * |Real.sin t|⁻¹ := by
              field_simp
        _ ≤ w a * (rho⁻¹ + 4) * R * |Real.sin t|⁻¹ := by
              (gcongr; linarith)
        _ ≤ w a * (rho⁻¹ + 4) * R * (1 + |Real.sin t|⁻¹) := by
              exact mul_le_mul_of_nonneg_left (by linarith : |Real.sin t|⁻¹ ≤
                1 + |Real.sin t|⁻¹) (by positivity)
        _ = (rho⁻¹ + 4) * R * (1 + |Real.sin t|⁻¹) * w a := by ring
    · have hfar : 2 * R < |p a| := lt_of_not_ge hnear
      have hR_le_p : R ≤ |p a| := by nlinarith
      have hdist : |p a| - R ≤ ‖z - (p a : ℂ)‖ := by
        have hrev := abs_norm_sub_norm_le z (p a : ℂ)
        rw [hznorm, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonpos (sub_nonpos.mpr hR_le_p)] at hrev
        simpa using hrev
      have hhalf : |p a| / 2 ≤ ‖z - (p a : ℂ)‖ := by nlinarith
      have hhalfpos : 0 < |p a| / 2 := by positivity
      have hdist_inv : ‖z - (p a : ℂ)‖⁻¹ ≤ 2 * |p a|⁻¹ := by
        calc
          ‖z - (p a : ℂ)‖⁻¹ ≤ (|p a| / 2)⁻¹ :=
            (inv_le_inv₀ hdistpos hhalfpos).2 hhalf
          _ = 2 * |p a|⁻¹ := by field_simp
      have hratio : (1 + (p a) ^ 2) / |p a| ^ 2 ≤ 2 := by
        rw [div_le_iff₀ (sq_pos_of_pos hpabspos)]
        nlinarith [sq_abs (p a)]
      have hres : ‖residueCoord data alpha beta x a.1.1 a.1.2‖ =
          w a * (1 + (p a) ^ 2) := by
        simp only [w, p]
        field_simp
      rw [hnorm, hres]
      calc
        w a * (1 + (p a) ^ 2) * R / (|p a| * ‖z - (p a : ℂ)‖) =
            w a * (1 + (p a) ^ 2) * R * |p a|⁻¹ * ‖z - (p a : ℂ)‖⁻¹ := by
              field_simp
        _ ≤ w a * (1 + (p a) ^ 2) * R * |p a|⁻¹ * (2 * |p a|⁻¹) := by
              gcongr
        _ = 2 * w a * ((1 + (p a) ^ 2) / |p a| ^ 2) * R := by
              field_simp
        _ = (2 * w a * R) * ((1 + (p a) ^ 2) / |p a| ^ 2) := by ring
        _ ≤ (2 * w a * R) * 2 :=
          mul_le_mul_of_nonneg_left hratio (by positivity)
        _ = 4 * w a * R := by ring
        _ ≤ (rho⁻¹ + 4) * R * w a := by
              rw [mul_assoc (rho⁻¹ + 4), mul_comm R (w a),
                ← mul_assoc (rho⁻¹ + 4), mul_assoc 4]
              have hrhoinv : 0 ≤ rho⁻¹ := inv_nonneg.mpr hrho.le
              have hc : (4 : ℝ) ≤ rho⁻¹ + 4 := by linarith
              simpa only [mul_assoc] using
                mul_le_mul_of_nonneg_right hc (mul_nonneg hw_nonneg hRpos.le)
        _ ≤ (rho⁻¹ + 4) * R * (1 + |Real.sin t|⁻¹) * w a := by
              apply mul_le_mul_of_nonneg_right _ hw_nonneg
              have hsle : (1 : ℝ) ≤ 1 + |Real.sin t|⁻¹ := by
                linarith [inv_nonneg.mpr hspos.le]
              simpa using mul_le_mul_of_nonneg_left hsle
                (mul_nonneg hconst_nonneg hRpos.le)
  have hmajor : Summable (fun a : ActiveIndex data x =>
      (rho⁻¹ + 4) * R * (1 + |Real.sin t|⁻¹) * w a) :=
    hw.mul_left ((rho⁻¹ + 4) * R * (1 + |Real.sin t|⁻¹))
  have hnormSummable : Summable (fun a : ActiveIndex data x => ‖activeTerm data x a z‖) :=
    Summable.of_nonneg_of_le (fun a => norm_nonneg _) hterm hmajor
  change ‖activeM data x z‖ ≤ Cx * R * (1 + |Real.sin t|⁻¹)
  calc
    ‖activeM data x z‖ ≤ ∑' a : ActiveIndex data x, ‖activeTerm data x a z‖ := by
      exact norm_tsum_le_tsum_norm hnormSummable
    _ ≤ ∑' a : ActiveIndex data x,
        (rho⁻¹ + 4) * R * (1 + |Real.sin t|⁻¹) * w a :=
      Summable.tsum_le_tsum hterm hnormSummable hmajor
    _ = (rho⁻¹ + 4) * R * (1 + |Real.sin t|⁻¹) * W := by
      rw [tsum_mul_left]
    _ = ((rho⁻¹ + 4) * W) * R * (1 + |Real.sin t|⁻¹) := by ring
    _ ≤ Cx * R * (1 + |Real.sin t|⁻¹) := by
      gcongr
      exact le_max_right 1 ((rho⁻¹ + 4) * W)

/- Proof idea: integrate the nonnegative positive part of the logarithmic norm around the radius-`R`
circle and multiply by the exact normalization `(2*pi)⁻¹`. -/
def circlePosLogMean (F : ℂ → ℂ) (R : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ *
    ∫ t in Set.Ioc (0 : ℝ) (2 * Real.pi),
      max (Real.log ‖F ((R : ℂ) * Complex.exp (Complex.I * (t : ℂ)))‖) 0

/- Proof idea: take positive logarithms of the AE `norm_activeM_circle_le_ae` estimate, integrate the
radius-dependent AE inequality, and absorb the finite sine majorant integral into `A` and `B`. -/
theorem circlePosLogMean_le_log {alpha : ℝ} {beta : ℚ} {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f) (x : AddCircle (1 : ℝ)) (hx : AnalyticParameter data x) (hactive : Nonempty (ActiveIndex data x)) : ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ R : ℝ, 1 ≤ R → circlePosLogMean (activeM data x) R ≤ A + B * Real.log R := by
  rcases norm_activeM_circle_le_ae data x hx hactive with ⟨Cx, hCx, hbound⟩
  let J : ℝ := ∫ t in Set.Ioc (0 : ℝ) (2 * Real.pi), logSineMajorant t
  let A : ℝ := Real.posLog Cx + (2 * Real.pi)⁻¹ * J
  let B : ℝ := 1
  have hJ : 0 ≤ J := integral_nonneg_of_ae (by
    filter_upwards with t
    unfold logSineMajorant
    split_ifs with hs
    · exact le_rfl
    · exact Real.log_nonneg (by
        have : 0 < |Real.sin t|⁻¹ := inv_pos.mpr (abs_pos.mpr hs)
        linarith))
  have hnormpos : 0 < 2 * Real.pi := by positivity
  have hA : 0 ≤ A := by
    dsimp [A]
    exact add_nonneg Real.posLog_nonneg
      (mul_nonneg (inv_nonneg.mpr hnormpos.le) hJ)
  refine ⟨A, B, hA, by simp [B], ?_⟩
  intro R hR
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hmero : MeromorphicOn (activeM data x) (Metric.sphere 0 |R|) := by
    intro z hz
    exact (meromorphicOn_activeM data x hx).1 z (by simp)
  have hlhsInterval : IntervalIntegrable
      (fun t : ℝ => Real.posLog ‖activeM data x
        ((R : ℂ) * Complex.exp (Complex.I * (t : ℂ)))‖)
      volume 0 (2 * Real.pi) := by
    have hcirc := hmero.circleIntegrable_posLog_norm
    simpa only [CircleIntegrable, circleMap_zero, mul_comm] using hcirc
  have hlhs : IntegrableOn
      (fun t : ℝ => Real.posLog ‖activeM data x
        ((R : ℂ) * Complex.exp (Complex.I * (t : ℂ)))‖)
      (Set.Ioc 0 (2 * Real.pi)) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)]
    exact hlhsInterval
  have hrhs : IntegrableOn
      (fun t : ℝ => Real.posLog Cx + Real.log R + logSineMajorant t)
      (Set.Ioc 0 (2 * Real.pi)) := by
    have hc : IntegrableOn (fun _t : ℝ => Real.posLog Cx + Real.log R)
        (Set.Ioc 0 (2 * Real.pi)) :=
      integrableOn_const measure_Ioc_lt_top.ne
    change IntegrableOn
      ((fun _t : ℝ => Real.posLog Cx + Real.log R) + logSineMajorant)
      (Set.Ioc 0 (2 * Real.pi))
    exact hc.add integrableOn_logSineMajorant
  have hpoint : ∀ᵐ t : ℝ ∂volume.restrict (Set.Ioc 0 (2 * Real.pi)),
      Real.posLog ‖activeM data x
        ((R : ℂ) * Complex.exp (Complex.I * (t : ℂ)))‖ ≤
      Real.posLog Cx + Real.log R + logSineMajorant t := by
    filter_upwards [hbound R hR] with t ht
    by_cases hs : Real.sin t = 0
    · have hmono := Real.posLog_le_posLog (norm_nonneg _) (by simpa [hs] using ht)
      calc
        Real.posLog ‖activeM data x
            ((R : ℂ) * Complex.exp (Complex.I * (t : ℂ)))‖ ≤
            Real.posLog (Cx * R) := hmono
        _ ≤ Real.posLog Cx + Real.posLog R := Real.posLog_mul
        _ = Real.posLog Cx + Real.log R + logSineMajorant t := by
          have hposR : Real.posLog R = Real.log R :=
            Real.posLog_eq_log (by simpa [abs_of_pos hRpos] using hR)
          rw [hposR]
          simp [logSineMajorant, hs]
    have hgpos : 0 < 1 + |Real.sin t|⁻¹ := by
      have : 0 < |Real.sin t|⁻¹ := inv_pos.mpr (abs_pos.mpr hs)
      linarith
    calc
      Real.posLog ‖activeM data x
          ((R : ℂ) * Complex.exp (Complex.I * (t : ℂ)))‖ ≤
          Real.posLog (Cx * R * (1 + |Real.sin t|⁻¹)) :=
        Real.posLog_le_posLog (norm_nonneg _) ht
      _ ≤ Real.posLog (Cx * R) + Real.posLog (1 + |Real.sin t|⁻¹) :=
        Real.posLog_mul
      _ ≤ (Real.posLog Cx + Real.posLog R) +
          Real.posLog (1 + |Real.sin t|⁻¹) := by
        have hm := Real.posLog_mul (x := Cx) (y := R)
        linarith
      _ = Real.posLog Cx + Real.posLog R +
          Real.posLog (1 + |Real.sin t|⁻¹) := rfl
      _ = Real.posLog Cx + Real.log R + logSineMajorant t := by
        have hposR : Real.posLog R = Real.log R :=
          Real.posLog_eq_log (by simpa [abs_of_pos hRpos] using hR)
        have hposG : Real.posLog (1 + |Real.sin t|⁻¹) =
            Real.log (1 + |Real.sin t|⁻¹) :=
          Real.posLog_eq_log (by
            rw [abs_of_pos hgpos]
            linarith [inv_pos.mpr (abs_pos.mpr hs)])
        rw [hposR, hposG]
        simp [logSineMajorant, hs]
  have hint := integral_mono_ae hlhs hrhs hpoint
  have hnorminv : 0 ≤ (2 * Real.pi)⁻¹ := inv_nonneg.mpr hnormpos.le
  have hmul := mul_le_mul_of_nonneg_left hint hnorminv
  have hc : Integrable (fun _t : ℝ => Real.posLog Cx + Real.log R)
      (volume.restrict (Set.Ioc 0 (2 * Real.pi))) :=
    integrableOn_const measure_Ioc_lt_top.ne
  have hrhs_eq :
      (∫ t in Set.Ioc (0 : ℝ) (2 * Real.pi),
        Real.posLog Cx + Real.log R + logSineMajorant t) =
      (Real.posLog Cx + Real.log R) * (2 * Real.pi) + J := by
    rw [integral_add (μ := volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi)))
      hc integrableOn_logSineMajorant]
    rw [integral_const, measureReal_restrict_apply_univ,
      Real.volume_real_Ioc_of_le (by positivity)]
    simp only [smul_eq_mul, J]
    ring
  rw [hrhs_eq] at hmul
  calc
    circlePosLogMean (activeM data x) R =
        (2 * Real.pi)⁻¹ *
          (∫ t in Set.Ioc (0 : ℝ) (2 * Real.pi),
            Real.posLog ‖activeM data x
              ((R : ℂ) * Complex.exp (Complex.I * (t : ℂ)))‖) := by
      unfold circlePosLogMean Real.posLog
      congr 2
      funext t
      exact max_comm _ _
    _ ≤ (2 * Real.pi)⁻¹ *
        ((Real.posLog Cx + Real.log R) * (2 * Real.pi) + J) := hmul
    _ = A + B * Real.log R := by
      dsimp [A, B]
      field_simp [hnormpos.ne']
      ring

/- Proof idea: divide the affine-in-log upper bound by positive large radii and squeeze between zero
and a function whose constant-over-radius and `log R / R` terms tend to zero. -/
theorem circlePosLogMean_div_tendsto_zero {alpha : ℝ} {beta : ℚ} {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f) (x : AddCircle (1 : ℝ)) (hx : AnalyticParameter data x) (hactive : Nonempty (ActiveIndex data x)) : Tendsto (fun R : ℝ => circlePosLogMean (activeM data x) R / R) atTop (nhds 0) := by
  rcases circlePosLogMean_le_log data x hx hactive with
    ⟨A, B, _hA, _hB, hbound⟩
  have hAdiv : Tendsto (fun R : ℝ => A / R) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hlogdiv : Tendsto (fun R : ℝ => Real.log R / R) atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hupper : Tendsto (fun R : ℝ => (A + B * Real.log R) / R)
      atTop (nhds 0) := by
    convert hAdiv.add (hlogdiv.const_mul B) using 1
    funext R
    ring
    simp
  apply squeeze_zero'
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    apply div_nonneg
    · unfold circlePosLogMean
      apply mul_nonneg (inv_nonneg.mpr (by positivity))
      exact integral_nonneg_of_ae (by
        filter_upwards with t
        exact le_max_right _ _)
    · exact hR.le
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    exact div_le_div_of_nonneg_right (hbound R hR) (zero_lt_one.trans_le hR).le
  · exact hupper

end Theorem12.Internal
