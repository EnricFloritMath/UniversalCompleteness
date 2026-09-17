import IntegerFrequenciesHD.WeightedOrbitSummability
import Theorem14.Broadening

/-!
# Canonical one-dimensional broadening of multitorus orbit data

This module proves the broadening step.  The input function is on
the product torus, while the canonical synthesized output remains a continuous
function on `UnitAddCircle`.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology

local instance broadeningMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance broadeningIsAddHaarMeasureUnitAddCircle : Measure.IsAddHaarMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance broadeningIsProbabilityMeasureUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace IntegerFrequenciesHD.Internal

/- Unfold the canonical definition and apply the proved
one-dimensional Fourier-synthesis coefficient theorem to the supplied norm
summability premise. -/
theorem mFourierCoeff_broadenedFunctionHD {d : Nat}
    {epsilon : Real} {alpha : RealVec d} {F : Torus d → Complex}
    {x : Torus d}
    (hsum : Summable (fun k : Int =>
      ‖weightedOrbitCoeffHD epsilon alpha F x k‖)) (k : Int) :
    fourierCoeff (broadenedFunctionHD epsilon alpha F x) k =
      weightedOrbitCoeffHD epsilon alpha F x k := by
  simpa only [broadenedFunctionHD] using
    Theorem14.Internal.fourierCoeff_fourierSynthesis hsum k

private theorem mFourier_zsmul_alphaTorus {d : Nat}
    (alpha : RealVec d) (n : IntVec d) (k : Int) :
    UnitAddTorus.mFourier n (k • alphaTorus alpha) =
      fourier k ((dotIntReal n alpha : Real) : UnitAddCircle) := by
  simp only [UnitAddTorus.mFourier, alphaTorus, ContinuousMap.coe_mk,
    Pi.smul_apply, ← QuotientAddGroup.mk_zsmul, fourier_coe_apply,
    ← Complex.exp_sum, dotIntReal, Complex.ofReal_sum,
    Complex.ofReal_mul, Complex.ofReal_intCast]
  congr 1
  push_cast
  rw [Finset.mul_sum]
  simp only [div_one, zsmul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/- Expand only the finite product-Fejer sum.  Factor the orbit
phase by multitorus character multiplicativity, move the finite outer sum
through the already justified one-dimensional synthesis, and identify every
inner series with the exported `fourierSynthesis_windowTranslate`.  The
translate is the positive quotient class of `dotIntReal n alpha`. -/
theorem broadenedFunctionHD_productFejerMean_eq_translateSum {d : Nat}
    (epsilon : Real) (alpha : RealVec d)
    (he0 : 0 < epsilon) (he1 : epsilon < 1)
    (F : Torus d → Complex) (N : Nat) (x : Torus d) :
    broadenedFunctionHD epsilon alpha (productFejerMean N F) x =
      ∑ n ∈ multiIndexBox d N,
        (((productFejerMultiplier N n : Real) : Complex) *
          UnitAddTorus.mFourierCoeff F n * UnitAddTorus.mFourier n x) •
            Theorem14.Internal.tentWindowTranslate epsilon he0 he1
              ((dotIntReal n alpha : Real) : UnitAddCircle) := by
  classical
  let s : Finset (IntVec d) := multiIndexBox d N
  let a : IntVec d → UnitAddCircle := fun n =>
    ((dotIntReal n alpha : Real) : UnitAddCircle)
  let A : IntVec d → Complex := fun n =>
    ((productFejerMultiplier N n : Real) : Complex) *
      UnitAddTorus.mFourierCoeff F n * UnitAddTorus.mFourier n x
  have hphase (n : IntVec d) (k : Int) :
      UnitAddTorus.mFourier n (x - k • alphaTorus alpha) =
        UnitAddTorus.mFourier n x * fourier (-k) (a n) := by
    calc
      UnitAddTorus.mFourier n (x - k • alphaTorus alpha) =
          UnitAddTorus.mFourier n x *
            UnitAddTorus.mFourier n (-(k • alphaTorus alpha)) := by
        simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk,
          sub_eq_add_neg, Pi.add_apply, Pi.neg_apply]
        rw [← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro i hi
        simp only [fourier_apply, zsmul_add, AddCircle.toCircle_add,
          Circle.coe_mul]
      _ = UnitAddTorus.mFourier n x * fourier (-k) (a n) := by
        congr 1
        rw [show -(k • alphaTorus alpha) = (-k) • alphaTorus alpha by simp]
        exact mFourier_zsmul_alphaTorus alpha n (-k)
  have hcoeff (k : Int) :
      weightedOrbitCoeffHD epsilon alpha (productFejerMean N F) x k =
        ∑ n ∈ s, A n *
          (fourier (-k) (a n) * Theorem14.Internal.windowCoeff epsilon k) := by
    rw [weightedOrbitCoeffHD, productFejerMean]
    simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [hphase n k]
    simp only [A, a]
    ring
  have hbase (n : IntVec d) : Summable (fun k : Int =>
      (fourier (-k) (a n) * Theorem14.Internal.windowCoeff epsilon k) •
        (fourier k : C(AddCircle (1 : Real), Complex))) := by
    apply Summable.of_norm
    simpa [norm_smul, fourier_norm, norm_mul, fourier_apply] using
      (Theorem14.Internal.summable_windowCoeff_and_tsum_norm
        epsilon he0 he1).1
  have hterms : ∀ n ∈ s, Summable (fun k : Int =>
      A n • ((fourier (-k) (a n) *
        Theorem14.Internal.windowCoeff epsilon k) •
          (fourier k : C(AddCircle (1 : Real), Complex)))) := by
    intro n hn
    exact (hbase n).const_smul (A n)
  rw [broadenedFunctionHD, Theorem14.Internal.fourierSynthesis]
  calc
    (∑' k : Int,
        weightedOrbitCoeffHD epsilon alpha (productFejerMean N F) x k •
          (fourier k : C(AddCircle (1 : Real), Complex))) =
        ∑' k : Int, ∑ n ∈ s,
          A n • ((fourier (-k) (a n) *
            Theorem14.Internal.windowCoeff epsilon k) •
              (fourier k : C(AddCircle (1 : Real), Complex))) := by
      apply tsum_congr
      intro k
      rw [hcoeff k]
      calc
        (∑ n ∈ s, A n *
            (fourier (-k) (a n) * Theorem14.Internal.windowCoeff epsilon k)) •
              (fourier k : C(AddCircle (1 : Real), Complex)) =
            ∑ n ∈ s,
              (A n * (fourier (-k) (a n) *
                Theorem14.Internal.windowCoeff epsilon k)) •
                  (fourier k : C(AddCircle (1 : Real), Complex)) :=
          Finset.sum_smul (R := Complex)
            (M := C(AddCircle (1 : Real), Complex))
            (f := fun n => A n *
              (fourier (-k) (a n) *
                Theorem14.Internal.windowCoeff epsilon k))
            (s := s) (x := (fourier k : C(AddCircle (1 : Real), Complex)))
        _ = ∑ n ∈ s,
            A n • ((fourier (-k) (a n) *
              Theorem14.Internal.windowCoeff epsilon k) •
                (fourier k : C(AddCircle (1 : Real), Complex))) := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [mul_smul]
    _ = ∑ n ∈ s, ∑' k : Int,
        A n • ((fourier (-k) (a n) *
          Theorem14.Internal.windowCoeff epsilon k) •
            (fourier k : C(AddCircle (1 : Real), Complex))) :=
      Summable.tsum_finsetSum hterms
    _ = ∑ n ∈ s, A n • ∑' k : Int,
        (fourier (-k) (a n) * Theorem14.Internal.windowCoeff epsilon k) •
          (fourier k : C(AddCircle (1 : Real), Complex)) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact (hbase n).tsum_const_smul (A n)
    _ = ∑ n ∈ s,
        A n • Theorem14.Internal.tentWindowTranslate epsilon he0 he1 (a n) := by
      apply Finset.sum_congr rfl
      intro n hn
      change A n • Theorem14.Internal.fourierSynthesis
          (fun k : Int => fourier (-k) (a n) *
            Theorem14.Internal.windowCoeff epsilon k) =
        A n • Theorem14.Internal.tentWindowTranslate epsilon he0 he1 (a n)
      rw [Theorem14.Internal.fourierSynthesis_windowTranslate
        epsilon he0 he1 (a n)]
    _ = ∑ n ∈ multiIndexBox d N,
        (((productFejerMultiplier N n : Real) : Complex) *
          UnitAddTorus.mFourierCoeff F n * UnitAddTorus.mFourier n x) •
            Theorem14.Internal.tentWindowTranslate epsilon he0 he1
              ((dotIntReal n alpha : Real) : UnitAddCircle) := by
      rfl

/- Selected finite terms vanish by the coefficient hypothesis.
For every nonselected phase use `fract < 1-v`; translating the literal tent
support `[0,epsilon]` stays in `[0,1-v+epsilon]` without wrap because
`epsilon<v<1`. -/
theorem supported_broadenedFunctionHD_productFejerMean {d : Nat}
    {alpha : RealVec d} {v epsilon : Real} {F : Torus d → Complex}
    (hv0 : 0 < v) (hv1 : v < 1)
    (he0 : 0 < epsilon) (hev : epsilon < v)
    (hzero : ∀ n ∈ integerFrequencySetHD alpha v,
      UnitAddTorus.mFourierCoeff F n = 0)
    (N : Nat) (x : Torus d) :
    Theorem14.Internal.SupportedInInitialArc
      (broadenedFunctionHD epsilon alpha (productFejerMean N F) x)
      (1 - v + epsilon) := by
  have _hv0 : 0 < v := hv0
  have he1 : epsilon < 1 := lt_trans hev hv1
  intro t ht
  rw [broadenedFunctionHD_productFejerMean_eq_translateSum
    epsilon alpha he0 he1 F N x]
  simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply]
  apply Finset.sum_eq_zero
  intro n hn
  by_cases hselected : n ∈ integerFrequencySetHD alpha v
  · simp [hzero n hselected]
  · have hfractLt : Int.fract (dotIntReal n alpha) < 1 - v := by
      by_contra hnot
      apply hselected
      exact ⟨le_of_not_gt hnot, Int.fract_lt_one _⟩
    let a : UnitAddCircle :=
      ((dotIntReal n alpha : Real) : UnitAddCircle)
    let u : Real := Theorem12.Generic.unitRep (t - a)
    let r : Real := Int.fract (dotIntReal n alpha)
    change r < 1 - v at hfractLt
    have hr0 : 0 ≤ r := Int.fract_nonneg _
    have htranslate :
        Theorem14.Internal.tentWindowTranslate epsilon he0 he1 a t = 0 := by
      change Theorem14.Internal.tentWindow epsilon (t - a) = 0
      apply (Theorem14.Internal.tentWindow_formula_and_support
        epsilon he0 he1).2
      intro hu
      change u ∈ Set.Icc (0 : Real) epsilon at hu
      have haRep : Theorem12.Generic.unitRep a = r := by
        simp only [a, r, Theorem12.Generic.unitRep_coe_eq_fract]
      have ha : a = ((r : Real) : UnitAddCircle) := by
        rw [← haRep]
        exact (Theorem12.Generic.coe_unitRep a).symm
      have hta : t - a = ((u : Real) : UnitAddCircle) := by
        exact (Theorem12.Generic.coe_unitRep (t - a)).symm
      have htCoe : t = ((u + r : Real) : UnitAddCircle) := by
        calc
          t = (t - a) + a := by abel
          _ = ((u : Real) : UnitAddCircle) +
              ((r : Real) : UnitAddCircle) := by rw [hta, ha]
          _ = ((u + r : Real) : UnitAddCircle) := by
            rw [AddCircle.coe_add]
      have hurIco : u + r ∈ Set.Ico (0 : Real) 1 := by
        constructor
        · exact add_nonneg hu.1 hr0
        · linarith [hu.2, hfractLt, hev]
      have htRep : Theorem12.Generic.unitRep t = u + r := by
        rw [htCoe, Theorem12.Generic.unitRep_coe_eq_fract,
          Int.fract_eq_self.mpr hurIco]
      apply ht
      rw [htRep]
      constructor
      · exact hurIco.1
      · linarith [hu.2, hfractLt]
    change (((productFejerMultiplier N n : Real) : Complex) *
      UnitAddTorus.mFourierCoeff F n * UnitAddTorus.mFourier n x) •
        Theorem14.Internal.tentWindowTranslate epsilon he0 he1 a t = 0
    rw [htranslate]
    simp

/- Choose one summably fast product-Fejer approximation and
restrict to its single weighted-approximation event.  Stage coefficient
sequences converge in l1, so their one-dimensional Fourier syntheses converge
uniformly to the canonical target.  Pass the common support through that
uniform limit and fill exact coefficients with `mFourierCoeff_broadenedFunctionHD`. -/
theorem broadeningHD_ae {d : Nat}
    {alpha : RealVec d} {v epsilon : Real} {F : Torus d → Complex}
    (hF : Integrable F volume)
    (hv0 : 0 < v) (hv1 : v < 1)
    (he0 : 0 < epsilon) (hev : epsilon < v)
    (hzero : ∀ n ∈ integerFrequencySetHD alpha v,
      UnitAddTorus.mFourierCoeff F n = 0) :
    ∀ᵐ x ∂volume, BroadeningDataHD epsilon alpha v F x := by
  have he1 : epsilon < 1 := lt_trans hev hv1
  obtain ⟨A⟩ := exists_productFejerApproximation hF
  filter_upwards [weightedApproximationAtHD_ae hF A he0 he1] with x hx
  let G : Nat → C(AddCircle (1 : Real), Complex) := fun j =>
    broadenedFunctionHD epsilon alpha (productFejerMean (A.index j) F) x
  let G0 : C(AddCircle (1 : Real), Complex) :=
    broadenedFunctionHD epsilon alpha F x
  let E : Nat → Real := fun j => ∑' k : Int,
    ‖weightedOrbitCoeffHD epsilon alpha
      (fun y => productFejerMean (A.index j) F y - F y) x k‖
  have hcoeffSub (j : Nat) (k : Int) :
      weightedOrbitCoeffHD epsilon alpha
          (productFejerMean (A.index j) F) x k -
        weightedOrbitCoeffHD epsilon alpha F x k =
      weightedOrbitCoeffHD epsilon alpha
        (fun y => productFejerMean (A.index j) F y - F y) x k := by
    unfold weightedOrbitCoeffHD
    ring
  have hdiffSummable (j : Nat) : Summable (fun k : Int =>
      ‖weightedOrbitCoeffHD epsilon alpha
          (productFejerMean (A.index j) F) x k -
        weightedOrbitCoeffHD epsilon alpha F x k‖) := by
    simpa only [hcoeffSub j] using hx.errorSummable j
  have hbound (j : Nat) : ‖G j - G0‖ ≤ E j := by
    dsimp only [G, G0, E]
    change
      ‖Theorem14.Internal.fourierSynthesis
          (weightedOrbitCoeffHD epsilon alpha
            (productFejerMean (A.index j) F) x) -
        Theorem14.Internal.fourierSynthesis
          (weightedOrbitCoeffHD epsilon alpha F x)‖ ≤ _
    calc
      ‖Theorem14.Internal.fourierSynthesis
          (weightedOrbitCoeffHD epsilon alpha
            (productFejerMean (A.index j) F) x) -
        Theorem14.Internal.fourierSynthesis
          (weightedOrbitCoeffHD epsilon alpha F x)‖ ≤
          ∑' k : Int,
            ‖weightedOrbitCoeffHD epsilon alpha
                (productFejerMean (A.index j) F) x k -
              weightedOrbitCoeffHD epsilon alpha F x k‖ :=
        Theorem14.Internal.norm_fourierSynthesis_sub_le
          (hx.stageSummable j) hx.targetSummable (hdiffSummable j)
      _ = ∑' k : Int,
          ‖weightedOrbitCoeffHD epsilon alpha
            (fun y => productFejerMean (A.index j) F y - F y) x k‖ := by
        apply tsum_congr
        intro k
        rw [hcoeffSub j k]
  have hEtend : Tendsto E atTop (nhds 0) :=
    hx.summable_errorNorm.tendsto_atTop_zero
  have hnormTend : Tendsto (fun j => ‖G j - G0‖) atTop (nhds 0) :=
    squeeze_zero'
      (Filter.Eventually.of_forall fun j => norm_nonneg (G j - G0))
      (Filter.Eventually.of_forall hbound) hEtend
  have hGtend : Tendsto G atTop (nhds G0) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr hnormTend
  have hstageSupport (j : Nat) :
      Theorem14.Internal.SupportedInInitialArc (G j) (1 - v + epsilon) := by
    dsimp only [G]
    exact supported_broadenedFunctionHD_productFejerMean
      hv0 hv1 he0 hev hzero (A.index j) x
  have htargetSupport :
      Theorem14.Internal.SupportedInInitialArc G0 (1 - v + epsilon) := by
    intro t ht
    have hstageZero (j : Nat) : G j t = 0 := hstageSupport j t ht
    have hevalTend : Tendsto (fun j => G j t) atTop (nhds (G0 t)) :=
      ((continuous_eval_const t).tendsto G0).comp hGtend
    have hzeroTend : Tendsto (fun j => G j t) atTop (nhds 0) := by
      have hseq : (fun j => G j t) = (fun _ : Nat => (0 : Complex)) := by
        funext j
        exact hstageZero j
      rw [hseq]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique hevalTend hzeroTend
  refine
    { coeffSummable := hx.targetSummable
      coeff_eq := ?_
      supported := ?_ }
  · intro k
    exact mFourierCoeff_broadenedFunctionHD hx.targetSummable k
  · exact htargetSupport

end IntegerFrequenciesHD.Internal
