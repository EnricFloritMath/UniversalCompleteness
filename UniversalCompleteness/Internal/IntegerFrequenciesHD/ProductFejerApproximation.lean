import IntegerFrequenciesHD.CubeTorusBridge
import Theorem14.FejerApproximation
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# Tensor-product Fejer approximation

This module proves tensor-product Fejer approximation.  All
transparent definitions and proposition structures are centralized in
`IntegerFrequenciesHD.Definitions`.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology

local instance productFejerMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance productFejerIsAddHaarMeasureUnitAddCircle : Measure.IsAddHaarMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance productFejerIsProbabilityMeasureUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance productFejerIsNegInvariantTorus (d : Nat) :
    Measure.IsNegInvariant (volume : Measure (UnitAddTorus (Fin d))) :=
  Measure.IsAddHaarMeasure.isNegInvariant_of_innerRegular volume

namespace IntegerFrequenciesHD.Internal

private theorem mFourierCoeff_mFourier {d : Nat} (m n : IntVec d) :
    UnitAddTorus.mFourierCoeff (UnitAddTorus.mFourier m) n =
      if m = n then 1 else 0 := by
  have h := (orthonormal_iff_ite.mp
    (UnitAddTorus.orthonormal_mFourier (d := Fin d))) n m
  simpa only [ContinuousMap.inner_toLp, UnitAddTorus.mFourierCoeff,
    UnitAddTorus.coeFn_mFourierLp, UnitAddTorus.mFourier_neg,
    smul_eq_mul, mul_comm, eq_comm] using h

/- Integrate the finite tensor mean termwise and collapse the
character coefficients with multitorus orthogonality.  Inside the box the
coefficient is the literal tensor multiplier; outside it, a coordinate outside
`[-N,N]` makes that multiplier zero. -/
theorem mFourierCoeff_productFejerMean {d : Nat}
    (N : Nat) (F : Torus d → Complex) (n : IntVec d) :
    UnitAddTorus.mFourierCoeff (productFejerMean N F) n =
      ((productFejerMultiplier N n : Real) : Complex) *
        UnitAddTorus.mFourierCoeff F n := by
  classical
  rw [productFejerMean]
  change (∫ t : Torus d, UnitAddTorus.mFourier (-n) t •
      (∑ m ∈ multiIndexBox d N,
        (((productFejerMultiplier N m : Real) : Complex) *
          UnitAddTorus.mFourierCoeff F m) • UnitAddTorus.mFourier m) t) = _
  simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply]
  rw [show (fun t : Torus d => UnitAddTorus.mFourier (-n) t •
      ∑ m ∈ multiIndexBox d N,
        (((productFejerMultiplier N m : Real) : Complex) *
          UnitAddTorus.mFourierCoeff F m) • UnitAddTorus.mFourier m t) =
    ∑ m ∈ multiIndexBox d N, fun t : Torus d =>
      UnitAddTorus.mFourier (-n) t •
        ((((productFejerMultiplier N m : Real) : Complex) *
          UnitAddTorus.mFourierCoeff F m) • UnitAddTorus.mFourier m t) by
    funext t
    simp only [smul_eq_mul, Finset.sum_apply]
    rw [Finset.mul_sum]
  ]
  rw [show (∑ m ∈ multiIndexBox d N, fun t : Torus d =>
      UnitAddTorus.mFourier (-n) t •
        ((((productFejerMultiplier N m : Real) : Complex) *
          UnitAddTorus.mFourierCoeff F m) • UnitAddTorus.mFourier m t)) =
    fun t : Torus d => ∑ m ∈ multiIndexBox d N,
      UnitAddTorus.mFourier (-n) t •
        ((((productFejerMultiplier N m : Real) : Complex) *
          UnitAddTorus.mFourierCoeff F m) • UnitAddTorus.mFourier m t) by
    funext t
    simp only [Finset.sum_apply]]
  rw [integral_finsetSum]
  · have hterm (m : IntVec d) :
        (∫ t : Torus d, UnitAddTorus.mFourier (-n) t •
          ((((productFejerMultiplier N m : Real) : Complex) *
            UnitAddTorus.mFourierCoeff F m) • UnitAddTorus.mFourier m t)) =
          (((productFejerMultiplier N m : Real) : Complex) *
            UnitAddTorus.mFourierCoeff F m) * (if m = n then 1 else 0) := by
      let c : Complex := ((productFejerMultiplier N m : Real) : Complex) *
        UnitAddTorus.mFourierCoeff F m
      calc
        (∫ t : Torus d, UnitAddTorus.mFourier (-n) t •
            (c • UnitAddTorus.mFourier m t)) =
            ∫ t : Torus d,
              c * (UnitAddTorus.mFourier (-n) t * UnitAddTorus.mFourier m t) := by
          apply integral_congr_ae
          filter_upwards [] with t
          simp only [smul_eq_mul]
          ring
        _ = c * ∫ t : Torus d,
              UnitAddTorus.mFourier (-n) t * UnitAddTorus.mFourier m t := by
          rw [integral_const_mul]
        _ = c * UnitAddTorus.mFourierCoeff (UnitAddTorus.mFourier m) n := rfl
        _ = c * (if m = n then 1 else 0) := by
          rw [mFourierCoeff_mFourier]
    simp_rw [hterm]
    by_cases hn : n ∈ multiIndexBox d N
    · rw [Finset.sum_eq_single n]
      · simp
      · intro b hb hbn
        simp [hbn]
      · exact fun h => (h hn).elim
    · have houtside : ∃ i, ¬ n i ∈ Finset.Icc (-(N : Int)) (N : Int) := by
        simpa [multiIndexBox, Fintype.mem_piFinset] using hn
      obtain ⟨i, hi⟩ := houtside
      have hmult : productFejerMultiplier N n = 0 := by
        rw [productFejerMultiplier]
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        rw [Theorem14.Internal.fejerMultiplier]
        simp only [Finset.mem_Icc] at hi
        rw [if_neg]
        simpa [abs_le] using hi
      rw [show (((productFejerMultiplier N n : Real) : Complex) *
          UnitAddTorus.mFourierCoeff F n) = 0 by simp [hmult]]
      apply Finset.sum_eq_zero
      intro m hm
      have hmn : m ≠ n := by
        intro h
        subst m
        exact hn hm
      simp [hmn]
  · intro m hm
    exact Continuous.integrable_of_hasCompactSupport (by fun_prop)
      (HasCompactSupport.of_compactSpace _)

private theorem productFejerKernel_expansion {d : Nat} (N : Nat) (x : Torus d) :
    ((productFejerKernel N x : Real) : Complex) =
      ∑ n ∈ multiIndexBox d N,
        ((productFejerMultiplier N n : Real) : Complex) *
          UnitAddTorus.mFourier n x := by
  classical
  change ((∏ i : Fin d, Theorem14.Internal.fejerKernel N (x i) : Real) :
      Complex) = _
  rw [Complex.ofReal_prod]
  calc
    (∏ i : Fin d,
        ((Theorem14.Internal.fejerKernel N (x i) : Real) : Complex)) =
        ∏ i : Fin d, ∑ k ∈ Finset.Icc (-(N : Int)) (N : Int),
          (Theorem14.Internal.fejerMultiplier N k : Complex) *
            fourier k (x i) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact Theorem14.Internal.fejerKernel_expansion_nonneg_integral N |>.1 (x i)
    _ = ∑ n ∈ Fintype.piFinset
          (fun _ : Fin d => Finset.Icc (-(N : Int)) (N : Int)),
        ∏ i : Fin d,
          ((Theorem14.Internal.fejerMultiplier N (n i) : Real) : Complex) *
            fourier (n i) (x i) := by
      exact Finset.prod_univ_sum _ _
    _ = ∑ n ∈ multiIndexBox d N,
        ((productFejerMultiplier N n : Real) : Complex) *
          UnitAddTorus.mFourier n x := by
      rw [multiIndexBox]
      apply Finset.sum_congr rfl
      intro n hn
      rw [productFejerMultiplier, UnitAddTorus.mFourier]
      push_cast
      rw [Finset.prod_mul_distrib]
      rfl

/- Apply the proved one-dimensional kernel nonnegativity in
every coordinate and use nonnegativity of a finite product. -/
theorem productFejerKernel_nonneg {d : Nat} (N : Nat) (x : Torus d) :
    0 ≤ productFejerKernel N x := by
  rw [productFejerKernel]
  exact Finset.prod_nonneg fun i _ =>
    (Theorem14.Internal.fejerKernel_expansion_nonneg_integral N).2.1 (x i)

/- Factor the product integral coordinatewise using
`integral_fintype_prod_volume_eq_prod`, then rewrite every one-dimensional
factor with the proved mass-one theorem. -/
theorem integral_productFejerKernel (d N : Nat) :
    (∫ x : Torus d, productFejerKernel N x) = 1 := by
  change (∫ x : (Fin d → UnitAddCircle),
    ∏ i, Theorem14.Internal.fejerKernel N (x i)) = 1
  rw [MeasureTheory.integral_fintype_prod_volume_eq_prod]
  calc
    (∏ _i : Fin d, ∫ x : UnitAddCircle,
        Theorem14.Internal.fejerKernel N x) =
        ∏ _i : Fin d, (1 : Real) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact (Theorem14.Internal.fejerKernel_expansion_nonneg_integral N).2.2
    _ = 1 := by simp

/- Expand the proved one-dimensional Fejer kernel in each
coordinate, distribute the finite product of finite sums over `multiIndexBox`,
interchange only the resulting finite sum and the integral, and identify the
coefficient with the multitorus Fourier convention. -/
theorem productFejerMean_eq_convolution {d : Nat}
    {F : Torus d → Complex} (hF : Integrable F volume)
    (N : Nat) (x : Torus d) :
    productFejerMean N F x = productFejerConvolution N F x := by
  classical
  have hcharSub (n : IntVec d) (z : Torus d) :
      UnitAddTorus.mFourier n (x - z) =
        UnitAddTorus.mFourier n x * UnitAddTorus.mFourier (-n) z := by
    simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk,
      Pi.add_apply, Pi.neg_apply, sub_eq_add_neg]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    simp only [fourier_apply, zsmul_add, AddCircle.toCircle_add, Circle.coe_mul]
    rw [show n i • (-z i) = (-n i) • z i by simp]
  have hbase (n : IntVec d) :
      (∫ y : Torus d, UnitAddTorus.mFourier n y * F (x - y)) =
        UnitAddTorus.mFourier n x * UnitAddTorus.mFourierCoeff F n := by
    let g : Torus d → Complex := fun z =>
      UnitAddTorus.mFourier n (x - z) * F z
    calc
      (∫ y : Torus d, UnitAddTorus.mFourier n y * F (x - y)) =
          ∫ y : Torus d, g (x - y) := by
        apply integral_congr_ae
        filter_upwards [] with y
        simp [g]
      _ = ∫ z : Torus d, g z := by
        exact integral_sub_left_eq_self g volume x
      _ = ∫ z : Torus d,
          UnitAddTorus.mFourier n x *
            (UnitAddTorus.mFourier (-n) z * F z) := by
        apply integral_congr_ae
        filter_upwards [] with z
        change UnitAddTorus.mFourier n (x - z) * F z = _
        rw [hcharSub]
        ring
      _ = UnitAddTorus.mFourier n x *
          UnitAddTorus.mFourierCoeff F n := by
        rw [integral_const_mul]
        rfl
  have hfx : Integrable (fun y : Torus d => F (x - y)) volume := by
    change Integrable (F ∘ fun y : Torus d => x - y) volume
    exact (volume : Measure (Torus d)).measurePreserving_sub_left x
      |>.integrable_comp_of_integrable hF
  rw [productFejerMean, productFejerConvolution]
  change (∑ n ∈ multiIndexBox d N,
      (((productFejerMultiplier N n : Real) : Complex) *
        UnitAddTorus.mFourierCoeff F n) • UnitAddTorus.mFourier n) x = _
  simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
  calc
    (∑ n ∈ multiIndexBox d N,
        (((productFejerMultiplier N n : Real) : Complex) *
          UnitAddTorus.mFourierCoeff F n) * UnitAddTorus.mFourier n x) =
      ∑ n ∈ multiIndexBox d N,
        ((productFejerMultiplier N n : Real) : Complex) *
          (UnitAddTorus.mFourier n x * UnitAddTorus.mFourierCoeff F n) := by
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ = ∑ n ∈ multiIndexBox d N,
        ∫ y : Torus d,
          (((productFejerMultiplier N n : Real) : Complex) *
            UnitAddTorus.mFourier n y) * F (x - y) := by
      apply Finset.sum_congr rfl
      intro n hn
      let c : Complex := (productFejerMultiplier N n : Real)
      calc
        ((productFejerMultiplier N n : Real) : Complex) *
            (UnitAddTorus.mFourier n x * UnitAddTorus.mFourierCoeff F n) =
            c * ∫ y : Torus d,
              UnitAddTorus.mFourier n y * F (x - y) := by
          exact congrArg (fun z : Complex => c * z) (hbase n).symm
        _ = ∫ y : Torus d,
            c * (UnitAddTorus.mFourier n y * F (x - y)) := by
          rw [integral_const_mul]
        _ = ∫ y : Torus d,
            (((productFejerMultiplier N n : Real) : Complex) *
              UnitAddTorus.mFourier n y) * F (x - y) := by
          apply integral_congr_ae
          filter_upwards [] with y
          dsimp [c]
          ring
    _ = ∫ y : Torus d, ∑ n ∈ multiIndexBox d N,
        (((productFejerMultiplier N n : Real) : Complex) *
          UnitAddTorus.mFourier n y) * F (x - y) := by
      symm
      rw [integral_finsetSum]
      intro n hn
      have hcharBound : ∀ᵐ y : Torus d ∂volume,
          ‖UnitAddTorus.mFourier n y‖ ≤ (1 : Real) := by
        filter_upwards [] with y
        simpa only [UnitAddTorus.mFourier_norm] using
          (UnitAddTorus.mFourier n).norm_coe_le_norm y
      have hcharMeas : AEStronglyMeasurable
          (fun y : Torus d => UnitAddTorus.mFourier n y) volume :=
        (UnitAddTorus.mFourier n).continuous.aestronglyMeasurable
      have hi : Integrable (fun y : Torus d =>
          UnitAddTorus.mFourier n y * F (x - y)) volume :=
        hfx.bdd_mul hcharMeas hcharBound
      exact (hi.const_mul ((productFejerMultiplier N n : Real) : Complex)).congr
        (Filter.Eventually.of_forall fun y => by ring)
    _ = ∫ y : Torus d,
        ((productFejerKernel N y : Real) : Complex) * F (x - y) := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [productFejerKernel_expansion N y, Finset.sum_mul]

/- Rewrite as the positive mass-one convolution, apply the norm
of an integral and Tonelli, and transport the inner norm integral by Haar
translation.  The resulting contraction constant is exactly one. -/
theorem integral_norm_productFejerMean_le {d : Nat}
    {F : Torus d → Complex} (hF : Integrable F volume) (N : Nat) :
    (∫ x, ‖productFejerMean N F x‖) ≤ ∫ x, ‖F x‖ := by
  classical
  let K : Torus d → Complex := fun y => (productFejerKernel N y : Complex)
  have hKnonneg : ∀ y : Torus d, 0 ≤ productFejerKernel N y :=
    productFejerKernel_nonneg N
  have hK : Integrable K volume := by
    rw [show K = fun y : Torus d =>
        ∑ n ∈ multiIndexBox d N,
          ((productFejerMultiplier N n : Real) : Complex) *
            UnitAddTorus.mFourier n y by
      funext y
      exact productFejerKernel_expansion N y]
    apply integrable_finsetSum
    intro n hn
    exact ((UnitAddTorus.mFourier n).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).const_mul _
  have hprod : Integrable
      (fun p : Torus d × Torus d => K p.2 * F (p.1 - p.2))
      (volume.prod volume) := by
    simpa only [ContinuousLinearMap.mul_apply'] using
      hK.convolution_integrand (ContinuousLinearMap.mul Complex Complex) hF
  have hconv : Integrable
      (fun x : Torus d => ∫ y, K y * F (x - y)) volume :=
    hprod.integral_prod_left
  rw [show (fun x => ‖productFejerMean N F x‖) =
      (fun x => ‖∫ y, K y * F (x - y)‖) by
    funext x
    rw [productFejerMean_eq_convolution hF N x]
    rfl]
  calc
    (∫ x, ‖∫ y, K y * F (x - y)‖) ≤
        ∫ x, ∫ y, ‖K y * F (x - y)‖ := by
      apply integral_mono hconv.norm hprod.norm.integral_prod_left
      intro x
      exact norm_integral_le_integral_norm _
    _ = ∫ y, ∫ x, ‖K y * F (x - y)‖ := by
      exact integral_integral_swap hprod.norm
    _ = ∫ y, ∫ x, productFejerKernel N y * ‖F (x - y)‖ := by
      apply integral_congr_ae
      filter_upwards [] with y
      apply integral_congr_ae
      filter_upwards [] with x
      simp [K, Real.norm_eq_abs, abs_of_nonneg (hKnonneg y)]
    _ = ∫ y, productFejerKernel N y * (∫ x, ‖F x‖) := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [integral_const_mul,
        integral_sub_right_eq_self (μ := volume) (fun x : Torus d => ‖F x‖) y]
    _ = ∫ x, ‖F x‖ := by
      rw [integral_mul_const, integral_productFejerKernel d N, one_mul]

/- Use integrability to subtract the total Bochner Fourier
coefficients, distribute subtraction through the finite box sum, and conclude
by continuous-map extensionality. -/
theorem productFejerMean_sub {d : Nat}
    {F G : Torus d → Complex} (hF : Integrable F volume)
    (hG : Integrable G volume) (N : Nat) :
    productFejerMean N (fun x => F x - G x) =
      productFejerMean N F - productFejerMean N G := by
  classical
  have hcoeffSub (n : IntVec d) :
      UnitAddTorus.mFourierCoeff (fun x => F x - G x) n =
        UnitAddTorus.mFourierCoeff F n - UnitAddTorus.mFourierCoeff G n := by
    unfold UnitAddTorus.mFourierCoeff
    rw [show (fun t : Torus d => UnitAddTorus.mFourier (-n) t • (F t - G t)) =
        (fun t => UnitAddTorus.mFourier (-n) t • F t -
          UnitAddTorus.mFourier (-n) t • G t) by
      funext t
      rw [smul_sub]]
    exact integral_sub
      (hF.bdd_mul (UnitAddTorus.mFourier (-n)).continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by
          simpa only [UnitAddTorus.mFourier_norm] using
            (UnitAddTorus.mFourier (-n)).norm_coe_le_norm x))
      (hG.bdd_mul (UnitAddTorus.mFourier (-n)).continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by
          simpa only [UnitAddTorus.mFourier_norm] using
            (UnitAddTorus.mFourier (-n)).norm_coe_le_norm x))
  ext x
  simp only [productFejerMean, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    ContinuousMap.sub_apply, smul_eq_mul, hcoeffSub, mul_sub]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  ring

/- Rewrite the left side with `productFejerMean_sub` and apply
the preceding L1 contraction to the integrable pointwise difference. -/
theorem integral_norm_productFejerMean_sub_le {d : Nat}
    {F G : Torus d → Complex} (hF : Integrable F volume)
    (hG : Integrable G volume) (N : Nat) :
    (∫ x, ‖productFejerMean N F x - productFejerMean N G x‖) ≤
      ∫ x, ‖F x - G x‖ := by
  have hdiff : Integrable (fun x => F x - G x) volume := hF.sub hG
  calc
    (∫ x, ‖productFejerMean N F x - productFejerMean N G x‖) =
        ∫ x, ‖productFejerMean N (fun x => F x - G x) x‖ := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [productFejerMean_sub hF hG N]
      rfl
    _ ≤ ∫ x, ‖F x - G x‖ := integral_norm_productFejerMean_le hdiff N

/- Bound the convolution pointwise by the continuous-map sup
norm times the nonnegative product kernel and use its exact mass one. -/
theorem norm_productFejerMean_le {d : Nat}
    (F : C(Torus d, Complex)) (N : Nat) :
    ‖productFejerMean N F‖ ≤ ‖F‖ := by
  classical
  have hF : Integrable (F : Torus d → Complex) volume :=
    F.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hKcCont : Continuous (fun y : Torus d =>
      ((productFejerKernel N y : Real) : Complex)) := by
    rw [show (fun y : Torus d => ((productFejerKernel N y : Real) : Complex)) =
        fun y => ∑ n ∈ multiIndexBox d N,
          ((productFejerMultiplier N n : Real) : Complex) *
            UnitAddTorus.mFourier n y by
      funext y
      exact productFejerKernel_expansion N y]
    fun_prop
  have hKCont : Continuous (productFejerKernel N : Torus d → Real) :=
    Complex.continuous_re.comp hKcCont
  apply (ContinuousMap.norm_le _ (norm_nonneg F)).2
  intro x
  rw [productFejerMean_eq_convolution hF N x]
  calc
    ‖∫ y : Torus d,
        ((productFejerKernel N y : Real) : Complex) * F (x - y)‖ ≤
        ∫ y : Torus d, productFejerKernel N y * ‖F (x - y)‖ := by
      calc
        _ ≤ ∫ y : Torus d,
            ‖((productFejerKernel N y : Real) : Complex) * F (x - y)‖ :=
          norm_integral_le_integral_norm _
        _ = _ := by
          apply integral_congr_ae
          filter_upwards [] with y
          simp [Real.norm_eq_abs,
            abs_of_nonneg (productFejerKernel_nonneg N y)]
    _ ≤ ∫ y : Torus d, productFejerKernel N y * ‖F‖ := by
      apply integral_mono
      · exact (hKCont.mul
          ((F.continuous.comp (continuous_const.sub continuous_id)).norm)).integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _)
      · exact hKCont.integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _) |>.mul_const ‖F‖
      · intro y
        exact mul_le_mul_of_nonneg_left (F.norm_coe_le_norm (x - y))
          (productFejerKernel_nonneg N y)
    _ = ‖F‖ := by
      rw [integral_mul_const, integral_productFejerKernel d N, one_mul]

/- Continuous inputs are integrable on the compact probability
torus.  Rewrite the difference as the mean of `F-G`, then apply the exact
sup-norm contraction. -/
theorem norm_productFejerMean_sub_le {d : Nat}
    (F G : C(Torus d, Complex)) (N : Nat) :
    ‖productFejerMean N F - productFejerMean N G‖ ≤ ‖F - G‖ := by
  have hF : Integrable (F : Torus d → Complex) volume :=
    F.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hG : Integrable (G : Torus d → Complex) volume :=
    G.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    ‖productFejerMean N F - productFejerMean N G‖ =
        ‖productFejerMean N (fun x => F x - G x)‖ := by
      rw [productFejerMean_sub hF hG N]
    _ ≤ ‖F - G‖ := norm_productFejerMean_le (F - G) N

private theorem fejerMultiplier_tendsto_one (k : Int) :
    Tendsto (fun N : Nat => Theorem14.Internal.fejerMultiplier N k)
      atTop (nhds 1) := by
  have hden : Tendsto (fun N : Nat => (N : Real) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hratio : Tendsto (fun N : Nat => (|k| : Real) / ((N : Real) + 1))
      atTop (nhds 0) := tendsto_const_nhds.div_atTop hden
  have hformula :
      (fun N : Nat => Theorem14.Internal.fejerMultiplier N k) =ᶠ[atTop]
        (fun N : Nat => 1 - (|k| : Real) / ((N : Real) + 1)) := by
    filter_upwards [eventually_ge_atTop (Int.natAbs k)] with N hN
    rw [Theorem14.Internal.fejerMultiplier, if_pos]
    have hN' : (Int.natAbs k : Int) ≤ (N : Int) := by exact_mod_cast hN
    simpa only [Int.natCast_natAbs] using hN'
  have hone : Tendsto (fun _ : Nat => (1 : Real)) atTop (nhds 1) :=
    tendsto_const_nhds
  simpa only [sub_zero] using (hone.sub hratio).congr' hformula.symm

private theorem productFejerMultiplier_tendsto_one {d : Nat} (n : IntVec d) :
    Tendsto (fun N : Nat => productFejerMultiplier N n) atTop (nhds 1) := by
  rw [show (fun N : Nat => productFejerMultiplier N n) =
      fun N : Nat => ∏ i : Fin d, Theorem14.Internal.fejerMultiplier N (n i) by
    funext N
    rfl]
  simpa using tendsto_finsetProd (Finset.univ : Finset (Fin d))
    (fun i hi => fejerMultiplier_tendsto_one (n i))

private theorem eventually_mem_multiIndexBox {d : Nat} (n : IntVec d) :
    ∀ᶠ N : Nat in atTop, n ∈ multiIndexBox d N := by
  let B : Nat := ∑ i : Fin d, Int.natAbs (n i)
  filter_upwards [eventually_ge_atTop B] with N hN
  rw [multiIndexBox]
  simp only [Fintype.mem_piFinset, Finset.mem_Icc]
  intro i
  have hi : Int.natAbs (n i) ≤ B := by
    dsimp [B]
    exact Finset.single_le_sum (fun j _ => Nat.zero_le (Int.natAbs (n j)))
      (Finset.mem_univ i)
  constructor <;> omega

private theorem productFejerMean_mFourier {d : Nat}
    (N : Nat) (n : IntVec d) :
    productFejerMean N (UnitAddTorus.mFourier n) =
      if n ∈ multiIndexBox d N then
        ((productFejerMultiplier N n : Real) : Complex) •
          UnitAddTorus.mFourier n
      else 0 := by
  classical
  ext x
  simp only [productFejerMean, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    mFourierCoeff_mFourier]
  by_cases hn : n ∈ multiIndexBox d N
  · rw [if_pos hn, Finset.sum_eq_single n]
    · simp
    · intro m hm hmn
      simp [Ne.symm hmn]
    · exact fun h => (h hn).elim
  · rw [if_neg hn]
    apply Finset.sum_eq_zero
    intro m hm
    have hmn : m ≠ n := by
      intro h
      subst m
      exact hn hm
    simp [Ne.symm hmn]

private theorem productFejerMean_tendsto_mFourier {d : Nat} (n : IntVec d) :
    Tendsto (fun N : Nat => productFejerMean N (UnitAddTorus.mFourier n))
      atTop (nhds (UnitAddTorus.mFourier n)) := by
  have hscalarReal := productFejerMultiplier_tendsto_one n
  have hscalarComplex : Tendsto
      (fun N : Nat => ((productFejerMultiplier N n : Real) : Complex))
      atTop (nhds 1) := Complex.continuous_ofReal.continuousAt.tendsto.comp hscalarReal
  have hsmul := hscalarComplex.smul_const (UnitAddTorus.mFourier n)
  have hev :
      (fun N : Nat => ((productFejerMultiplier N n : Real) : Complex) •
        UnitAddTorus.mFourier n) =ᶠ[atTop]
      (fun N : Nat => productFejerMean N (UnitAddTorus.mFourier n)) := by
    filter_upwards [eventually_mem_multiIndexBox n] with N hN
    rw [productFejerMean_mFourier, if_pos hN]
  simpa only [one_smul] using hsmul.congr' hev

private theorem productFejerMean_add_continuous {d : Nat}
    (F G : C(Torus d, Complex)) (N : Nat) :
    productFejerMean N (F + G) =
      productFejerMean N F + productFejerMean N G := by
  classical
  have hF : Integrable (F : Torus d → Complex) volume :=
    F.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hG : Integrable (G : Torus d → Complex) volume :=
    G.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hcoeff (n : IntVec d) :
      UnitAddTorus.mFourierCoeff (F + G) n =
        UnitAddTorus.mFourierCoeff F n + UnitAddTorus.mFourierCoeff G n := by
    unfold UnitAddTorus.mFourierCoeff
    rw [show (fun t : Torus d => UnitAddTorus.mFourier (-n) t • (F + G) t) =
        (fun t => UnitAddTorus.mFourier (-n) t • F t +
          UnitAddTorus.mFourier (-n) t • G t) by
      funext t
      simp only [ContinuousMap.add_apply, smul_add]]
    exact integral_add
      (hF.bdd_mul (UnitAddTorus.mFourier (-n)).continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by
          simpa only [UnitAddTorus.mFourier_norm] using
            (UnitAddTorus.mFourier (-n)).norm_coe_le_norm x))
      (hG.bdd_mul (UnitAddTorus.mFourier (-n)).continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by
          simpa only [UnitAddTorus.mFourier_norm] using
            (UnitAddTorus.mFourier (-n)).norm_coe_le_norm x))
  ext x
  simp only [productFejerMean, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    ContinuousMap.add_apply, smul_eq_mul, hcoeff, mul_add]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  ring

private theorem productFejerMean_smul_continuous {d : Nat}
    (c : Complex) (F : C(Torus d, Complex)) (N : Nat) :
    productFejerMean N (c • F) = c • productFejerMean N F := by
  classical
  have hcoeff (n : IntVec d) :
      UnitAddTorus.mFourierCoeff (c • F) n =
        c * UnitAddTorus.mFourierCoeff F n := by
    unfold UnitAddTorus.mFourierCoeff
    calc
      (∫ t : Torus d, UnitAddTorus.mFourier (-n) t • (c • F) t) =
          ∫ t : Torus d,
            c * (UnitAddTorus.mFourier (-n) t • F t) := by
        apply integral_congr_ae
        filter_upwards [] with t
        simp only [ContinuousMap.smul_apply, smul_eq_mul]
        ring
      _ = c * ∫ t : Torus d,
          UnitAddTorus.mFourier (-n) t • F t := by
        rw [integral_const_mul]
  ext x
  simp only [productFejerMean, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    smul_eq_mul, hcoeff, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  ring

/- Prove diagonal multiplier convergence first on every
`UnitAddTorus.mFourier n`, close under finite linear combinations, then pass
from the dense character span to all continuous functions using the exact
difference contraction. -/
theorem productFejerMean_tendsto_uniform_continuous {d : Nat}
    (F : C(Torus d, Complex)) :
    Tendsto (fun N : Nat => productFejerMean N F) atTop (nhds F) := by
  classical
  let S : Submodule Complex C(Torus d, Complex) :=
    Submodule.span Complex (Set.range (UnitAddTorus.mFourier (d := Fin d)))
  have hspan (G : C(Torus d, Complex)) (hG : G ∈ S) :
      Tendsto (fun N : Nat => productFejerMean N G) atTop (nhds G) := by
    change G ∈ Submodule.span Complex
      (Set.range (UnitAddTorus.mFourier (d := Fin d))) at hG
    induction hG using Submodule.span_induction with
    | mem G hG =>
        obtain ⟨n, rfl⟩ := hG
        exact productFejerMean_tendsto_mFourier n
    | zero =>
        apply (tendsto_const_nhds : Tendsto (fun _ : Nat =>
          (0 : C(Torus d, Complex))) atTop (nhds 0)).congr'
        filter_upwards [] with N
        ext x
        simp [productFejerMean, UnitAddTorus.mFourierCoeff]
    | add G H hGS hHS hGconv hHconv =>
        apply (hGconv.add hHconv).congr'
        filter_upwards [] with N
        exact productFejerMean_add_continuous G H N |>.symm
    | smul c G hGS hGconv =>
        apply hGconv.const_smul c |>.congr'
        filter_upwards [] with N
        exact productFejerMean_smul_continuous c G N |>.symm
  have hclosure : F ∈ closure (S : Set C(Torus d, Complex)) := by
    change F ∈ (S.topologicalClosure : Set C(Torus d, Complex))
    rw [show S.topologicalClosure = ⊤ by
      dsimp [S]
      exact UnitAddTorus.span_mFourier_closure_eq_top]
    trivial
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  obtain ⟨G, hGS, hFG⟩ :=
    (SeminormedAddCommGroup.mem_closure_iff.mp hclosure)
      (epsilon / 3) (by positivity)
  have hGconv := hspan G hGS
  rw [Metric.tendsto_atTop] at hGconv
  obtain ⟨N0, hN0⟩ := hGconv (epsilon / 3) (by positivity)
  refine ⟨N0, ?_⟩
  intro N hN
  have hcenter : ‖productFejerMean N G - G‖ < epsilon / 3 := by
    simpa only [dist_eq_norm] using hN0 N hN
  have hfirst :
      ‖productFejerMean N F - productFejerMean N G‖ < epsilon / 3 :=
    (norm_productFejerMean_sub_le F G N).trans_lt hFG
  have hlast : ‖G - F‖ < epsilon / 3 := by
    simpa only [norm_sub_rev] using hFG
  rw [dist_eq_norm]
  calc
    ‖productFejerMean N F - F‖ =
        ‖(productFejerMean N F - productFejerMean N G) +
          (productFejerMean N G - G) + (G - F)‖ := by
      congr 1
      abel
    _ ≤ ‖productFejerMean N F - productFejerMean N G‖ +
        ‖productFejerMean N G - G‖ + ‖G - F‖ := norm_add₃_le
    _ < epsilon := by linarith

/- Approximate the integrable representative by a bounded
continuous map.  Control the two outer errors with the representative-level
difference contraction and the center error by uniform convergence on the
probability torus. -/
theorem productFejerMean_tendsto_L1 {d : Nat}
    {F : Torus d → Complex} (hF : Integrable F volume) :
    Tendsto (fun N : Nat =>
      ∫ x, ‖productFejerMean N F x - F x‖) atTop (nhds 0) := by
  classical
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  obtain ⟨phi, happrox, hphi⟩ :=
    hF.exists_boundedContinuous_integral_sub_le (by positivity : 0 < epsilon / 4)
  let phiC : C(Torus d, Complex) := phi.toContinuousMap
  have huniform := productFejerMean_tendsto_uniform_continuous phiC
  rw [Metric.tendsto_atTop] at huniform
  obtain ⟨N0, hN0⟩ := huniform (epsilon / 2) (by positivity)
  refine ⟨N0, ?_⟩
  intro N hN
  have hcenterNorm : ‖productFejerMean N phi - phiC‖ < epsilon / 2 := by
    have h := hN0 N hN
    change ‖productFejerMean N phiC - phiC‖ < epsilon / 2
    simpa only [dist_eq_norm] using h
  let A : C(Torus d, Complex) := productFejerMean N F
  let P : C(Torus d, Complex) := productFejerMean N phi
  have hcontinuousIntegrable (g : C(Torus d, Complex)) : Integrable g volume :=
    g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hA : Integrable A volume := hcontinuousIntegrable A
  have hP : Integrable P volume := hcontinuousIntegrable P
  have ht1 : Integrable (fun x : Torus d => ‖A x - P x‖) volume :=
    (hA.sub hP).norm
  have ht2 : Integrable (fun x : Torus d => ‖P x - phi x‖) volume :=
    (hP.sub hphi).norm
  have ht3 : Integrable (fun x : Torus d => ‖phi x - F x‖) volume :=
    (hphi.sub hF).norm
  have hlhs : Integrable (fun x : Torus d => ‖A x - F x‖) volume :=
    (hA.sub hF).norm
  have htriangle :
      (∫ x, ‖A x - F x‖) ≤
        (∫ x, ‖A x - P x‖) + (∫ x, ‖P x - phi x‖) +
          ∫ x, ‖phi x - F x‖ := by
    calc
      (∫ x, ‖A x - F x‖) ≤
          ∫ x, ‖A x - P x‖ + (‖P x - phi x‖ + ‖phi x - F x‖) := by
        apply integral_mono hlhs (ht1.add (ht2.add ht3))
        intro x
        calc
          ‖A x - F x‖ =
              ‖(A x - P x) + (P x - phi x) + (phi x - F x)‖ := by
            congr 1
            ring
          _ ≤ ‖A x - P x‖ + ‖P x - phi x‖ + ‖phi x - F x‖ :=
            norm_add₃_le
          _ = ‖A x - P x‖ + (‖P x - phi x‖ + ‖phi x - F x‖) := by
            ring
      _ = (∫ x, ‖A x - P x‖) + (∫ x, ‖P x - phi x‖) +
          ∫ x, ‖phi x - F x‖ := by
        calc
          (∫ x, ‖A x - P x‖ + (‖P x - phi x‖ + ‖phi x - F x‖)) =
              (∫ x, ‖A x - P x‖) +
                ∫ x, ‖P x - phi x‖ + ‖phi x - F x‖ :=
            integral_add ht1 (ht2.add ht3)
          _ = _ := by
            rw [integral_add ht2 ht3]
            ring
  have hfirst : (∫ x, ‖A x - P x‖) ≤ epsilon / 4 := by
    calc
      (∫ x, ‖A x - P x‖) =
          ∫ x, ‖productFejerMean N F x - productFejerMean N phi x‖ := rfl
      _ ≤ ∫ x, ‖F x - phi x‖ :=
        integral_norm_productFejerMean_sub_le hF hphi N
      _ ≤ epsilon / 4 := happrox
  have hcenter : (∫ x, ‖P x - phi x‖) < epsilon / 2 := by
    calc
      (∫ x, ‖P x - phi x‖) ≤ ∫ _x : Torus d, ‖P - phiC‖ := by
        apply integral_mono ht2 (integrable_const ‖P - phiC‖)
        intro x
        exact (P - phiC).norm_coe_le_norm x
      _ = ‖P - phiC‖ := by simp
      _ < epsilon / 2 := hcenterNorm
  have hlast : (∫ x, ‖phi x - F x‖) ≤ epsilon / 4 := by
    calc
      (∫ x, ‖phi x - F x‖) = ∫ x, ‖F x - phi x‖ := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [norm_sub_rev]
      _ ≤ epsilon / 4 := happrox
  have hfinal : (∫ x, ‖productFejerMean N F x - F x‖) < epsilon := by
    change (∫ x, ‖A x - F x‖) < epsilon
    exact lt_of_le_of_lt htriangle (by linarith)
  have herrNonneg : 0 ≤ ∫ x, ‖productFejerMean N F x - F x‖ :=
    integral_nonneg fun _ => norm_nonneg _
  rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg herrNonneg]
  exact hfinal

/- Every finite product Fejer mean is zero when all multitorus
coefficients vanish.  L1 convergence then gives `integral ‖F‖ = 0`, hence the
same raw representative is zero almost everywhere. -/
theorem ae_zero_of_mFourierCoeff_zero_L1 {d : Nat}
    {F : Torus d → Complex} (hF : Integrable F volume)
    (hzero : ∀ n : IntVec d, UnitAddTorus.mFourierCoeff F n = 0) :
    F =ᵐ[volume] (fun _ => (0 : Complex)) := by
  classical
  have hmeanZero (N : Nat) : productFejerMean N F = 0 := by
    ext x
    simp [productFejerMean, hzero]
  have hconv := productFejerMean_tendsto_L1 hF
  have hconst : Tendsto (fun _ : Nat => ∫ x, ‖F x‖) atTop (nhds 0) := by
    apply hconv.congr'
    filter_upwards [] with N
    apply integral_congr_ae
    filter_upwards [] with x
    rw [hmeanZero N]
    simp only [ContinuousMap.zero_apply, zero_sub, norm_neg]
  have hself : Tendsto (fun _ : Nat => ∫ x, ‖F x‖) atTop (nhds (∫ x, ‖F x‖)) :=
    tendsto_const_nhds
  have hint : (∫ x, ‖F x‖) = 0 :=
    tendsto_nhds_unique hself hconst
  have hnormAE : (fun x => ‖F x‖) =ᵐ[volume] (fun _ => (0 : Real)) :=
    (integral_eq_zero_iff_of_nonneg (fun _ => norm_nonneg _) hF.norm).mp hint
  filter_upwards [hnormAE] with x hx
  exact norm_eq_zero.mp hx

/- From L1 convergence choose at every stage an index with
error at most `(1/2)^(j+1)` and compare the literal selected error series with
the summable geometric series. -/
theorem exists_productFejerApproximation {d : Nat}
    {F : Torus d → Complex} (hF : Integrable F volume) :
    Nonempty (ProductFejerApproximation F) := by
  let err : Nat → Real := fun N =>
    ∫ x, ‖productFejerMean N F x - F x‖
  have herr0 (N : Nat) : 0 ≤ err N := by
    dsimp [err]
    exact integral_nonneg fun _ => norm_nonneg _
  have hconv := productFejerMean_tendsto_L1 hF
  rw [Metric.tendsto_atTop] at hconv
  have hchoose (j : Nat) :
      ∃ N : Nat, err N ≤ ((1 : Real) / 2) ^ (j + 1) := by
    have hr : 0 < ((1 : Real) / 2) ^ (j + 1) := by positivity
    obtain ⟨N, hN⟩ := hconv (((1 : Real) / 2) ^ (j + 1)) hr
    refine ⟨N, le_of_lt ?_⟩
    have h := hN N le_rfl
    simpa [err, dist_zero_right, Real.norm_eq_abs,
      abs_of_nonneg (herr0 N)] using h
  let index : Nat → Nat := fun j => Classical.choose (hchoose j)
  have hindex (j : Nat) : err (index j) ≤ ((1 : Real) / 2) ^ (j + 1) :=
    Classical.choose_spec (hchoose j)
  have hgeom : Summable (fun j : Nat => ((1 : Real) / 2) ^ (j + 1)) := by
    simpa [pow_succ', mul_comm] using
      summable_geometric_two.mul_left ((1 : Real) / 2)
  refine ⟨{ index := index, summable_error := ?_ }⟩
  change Summable (fun j => err (index j))
  exact Summable.of_nonneg_of_le (fun j => herr0 (index j)) hindex hgeom

end IntegerFrequenciesHD.Internal
