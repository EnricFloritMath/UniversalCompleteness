import UniversalCompletenessHD.GenericLpDuality
import UniversalCompletenessHD.RecoveryUniqueness

noncomputable section

open MeasureTheory Set
open scoped ENNReal Topology

namespace UniversalCompletenessHD.Internal

/- Coercion of the exact positive exponential `Lp` atom. -/
private theorem coeFn_positiveExponentialLpHD {d : Nat}
    (S : Set (RealVec d)) (hSmeas : MeasurableSet S)
    (hSfinite : volume S ≠ ∞) (p : ENNReal) (hp : 1 ≤ p)
    (xi : RealVec d) :
    letI : Fact (1 ≤ p) := ⟨hp⟩
    ⇑(positiveExponentialLpHD S hSmeas p hp hSfinite xi)
      =ᵐ[volume.restrict S] fourierCharHD xi := by
  dsimp only [positiveExponentialLpHD]
  exact (memLp_fourierCharHD_restrict S hSmeas hSfinite p hp xi).coeFn_toLp

/-
`conj_kernel_negative_sampleHD`. Exact same-frequency conjugation identity. No set reflection or
frequency negation occurs; the integral is in the atom-times-kernel order used
by the generic representation formula.
-/
private theorem conj_kernel_negative_sampleHD {d : Nat}
    (S : Set (RealVec d)) (g : RealVec d → Complex) (xi : RealVec d) :
    negativeFourierSampleOnHD S (fun x => starRingEnd Complex (g x)) xi =
      starRingEnd Complex
        (∫ x : RealVec d, fourierCharHD xi x * g x ∂(volume.restrict S)) := by
  rw [negativeFourierSampleOnHD]
  calc
    (∫ x : RealVec d in S,
        starRingEnd Complex (g x) * starRingEnd Complex (fourierCharHD xi x) ∂volume) =
        ∫ x : RealVec d in S,
          starRingEnd Complex (fourierCharHD xi x * g x) ∂volume := by
      apply integral_congr_ae
      filter_upwards
      intro x
      rw [map_mul]
      ring
    _ = starRingEnd Complex
        (∫ x : RealVec d in S, fourierCharHD xi x * g x ∂volume) := integral_conj

/-
`exists_annihilatorKernelHD`. Specialize the exact generic finite-measure `Lp` representation,
including the endpoint `p=1`.
-/
private theorem exists_annihilatorKernelHD {d : Nat}
    (S : Set (RealVec d)) (hSmeas : MeasurableSet S)
    (hSlt : volume S < ENNReal.ofReal 1)
    (p : ENNReal) (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (L : letI : Fact (1 ≤ p) := ⟨hp⟩;
      Lp Complex p (volume.restrict S) →L[Complex] Complex) :
    Nonempty (Theorem12.Generic.LpKernelRepresentation
      (volume.restrict S) p hp L) := by
  letI : Fact (1 ≤ p) := ⟨hp⟩
  letI : IsFiniteMeasure (volume.restrict S) :=
    isFiniteMeasure_restrict.mpr
      (ne_of_lt (lt_of_lt_of_le hSlt le_top))
  exact exists_LpKernelRepresentationHD (volume.restrict S) p hp hpTop L

/-
`annihilatorHD_eq_zero`. Represent an annihilator, turn its atom pairings into negative
samples of the conjugated kernel, apply `l1_uniqueness_negative_fixedHD`, and recover `L=0`.
-/
private theorem annihilatorHD_eq_zero (P : Params)
    (S : Set (RealVec P.d)) (hSmeas : MeasurableSet S)
    (hSlt : volume S < ENNReal.ofReal 1)
    (p : ENNReal) (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (L : letI : Fact (1 ≤ p) := ⟨hp⟩;
      Lp Complex p (volume.restrict S) →L[Complex] Complex)
    (hannihilates : ∀ xi : RealVec P.d, xi ∈ modulatedLambdaSetHD P.alpha P.beta →
      L (positiveExponentialLpHD S hSmeas p hp
        (ne_of_lt (lt_of_lt_of_le hSlt le_top)) xi) = 0) :
    L = 0 := by
  let hSfinite : volume S ≠ ∞ := ne_of_lt (lt_of_lt_of_le hSlt le_top)
  letI : Fact (1 ≤ p) := ⟨hp⟩
  letI : IsFiniteMeasure (volume.restrict S) :=
    isFiniteMeasure_restrict.mpr hSfinite
  let rep := (exists_annihilatorKernelHD S hSmeas hSlt p hp hpTop L).some
  letI : p.HolderConjugate (ENNReal.conjExponent p) :=
    ENNReal.HolderConjugate.conjExponent hp
  letI : (ENNReal.conjExponent p).HolderConjugate p :=
    ENNReal.HolderConjugate.symm
  have hq : 1 ≤ ENNReal.conjExponent p :=
    ENNReal.HolderConjugate.one_le (ENNReal.conjExponent p) p
  have hkernelInt : Integrable rep.kernel (volume.restrict S) :=
    rep.memLp_kernel.integrable hq
  have hconjInt : Integrable (fun x => starRingEnd Complex (rep.kernel x))
      (volume.restrict S) := by
    simpa only [Complex.conjCLE_apply] using
      ((Complex.conjCLE.integrable_comp_iff).mpr hkernelInt)
  have hpositive (n : IntVec P.d) :
      (∫ x : RealVec P.d,
        fourierCharHD (modulatedLambdaHD P.alpha P.beta n) x * rep.kernel x
          ∂(volume.restrict S)) = 0 := by
    let atom := positiveExponentialLpHD S hSmeas p hp hSfinite
      (modulatedLambdaHD P.alpha P.beta n)
    calc
      (∫ x : RealVec P.d,
        fourierCharHD (modulatedLambdaHD P.alpha P.beta n) x * rep.kernel x
          ∂(volume.restrict S)) =
          ∫ x : RealVec P.d, (atom : RealVec P.d → Complex) x * rep.kernel x
            ∂(volume.restrict S) := by
              apply integral_congr_ae
              exact (coeFn_positiveExponentialLpHD S hSmeas hSfinite p hp
                (modulatedLambdaHD P.alpha P.beta n)).symm.mul
                  Filter.EventuallyEq.rfl
      _ = L atom := (rep.formula atom).symm
      _ = 0 := hannihilates (modulatedLambdaHD P.alpha P.beta n) ⟨n, rfl⟩
  have hnegative (n : IntVec P.d) :
      negativeFourierSampleOnHD S (fun x => starRingEnd Complex (rep.kernel x))
        (modulatedLambdaHD P.alpha P.beta n) = 0 := by
    rw [conj_kernel_negative_sampleHD, hpositive n]
    simp
  have hconjZero : (fun x => starRingEnd Complex (rep.kernel x))
      =ᵐ[volume.restrict S] (fun _ => 0) :=
    l1_uniqueness_negative_fixedHD P S hSmeas hSlt _ hconjInt hnegative
  have hkernelZero : rep.kernel =ᵐ[volume.restrict S] (fun _ => 0) := by
    filter_upwards [hconjZero] with x hx
    have hx' := congrArg (starRingEnd Complex) hx
    simpa using hx'
  apply ContinuousLinearMap.ext
  intro h
  calc
    L h = ∫ x : RealVec P.d, (h : RealVec P.d → Complex) x * rep.kernel x
        ∂(volume.restrict S) := rep.formula h
    _ = ∫ x : RealVec P.d, (h : RealVec P.d → Complex) x * 0
        ∂(volume.restrict S) := by
      exact integral_congr_ae (Filter.EventuallyEq.rfl.mul hkernelZero)
    _ = (0 : Lp Complex p (volume.restrict S) →L[Complex] Complex) h := by simp

/-
`exponentialSpanHD_dense`. Hahn--Banach separation plus `annihilatorHD_eq_zero` gives density of the
literal positive-exponential span; no reflexivity argument is used.
-/
private theorem exponentialSpanHD_dense (P : Params)
    (S : Set (RealVec P.d)) (hSmeas : MeasurableSet S)
    (hSlt : volume S < ENNReal.ofReal 1)
    (p : ENNReal) (hp : 1 ≤ p) (hpTop : p ≠ ∞) :
    ExponentialCompleteInLpHD (modulatedLambdaSetHD P.alpha P.beta)
      S hSmeas p hp (ne_of_lt (lt_of_lt_of_le hSlt le_top)) := by
  let hSfinite : volume S ≠ ∞ := ne_of_lt (lt_of_lt_of_le hSlt le_top)
  letI : Fact (1 ≤ p) := ⟨hp⟩
  letI : IsFiniteMeasure (volume.restrict S) :=
    isFiniteMeasure_restrict.mpr hSfinite
  dsimp only [ExponentialCompleteInLpHD]
  by_contra hDense
  obtain ⟨L, hLne, hLvanish⟩ :=
    exists_nonzero_clm_annihilating_of_not_dense _ hDense
  have hannihilates : ∀ xi : RealVec P.d,
      xi ∈ modulatedLambdaSetHD P.alpha P.beta →
      L (positiveExponentialLpHD S hSmeas p hp hSfinite xi) = 0 := by
    intro xi hxi
    let atom : Lp Complex p (volume.restrict S) :=
      positiveExponentialLpHD S hSmeas p hp hSfinite xi
    have hatom : atom ∈ Submodule.span Complex
        (Set.range (fun eta :
          {x : RealVec P.d // x ∈ modulatedLambdaSetHD P.alpha P.beta} =>
            positiveExponentialLpHD S hSmeas p hp hSfinite eta.1)) := by
      apply Submodule.subset_span
      exact ⟨⟨xi, hxi⟩, rfl⟩
    exact hLvanish ⟨atom, hatom⟩
  have hLzero : L = 0 :=
    annihilatorHD_eq_zero P S hSmeas hSlt p hp hpTop L hannihilates
  exact hLne hLzero

end UniversalCompletenessHD.Internal

namespace UniversalCompletenessHD

/- Public finite-`Lp` completeness, explicitly including `p=1`. -/
theorem modulatedLambdaSetHD_completeLp
    (d : Nat) (hd : 0 < d) (alpha beta : RealVec d)
    (hAlpha : RationallyIndependentWithOneHD alpha)
    (hPole : PoleNonresonant alpha beta)
    (hBeta : euclideanNormHD beta < 1 / 2) :
    UniversalFiniteLpCompletenessHD (modulatedLambdaSetHD alpha beta) := by
  intro S hSmeas hSlt p hp hpTop
  let P : Params :=
    { d := d
      hd := hd
      alpha := alpha
      beta := beta
      alpha_independent := hAlpha
      pole_nonresonant := hPole
      beta_small := hBeta }
  simpa [P] using
    Internal.exponentialSpanHD_dense P S hSmeas hSlt p hp hpTop

end UniversalCompletenessHD
