import Theorem12.Definitions
import Theorem12.GenericLpDuality
import Theorem12.RecoveryUniqueness

noncomputable section

open MeasureTheory Set
open scoped ENNReal Topology

namespace Theorem12.Internal

/- Proof idea: apply the `MemLp.toLp` representative theorem to the exact transparent
`exponentialLp` construction after installing the explicit lower-exponent fact locally. -/
theorem coeFn_exponentialLp (S : Set ℝ) (hSmeas : MeasurableSet S)
    (hSfinite : volume S ≠ ∞) (p : ENNReal) (hp : 1 ≤ p) (xi : ℝ) :
    letI : Fact (1 ≤ p) := ⟨hp⟩
    ⇑(exponentialLp S hSmeas p hp hSfinite xi) =ᵐ[volume.restrict S]
      (fun x : ℝ => Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I *
        (xi : ℂ) * (x : ℂ))) := by
  dsimp only [exponentialLp]
  exact (memLp_exponential_restrict S hSmeas hSfinite p hp xi).coeFn_toLp

end Theorem12.Internal

namespace Theorem12.Generic

/- Proof idea: separate a point outside the closure of the submodule and restrict the resulting
nonzero complex continuous linear functional, which vanishes on the original submodule. -/
theorem exists_nonzero_clm_annihilating_of_not_dense {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] (V : Submodule ℂ E)
    (hV : ¬ Dense (↑V : Set E)) :
    ∃ L : E →L[ℂ] ℂ, L ≠ 0 ∧ ∀ v : V, L v = 0 := by
  have hclosure : closure (↑V : Set E) ≠ Set.univ :=
    mt dense_iff_closure_eq.mpr hV
  obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem _).mp hclosure
  have hconv : Convex ℝ (closure (↑V : Set E)) := by
    rw [← Submodule.coe_restrictScalars ℝ V]
    exact (V.restrictScalars ℝ).convex.closure
  obtain ⟨L, u, hLclosure, hLx⟩ :=
    RCLike.geometric_hahn_banach_closed_point (𝕜 := ℂ)
      hconv isClosed_closure hx
  have hu : 0 < u := by
    simpa using hLclosure 0 (subset_closure V.zero_mem)
  have hvanish (v : V) : L v = 0 := by
    by_contra hv
    let c : ℂ := ((u + 1 : ℝ) : ℂ) / L v
    have hcv : (c • (v : E)) ∈ closure (↑V : Set E) :=
      subset_closure (V.smul_mem c v.2)
    have hbound := hLclosure (c • (v : E)) hcv
    rw [L.map_smul] at hbound
    change Complex.re (c * L v) < u at hbound
    dsimp [c] at hbound
    rw [div_mul_cancel₀ _ hv] at hbound
    norm_num at hbound
  refine ⟨L, ?_, hvanish⟩
  intro hzero
  subst L
  simp at hLx
  linarith

end Theorem12.Generic

namespace Theorem12.Internal

/- Proof idea: derive finiteness of `volume.restrict S` from `volume S < 1`, install that and
`Fact (1 ≤ p)` only in the proof, and apply the generic finite-`Lp` representation theorem. -/
theorem exists_annihilator_kernel (S : Set ℝ) (hSmeas : MeasurableSet S)
    (hSlt : volume S < 1) (p : ENNReal) (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (L : letI : Fact (1 ≤ p) := ⟨hp⟩
      Lp ℂ p (volume.restrict S) →L[ℂ] ℂ) :
    Nonempty (Theorem12.Generic.LpKernelRepresentation
      (volume.restrict S) p hp L) := by
  letI : Fact (1 ≤ p) := ⟨hp⟩
  letI : IsFiniteMeasure (volume.restrict S) :=
    isFiniteMeasure_restrict.mpr
      (ne_of_lt (lt_of_lt_of_le hSlt le_top))
  exact Theorem12.Generic.exists_LpKernelRepresentation
    (volume.restrict S) p hp hpTop L

/- Proof idea: choose the finite-`Lp` kernel, make it integrable on the finite restriction,
conjugate its positive samples into public negative samples, apply `l1_uniqueness_fixed`, and use the
unconjugated representation formula to prove the functional is zero. -/
theorem annihilator_eq_zero (alpha : ℝ) (hAlpha : Irrational alpha)
    (beta : ℚ) (hbeta0 : beta ≠ 0) (hbetaSmall : |(beta : ℝ)| < 1 / 2)
    (S : Set ℝ) (hSmeas : MeasurableSet S) (hSlt : volume S < 1)
    (p : ENNReal) (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (L : letI : Fact (1 ≤ p) := ⟨hp⟩
      Lp ℂ p (volume.restrict S) →L[ℂ] ℂ)
    (hannihilates : ∀ xi : ℝ, xi ∈ frequencySet alpha beta →
      L (exponentialLp S hSmeas p hp
        (ne_of_lt (lt_of_lt_of_le hSlt le_top)) xi) = 0) :
    L = 0 := by
  let hSfinite : volume S ≠ ∞ := ne_of_lt (lt_of_lt_of_le hSlt le_top)
  letI : Fact (1 ≤ p) := ⟨hp⟩
  letI : IsFiniteMeasure (volume.restrict S) :=
    isFiniteMeasure_restrict.mpr hSfinite
  let rep := (exists_annihilator_kernel S hSmeas hSlt p hp hpTop L).some
  letI : p.HolderConjugate (ENNReal.conjExponent p) :=
    ENNReal.HolderConjugate.conjExponent hp
  letI : (ENNReal.conjExponent p).HolderConjugate p :=
    ENNReal.HolderConjugate.symm
  have hq : 1 ≤ ENNReal.conjExponent p :=
    ENNReal.HolderConjugate.one_le (ENNReal.conjExponent p) p
  have hkernelInt : Integrable rep.kernel (volume.restrict S) :=
    rep.memLp_kernel.integrable hq
  have hconjInt : Integrable (fun x => starRingEnd ℂ (rep.kernel x))
      (volume.restrict S) := by
    simpa only [Complex.conjCLE_apply] using
      ((Complex.conjCLE.integrable_comp_iff).mpr hkernelInt)
  have hexpConj (xi x : ℝ) :
      starRingEnd ℂ
          (Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I *
            (xi : ℂ) * (x : ℂ))) =
        Complex.exp (-((2 * Real.pi : ℝ) : ℂ) * Complex.I *
          (xi : ℂ) * (x : ℂ)) := by
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hpositive (n : ℤ) :
      (∫ x : ℝ, Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I *
          (frequency alpha beta n : ℂ) * (x : ℂ)) * rep.kernel x
        ∂volume.restrict S) = 0 := by
    let atom := exponentialLp S hSmeas p hp hSfinite
      (frequency alpha beta n)
    calc
      (∫ x : ℝ, Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I *
          (frequency alpha beta n : ℂ) * (x : ℂ)) * rep.kernel x
        ∂volume.restrict S) =
          ∫ x : ℝ, (atom : ℝ → ℂ) x * rep.kernel x
            ∂volume.restrict S := by
              apply integral_congr_ae
              exact (coeFn_exponentialLp S hSmeas hSfinite p hp
                (frequency alpha beta n)).symm.mul (Filter.EventuallyEq.rfl)
      _ = L atom := (rep.formula atom).symm
      _ = 0 := hannihilates (frequency alpha beta n) ⟨n, rfl⟩
  have hnegative (n : ℤ) :
      fourierSampleOn S (fun x => starRingEnd ℂ (rep.kernel x))
        (frequency alpha beta n) = 0 := by
    rw [fourierSampleOn]
    calc
      (∫ x : ℝ in S, starRingEnd ℂ (rep.kernel x) *
          Complex.exp (-((2 * Real.pi : ℝ) : ℂ) * Complex.I *
            (frequency alpha beta n : ℂ) * (x : ℂ)) ∂volume) =
          ∫ x : ℝ in S, starRingEnd ℂ
            (Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I *
              (frequency alpha beta n : ℂ) * (x : ℂ)) * rep.kernel x)
              ∂volume := by
                apply integral_congr_ae
                filter_upwards
                intro x
                rw [map_mul, hexpConj]
                ring
      _ = starRingEnd ℂ
          (∫ x : ℝ in S, Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I *
            (frequency alpha beta n : ℂ) * (x : ℂ)) * rep.kernel x
              ∂volume) := integral_conj
      _ = 0 := by rw [hpositive n]; simp
  have hconjZero : (fun x => starRingEnd ℂ (rep.kernel x))
      =ᵐ[volume.restrict S] (fun _ => 0) :=
    l1_uniqueness_fixed alpha hAlpha beta hbeta0 hbetaSmall S hSmeas hSlt
      _ hconjInt hnegative
  have hkernelZero : rep.kernel =ᵐ[volume.restrict S] (fun _ => 0) := by
    filter_upwards [hconjZero] with x hx
    have hx' := congrArg (starRingEnd ℂ) hx
    simpa using hx'
  apply ContinuousLinearMap.ext
  intro h
  calc
    L h = ∫ x : ℝ, (h : ℝ → ℂ) x * rep.kernel x ∂volume.restrict S :=
      rep.formula h
    _ = ∫ x : ℝ, (h : ℝ → ℂ) x * 0 ∂volume.restrict S := by
      exact integral_congr_ae (Filter.EventuallyEq.rfl.mul hkernelZero)
    _ = (0 : Lp ℂ p (volume.restrict S) →L[ℂ] ℂ) h := by simp

/- Proof idea: separate a hypothetical nondense exponential span, show the resulting nonzero
functional annihilates every generating atom, and contradict `annihilator_eq_zero`. -/
theorem exponential_span_dense (alpha : ℝ) (hAlpha : Irrational alpha)
    (beta : ℚ) (hbeta0 : beta ≠ 0) (hbetaSmall : |(beta : ℝ)| < 1 / 2)
    (S : Set ℝ) (hSmeas : MeasurableSet S) (hSlt : volume S < 1)
    (p : ENNReal) (hp : 1 ≤ p) (hpTop : p ≠ ∞) :
    ExponentialCompleteInLp (frequencySet alpha beta) S hSmeas p hp
      (ne_of_lt (lt_of_lt_of_le hSlt le_top)) := by
  let hSfinite : volume S ≠ ∞ := ne_of_lt (lt_of_lt_of_le hSlt le_top)
  letI : Fact (1 ≤ p) := ⟨hp⟩
  letI : IsFiniteMeasure (volume.restrict S) :=
    isFiniteMeasure_restrict.mpr hSfinite
  dsimp only [ExponentialCompleteInLp]
  by_contra hDense
  obtain ⟨L, hLne, hLvanish⟩ :=
    Theorem12.Generic.exists_nonzero_clm_annihilating_of_not_dense _ hDense
  have hannihilates : ∀ xi : ℝ, xi ∈ frequencySet alpha beta →
      L (exponentialLp S hSmeas p hp hSfinite xi) = 0 := by
    intro xi hxi
    let atom : Lp ℂ p (volume.restrict S) :=
      exponentialLp S hSmeas p hp hSfinite xi
    have hatom : atom ∈ Submodule.span ℂ
        (Set.range (fun eta : {x : ℝ // x ∈ frequencySet alpha beta} =>
          exponentialLp S hSmeas p hp hSfinite eta.1)) := by
      apply Submodule.subset_span
      exact ⟨⟨xi, hxi⟩, rfl⟩
    exact hLvanish ⟨atom, hatom⟩
  have hLzero : L = 0 := annihilator_eq_zero alpha hAlpha beta hbeta0
    hbetaSmall S hSmeas hSlt p hp hpTop L hannihilates
  exact hLne hLzero

end Theorem12.Internal

namespace Theorem12

/- Proof idea: retain the exact article quantifiers, derive the canonical support-finiteness proof
from `volume S < 1`, and invoke the internal dense-span theorem. -/
theorem frequencySet_completeLp (alpha : ℝ) (hAlpha : Irrational alpha)
    (beta : ℚ) (hbeta0 : beta ≠ 0) (hbetaSmall : |(beta : ℝ)| < 1 / 2)
    (S : Set ℝ) (hSmeas : MeasurableSet S) (hSlt : volume S < 1)
    (p : ENNReal) (hp : 1 ≤ p) (hpTop : p ≠ ∞) :
    ExponentialCompleteInLp (frequencySet alpha beta) S hSmeas p hp
      (ne_of_lt (lt_of_lt_of_le hSlt le_top)) := by
  exact Internal.exponential_span_dense alpha hAlpha beta hbeta0 hbetaSmall
    S hSmeas hSlt p hp hpTop

end Theorem12
