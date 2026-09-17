import IntegerFrequenciesHD.L1Uniqueness
import Theorem12.GenericLpDuality
import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Finite-Lp completeness

This module proves finite-Lp completeness.  Completeness is reduced to
the proved restricted-L1 uniqueness statement through the proved generic
finite-`Lp` kernel representation and Hahn--Banach annihilator argument.
-/

noncomputable section

open Filter MeasureTheory Set TopologicalSpace
open scoped BigOperators ENNReal Topology

namespace IntegerFrequenciesHD
namespace Internal

/- Unfold the positive exponential atom and use the exact
`MemLp.coeFn_toLp` representative theorem from its finite-measure
construction. -/
theorem coeFn_exponentialLpHD {d : Nat}
    (S : Set (RealVec d)) (hSmeas : MeasurableSet S)
    (hSfinite : volume S ≠ ∞)
    (p : ENNReal) (hp : 1 ≤ p) (n : IntVec d) :
    letI : Fact (1 ≤ p) := ⟨hp⟩
    ⇑(exponentialLpHD S hSmeas p hp hSfinite n)
      =ᵐ[volume.restrict S]
        (fun x => fourierCharHD (fun i => (n i : Real)) x) := by
  dsimp only [exponentialLpHD]
  exact (memLp_fourierCharHD_restrict
    S hSmeas hSfinite p hp n).coeFn_toLp

/- Rewrite the positive atom using `coeFn_exponentialLpHD` and the supplied
kernel representation formula.  Conjugate the resulting integral exactly
once; conjugation converts the positive exponential pairing into the negative
article sample without any symmetry hypothesis on the frequency set. -/
theorem conjugate_kernel_fourierSampleHD {d : Nat}
    (S : Set (RealVec d)) (hSmeas : MeasurableSet S)
    (hSfinite : volume S ≠ ∞)
    (p : ENNReal) (hp : 1 ≤ p)
    (L : letI : Fact (1 ≤ p) := ⟨hp⟩
      Lp Complex p (volume.restrict S) →L[Complex] Complex)
    (rep : Theorem12.Generic.LpKernelRepresentation
      (volume.restrict S) p hp L)
    (n : IntVec d)
    (hannihilates : L (exponentialLpHD S hSmeas p hp hSfinite n) = 0) :
    fourierSampleOnHD S (fun x => starRingEnd Complex (rep.kernel x))
      (fun i => (n i : Real)) = 0 := by
  let atom := exponentialLpHD S hSmeas p hp hSfinite n
  have hpositive :
      (∫ x : RealVec d,
        fourierCharHD (fun i => (n i : Real)) x * rep.kernel x
          ∂volume.restrict S) = 0 := by
    calc
      (∫ x : RealVec d,
          fourierCharHD (fun i => (n i : Real)) x * rep.kernel x
            ∂volume.restrict S) =
          ∫ x : RealVec d, (atom : RealVec d → Complex) x * rep.kernel x
            ∂volume.restrict S := by
              apply integral_congr_ae
              exact (coeFn_exponentialLpHD S hSmeas hSfinite p hp n).symm.mul
                Filter.EventuallyEq.rfl
      _ = L atom := (rep.formula atom).symm
      _ = 0 := hannihilates
  rw [fourierSampleOnHD]
  calc
    (∫ x in S, starRingEnd Complex (rep.kernel x) *
        starRingEnd Complex
          (fourierCharHD (fun i => (n i : Real)) x)) =
        ∫ x in S, starRingEnd Complex
          (fourierCharHD (fun i => (n i : Real)) x * rep.kernel x) := by
            apply integral_congr_ae
            filter_upwards
            intro x
            rw [map_mul]
            ring
    _ = starRingEnd Complex
        (∫ x in S,
          fourierCharHD (fun i => (n i : Real)) x * rep.kernel x) :=
      integral_conj
    _ = 0 := by rw [hpositive]; simp

private lemma exists_nonzero_clm_annihilating_of_not_denseHD
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Complex E]
    (V : Submodule Complex E) (hV : ¬ Dense (↑V : Set E)) :
    ∃ L : E →L[Complex] Complex, L ≠ 0 ∧ ∀ v : V, L v = 0 := by
  have hclosure : closure (↑V : Set E) ≠ Set.univ :=
    mt dense_iff_closure_eq.mpr hV
  obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem _).mp hclosure
  have hconv : Convex Real (closure (↑V : Set E)) := by
    rw [← Submodule.coe_restrictScalars Real V]
    exact (V.restrictScalars Real).convex.closure
  obtain ⟨L, u, hLclosure, hLx⟩ :=
    RCLike.geometric_hahn_banach_closed_point (𝕜 := Complex)
      hconv isClosed_closure hx
  have hu : 0 < u := by
    simpa using hLclosure 0 (subset_closure V.zero_mem)
  have hvanish (v : V) : L v = 0 := by
    by_contra hv
    let c : Complex := ((u + 1 : Real) : Complex) / L v
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

/- If the exact generator span is not dense, separate its
closure by a nonzero complex continuous functional.  Represent that
functional by the proved finite-`Lp` kernel (including `p=1`), use
`conjugate_kernel_fourierSampleHD` to obtain all negative samples of its conjugate, invoke the given
L1 uniqueness implication, and contradict nonzeroness. -/
theorem dense_exponentialSpan_of_l1_uniquenessHD {d : Nat}
    (Lambda : Set (IntVec d)) (S : Set (RealVec d))
    (hSmeas : MeasurableSet S) (hSfinite : volume S ≠ ∞)
    (p : ENNReal) (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (hunique : ∀ f : RealVec d → Complex,
      Integrable f (volume.restrict S) →
      (∀ n ∈ Lambda, fourierSampleOnHD S f
        (fun i => (n i : Real)) = 0) →
      f =ᵐ[volume.restrict S] 0) :
    ExponentialCompleteInLpHD Lambda S hSmeas p hp hSfinite := by
  letI : Fact (1 ≤ p) := ⟨hp⟩
  letI : IsFiniteMeasure (volume.restrict S) :=
    isFiniteMeasure_restrict.mpr hSfinite
  dsimp only [ExponentialCompleteInLpHD]
  by_contra hDense
  obtain ⟨L, hLne, hLvanish⟩ :=
    exists_nonzero_clm_annihilating_of_not_denseHD _ hDense
  have hannihilates : ∀ n : IntVec d, n ∈ Lambda →
      L (exponentialLpHD S hSmeas p hp hSfinite n) = 0 := by
    intro n hn
    let atom : Lp Complex p (volume.restrict S) :=
      exponentialLpHD S hSmeas p hp hSfinite n
    have hatom : atom ∈ Submodule.span Complex
        (Set.range (fun m : {n : IntVec d // n ∈ Lambda} =>
          exponentialLpHD S hSmeas p hp hSfinite m.1)) := by
      apply Submodule.subset_span
      exact ⟨⟨n, hn⟩, rfl⟩
    exact hLvanish ⟨atom, hatom⟩
  let rep := (Theorem12.Generic.exists_LpKernelRepresentation
    (volume.restrict S) p hp hpTop L).some
  letI : p.HolderConjugate (ENNReal.conjExponent p) :=
    ENNReal.HolderConjugate.conjExponent hp
  letI : (ENNReal.conjExponent p).HolderConjugate p :=
    ENNReal.HolderConjugate.symm
  have hq : 1 ≤ ENNReal.conjExponent p :=
    ENNReal.HolderConjugate.one_le (ENNReal.conjExponent p) p
  have hkernelInt : Integrable rep.kernel (volume.restrict S) :=
    rep.memLp_kernel.integrable hq
  have hconjInt : Integrable
      (fun x => starRingEnd Complex (rep.kernel x))
      (volume.restrict S) := by
    simpa only [Complex.conjCLE_apply] using
      ((Complex.conjCLE.integrable_comp_iff).mpr hkernelInt)
  have hnegative (n : IntVec d) (hn : n ∈ Lambda) :
      fourierSampleOnHD S (fun x => starRingEnd Complex (rep.kernel x))
        (fun i => (n i : Real)) = 0 :=
    conjugate_kernel_fourierSampleHD S hSmeas hSfinite p hp L rep n
      (hannihilates n hn)
  have hconjZero : (fun x => starRingEnd Complex (rep.kernel x))
      =ᵐ[volume.restrict S] (fun _ => 0) :=
    hunique _ hconjInt hnegative
  have hkernelZero : rep.kernel =ᵐ[volume.restrict S] (fun _ => 0) := by
    filter_upwards [hconjZero] with x hx
    have hx' := congrArg (starRingEnd Complex) hx
    simpa using hx'
  have hLzero : L = 0 := by
    apply ContinuousLinearMap.ext
    intro h
    calc
      L h = ∫ x : RealVec d, (h : RealVec d → Complex) x * rep.kernel x
          ∂volume.restrict S := rep.formula h
      _ = ∫ x : RealVec d, (h : RealVec d → Complex) x * 0
          ∂volume.restrict S := by
        exact integral_congr_ae (Filter.EventuallyEq.rfl.mul hkernelZero)
      _ = (0 : Lp Complex p (volume.restrict S) →L[Complex] Complex) h := by
        simp
  exact hLne hLzero

end Internal

/- Derive the exact finite-measure witness from `hSlt`,
specialize the public restricted-L1 uniqueness theorem to the same carrier,
and apply the generic density reduction with unchanged atom parameters. -/
theorem integerFrequencySetHD_completeLp
    (d : Nat) (alpha : RealVec d)
    (hAlpha : RationallyIndependentWithOne alpha)
    (v : Real) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (S : Set (RealVec d)) (hSmeas : MeasurableSet S)
    (hSsub : S ⊆ unitCubeHD d)
    (hSlt : volume S < ENNReal.ofReal v)
    (p : ENNReal) (hp : 1 ≤ p) (hpTop : p ≠ ∞) :
    ExponentialCompleteInLpHD (integerFrequencySetHD alpha v)
      S hSmeas p hp (ne_of_lt (lt_of_lt_of_le hSlt le_top)) := by
  let hSfinite : volume S ≠ ∞ :=
    ne_of_lt (lt_of_lt_of_le hSlt le_top)
  apply Internal.dense_exponentialSpan_of_l1_uniquenessHD
    (integerFrequencySetHD alpha v) S hSmeas hSfinite p hp hpTop
  intro f hf hzero
  exact integerFrequencySetHD_universalL1 alpha hAlpha v hv0 hv1
    S hSmeas hSsub hSlt f hf hzero

end IntegerFrequenciesHD
