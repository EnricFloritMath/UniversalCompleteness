import UniversalCompletenessHD.Definitions

/-! # Generic finite-`Lp` duality adapters -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace UniversalCompletenessHD.Internal

/- Thin re-export of the proved finite-`Lp` kernel
representation.  Its exact pairing is `L h = ∫ x, h x * kernel x`, and the
conjugate-exponent membership includes the endpoint `p=1`. -/
theorem exists_LpKernelRepresentationHD {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [SigmaFinite mu] [IsFiniteMeasure mu]
    (p : ENNReal) (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (L : letI : Fact (1 ≤ p) := ⟨hp⟩; Lp Complex p mu →L[Complex] Complex) :
    Nonempty (Theorem12.Generic.LpKernelRepresentation mu p hp L) := by
  exact Theorem12.Generic.exists_LpKernelRepresentation mu p hp hpTop L

/- Hahn--Banach separation of a nondense complex submodule;
the functional is explicitly nonzero and annihilates the algebraic submodule
before closure. -/
theorem exists_nonzero_clm_annihilating_of_not_dense {E : Type*}
    [NormedAddCommGroup E] [NormedSpace Complex E] (V : Submodule Complex E)
    (hV : ¬ Dense (↑V : Set E)) :
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

end UniversalCompletenessHD.Internal
