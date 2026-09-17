import IntegerFrequenciesHD.PublicAssembly

/-!
# Integer frequencies in higher dimension

This file expands the three conclusions and derives them from the theorem in
`PublicAssembly`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace IntegerFrequenciesHD

theorem integer_frequencies_higher_dimension_basic
    (d : Nat) (hd : 0 < d) (alpha : RealVec d)
    (hAlpha : RationallyIndependentWithOne alpha)
    (v : Real) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    HasUniformCubicalDensity (integerFrequencySetHD alpha v) v ∧
      (∀ (S : Set (RealVec d)), MeasurableSet S → S ⊆ unitCubeHD d →
        volume S < ENNReal.ofReal v →
          ∀ (f : RealVec d → Complex), Integrable f (volume.restrict S) →
            (∀ n ∈ integerFrequencySetHD alpha v,
              fourierSampleOnHD S f (fun i => (n i : Real)) = 0) →
            f =ᵐ[volume.restrict S] (fun _ => 0)) ∧
      (∀ (S : Set (RealVec d)) (hSmeas : MeasurableSet S)
        (hSsub : S ⊆ unitCubeHD d)
        (hSlt : volume S < ENNReal.ofReal v)
        (p : ENNReal) (hp : 1 ≤ p) (hpTop : p ≠ ∞),
        ExponentialCompleteInLpHD (integerFrequencySetHD alpha v)
          S hSmeas p hp (ne_of_lt (lt_of_lt_of_le hSlt le_top))) := by
  have h := integer_frequencies_higher_dimension
    d hd alpha hAlpha v hv0 hv1
  refine ⟨h.density, h.universalL1, ?_⟩
  intro S hSmeas hSsub hSlt p hp hpTop
  exact h.completeLp S hSmeas hSsub hSlt p hp hpTop

end IntegerFrequenciesHD
