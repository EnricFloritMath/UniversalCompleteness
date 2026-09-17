import IntegerFrequenciesHD.CubicalFrequencyDensity
import IntegerFrequenciesHD.L1Uniqueness
import IntegerFrequenciesHD.LpCompleteness

/-!
# Public assembly

The theorem and its readable projections correspond to the integer-frequency
statement in the paper.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace IntegerFrequenciesHD

/- Construct the three fields of
`IntegerFrequenciesHDConclusion`: density from module 04, universal restricted
L1 uniqueness from module 09, and finite-Lp completeness from module 10.  The
last field passes the same strict-volume witness to every exponential atom. -/
theorem integer_frequencies_higher_dimension
    (d : Nat) (hd : 0 < d) (alpha : RealVec d)
    (hAlpha : RationallyIndependentWithOne alpha)
    (v : Real) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    IntegerFrequenciesHDConclusion d alpha v := by
  refine
    { density := integerFrequencySetHD_hasUniformCubicalDensity
        hd hAlpha v hv0 hv1
      universalL1 := integerFrequencySetHD_universalL1
        alpha hAlpha v hv0 hv1
      completeLp := ?_ }
  intro S hSmeas hSsub hSlt p hp hpTop
  exact integerFrequencySetHD_completeLp d alpha hAlpha v hv0 hv1
    S hSmeas hSsub hSlt p hp hpTop

/- Project the density field of the stable theorem without
changing any visible dimension, independence, or endpoint hypothesis. -/
theorem integer_frequencies_higher_dimension_density
    (d : Nat) (hd : 0 < d) (alpha : RealVec d)
    (hAlpha : RationallyIndependentWithOne alpha)
    (v : Real) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    HasUniformCubicalDensity (integerFrequencySetHD alpha v) v := by
  exact (integer_frequencies_higher_dimension
    d hd alpha hAlpha v hv0 hv1).density

/- Apply the universal-L1 projection of the stable theorem to
the exact carrier, integrability, and negative-sample hypotheses. -/
theorem integer_frequencies_higher_dimension_l1
    (d : Nat) (hd : 0 < d) (alpha : RealVec d)
    (hAlpha : RationallyIndependentWithOne alpha)
    (v : Real) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (S : Set (RealVec d)) (hSmeas : MeasurableSet S)
    (hSsub : S ⊆ unitCubeHD d)
    (hSlt : volume S < ENNReal.ofReal v)
    (f : RealVec d → Complex)
    (hf : Integrable f (volume.restrict S))
    (hzero : ∀ n ∈ integerFrequencySetHD alpha v,
      fourierSampleOnHD S f (fun i => (n i : Real)) = 0) :
    f =ᵐ[volume.restrict S] 0 := by
  exact (integer_frequencies_higher_dimension
    d hd alpha hAlpha v hv0 hv1).universalL1
      S hSmeas hSsub hSlt f hf hzero

/- Apply the finite-Lp projection of the stable theorem with
the exact carrier data, including `p=1` and excluding only `p=∞`. -/
theorem integer_frequencies_higher_dimension_completeLp
    (d : Nat) (hd : 0 < d) (alpha : RealVec d)
    (hAlpha : RationallyIndependentWithOne alpha)
    (v : Real) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (S : Set (RealVec d)) (hSmeas : MeasurableSet S)
    (hSsub : S ⊆ unitCubeHD d)
    (hSlt : volume S < ENNReal.ofReal v)
    (p : ENNReal) (hp : 1 ≤ p) (hpTop : p ≠ ∞) :
    ExponentialCompleteInLpHD (integerFrequencySetHD alpha v)
      S hSmeas p hp (ne_of_lt (lt_of_lt_of_le hSlt le_top)) := by
  exact (integer_frequencies_higher_dimension
    d hd alpha hAlpha v hv0 hv1).completeLp
      S hSmeas hSsub hSlt p hp hpTop

end IntegerFrequenciesHD
