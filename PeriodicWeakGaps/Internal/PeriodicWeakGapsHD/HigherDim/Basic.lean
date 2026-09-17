import PeriodicWeakGapsHD.HigherDim.RecursiveCorrections

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Topology ENNReal FourierTransform

namespace SpectralGapsPrelim.HigherDim

/-!
Library entry point for the higher-dimensional theorem.
-/

/-- Basic higher-dimensional nonuniqueness theorem.

`WeightedPW alpha A f` packages a Fourier-side representative supported in
`A + ℤ^d` with finite weighted `L2` energy. The strict hypothesis
`volume A < 1` is stated explicitly; the construction uses the assumptions
bundled in `AContextHD`. -/
theorem Hermite {d : ℕ} (hd_pos : 0 < d)
    {A Lambda : Set (E d)} {alpha : ℝ} {x0 : E d}
    (hA_meas : MeasurableSet A)
    (hA_sub : A ⊆ unitCube d)
    (hA_pos : 0 < volume A)
    (hA_lt_one : volume A < 1)
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_le_dim : 2 * alpha ≤ (d : ℝ))
    (hLambda : UniformlyDiscrete Lambda)
    (hx0 : x0 ∉ Lambda) :
    ∃ f : E d → ℂ,
      WeightedPW alpha A f ∧
      Continuous f ∧
      f x0 = 1 ∧
      ∀ lambda ∈ Lambda, f lambda = 0 :=
  higher_dimensional_nonuniqueness
    (d := d) hd_pos
    (A := A) (Lambda := Lambda) (alpha := alpha) (x0 := x0)
    hA_meas hA_sub hA_pos hA_lt_one
    halpha_nonneg halpha_le_dim hLambda hx0

theorem higher_dimensional_nonuniqueness_basic {d : ℕ} (hd_pos : 0 < d)
    {A Lambda : Set (E d)} {alpha : ℝ} {x0 : E d}
    (hA_meas : MeasurableSet A)
    (hA_sub : A ⊆ unitCube d)
    (hA_pos : 0 < volume A)
    (hA_lt_one : volume A < 1)
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_le_dim : 2 * alpha ≤ (d : ℝ))
    (hLambda : UniformlyDiscrete Lambda)
    (hx0 : x0 ∉ Lambda) :
    ∃ f : E d → ℂ,
      WeightedPW alpha A f ∧
      Continuous f ∧
      f x0 = 1 ∧
      ∀ lambda ∈ Lambda, f lambda = 0 :=
  Hermite
    (d := d) hd_pos
    (A := A) (Lambda := Lambda) (alpha := alpha) (x0 := x0)
    hA_meas hA_sub hA_pos hA_lt_one
    halpha_nonneg halpha_le_dim hLambda hx0

end SpectralGapsPrelim.HigherDim

