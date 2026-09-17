import AsymptoticallyIntegerHD.Definitions

/-!
# Restricted exponentials and completeness

The declarations below describe restricted exponentials and their completeness.
-/

noncomputable section

open MeasureTheory Set Topology
open scoped ENNReal

namespace AsymptoticallyIntegerHD

namespace Internal

/-- A unit-modulus character belongs to restricted `L²` on
every measurable finite-measure carrier. -/
theorem restrictedExponential_memLp {d : Nat}
    (S : Set (RealVec d)) (_hSmeas : MeasurableSet S)
    (hSfinite : volume S ≠ ∞) (xi : RealVec d) :
    MemLp (fourierChar xi) (2 : ENNReal) (volume.restrict S) := by
  letI : IsFiniteMeasure (volume.restrict S) :=
    isFiniteMeasure_restrict.mpr hSfinite
  have hmeas : AEStronglyMeasurable (fourierChar xi) (volume.restrict S) := by
    apply Continuous.aestronglyMeasurable
    unfold fourierChar
    fun_prop
  apply MemLp.of_bound hmeas 1
  filter_upwards with x
  have harg :
      (((2 * Real.pi : Real) : Complex) * Complex.I *
          ((∑ i : Fin d, xi i * x i : Real) : Complex)) =
        (((2 * Real.pi * ∑ i : Fin d, xi i * x i : Real) : Complex) *
          Complex.I) := by
    push_cast
    ring
  rw [fourierChar, harg]
  exact (Complex.norm_exp_ofReal_mul_I
    (2 * Real.pi * ∑ i : Fin d, xi i * x i)).le

end Internal

/-- The actual restricted-`Lp` positive Fourier atom. -/
def restrictedExponential {d : Nat}
    (S : Set (RealVec d)) (hSmeas : MeasurableSet S)
    (hSfinite : volume S ≠ ∞) (xi : RealVec d) :
    Lp Complex (2 : ENNReal) (volume.restrict S) :=
  (Internal.restrictedExponential_memLp S hSmeas hSfinite xi).toLp
    (fourierChar xi)

/-- Complex algebraic span of the restricted atoms. -/
def exponentialSpan {d : Nat}
    (Lambda : Set (RealVec d)) (S : Set (RealVec d))
    (hSmeas : MeasurableSet S) (hSfinite : volume S ≠ ∞) :
    Submodule Complex (Lp Complex (2 : ENNReal) (volume.restrict S)) :=
  Submodule.span Complex
    {f | ∃ xi ∈ Lambda, f = restrictedExponential S hSmeas hSfinite xi}

/-- Completeness is genuine density of the algebraic span. -/
def ExponentialCompleteInL2HD {d : Nat}
    (Lambda : Set (RealVec d)) (S : Set (RealVec d))
    (hSmeas : MeasurableSet S) (hSfinite : volume S ≠ ∞) : Prop :=
  Dense ((exponentialSpan Lambda S hSmeas hSfinite :
    Submodule Complex (Lp Complex (2 : ENNReal) (volume.restrict S))) :
      Set (Lp Complex (2 : ENNReal) (volume.restrict S)))

end AsymptoticallyIntegerHD
