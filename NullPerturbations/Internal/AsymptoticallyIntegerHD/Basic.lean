import AsymptoticallyIntegerHD.PublicAssembly

/-!
# Library theorem check for Section 6, item (2)

The anonymous example restates the library theorem's type and applies
`AsymptoticallyIntegerHD.theorem_1_4_higher_dimension` directly. The
paper-facing statement is in `NullPerturbations/showcase.lean`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

example (d : Nat) (hd : 0 < d)
    (delta : AsymptoticallyIntegerHD.IntVec d →
      AsymptoticallyIntegerHD.RealVec d)
    (hdelta : AsymptoticallyIntegerHD.TendsToZeroAtIntVecInfinity delta)
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∃ (S : Set (AsymptoticallyIntegerHD.RealVec d))
      (hSmeas : MeasurableSet S) (hSfinite : volume S ≠ ∞),
      volume S < ENNReal.ofReal epsilon ∧
        ¬ AsymptoticallyIntegerHD.ExponentialCompleteInL2HD
          (AsymptoticallyIntegerHD.frequencySet delta)
          S hSmeas hSfinite := by
  exact AsymptoticallyIntegerHD.theorem_1_4_higher_dimension
    d hd delta hdelta epsilon hepsilon
