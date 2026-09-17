import IntegerFrequenciesHD.Definitions

/-!
# Arithmetic and endpoint theorems

This module proves the arithmetic and endpoint statements using the transparent
definitions and proposition structures in `IntegerFrequenciesHD.Definitions`.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology ComplexConjugate

namespace IntegerFrequenciesHD

/- Instantiate rational independence with constant coefficient `-m`
and coordinate coefficients `n i`; cast normalization then contradicts `n ≠ 0`. -/
theorem nonresonant_dotIntReal {d : Nat} {alpha : RealVec d}
    (hAlpha : RationallyIndependentWithOne alpha)
    (n : IntVec d) (hn : n ≠ 0) (m : Int) :
    dotIntReal n alpha ≠ m := by
  intro hnm
  have hrel : ((-(m : Rat) : Rat) : Real) +
      ∑ i, (((n i : Int) : Rat) : Real) * alpha i = 0 := by
    rw [show ((-(m : Rat) : Rat) : Real) = -(m : Real) by norm_num]
    simp only [Rat.cast_intCast]
    rw [← dotIntReal]
    rw [hnm]
    norm_num
  have hcoeff := (hAlpha (-(m : Rat)) (fun i => (n i : Rat)) hrel).2
  apply hn
  funext i
  have hi : (n i : Rat) = 0 := hcoeff i
  exact_mod_cast hi

/- Unfold the selected interval at `v = 0`; its endpoint
conditions require simultaneously `fract ≥ 1` and `fract < 1`. -/
theorem integerFrequencySetHD_zero {d : Nat} (alpha : RealVec d) :
    integerFrequencySetHD alpha 0 = ∅ := by
  ext n
  simp [integerFrequencySetHD]

/- Unfold the selected interval at `v = 1` and use
`Int.fract_nonneg` together with `Int.fract_lt_one`. -/
theorem integerFrequencySetHD_one {d : Nat} (alpha : RealVec d) :
    integerFrequencySetHD alpha 1 = Set.univ := by
  ext n
  simp [integerFrequencySetHD, Int.fract_nonneg, Int.fract_lt_one]

end IntegerFrequenciesHD
