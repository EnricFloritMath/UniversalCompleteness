import Theorem12.Definitions
import Theorem12.GeometryDensity
import Theorem12.RecoveryUniqueness
import Theorem12.LpCompleteness

namespace Theorem12

/- Proof idea: assemble the four component exports into the transparent conclusion. -/
theorem theorem_1_2 (alpha : ℝ) (beta : ℚ) (hAlpha : Irrational alpha)
    (hbeta0 : beta ≠ 0) (hbetaSmall : |(beta : ℝ)| < 1 / 2) :
    Theorem12Conclusion alpha beta where
  uniformlyDiscrete := frequencySet_uniformlyDiscrete alpha beta hbetaSmall
  uniformDensity := frequencySet_uniformDensity alpha beta hbetaSmall
  universalL1 := frequencySet_universalL1 alpha hAlpha beta hbeta0 hbetaSmall
  completeLp := fun S hSmeas hSlt p hp hpTop =>
    frequencySet_completeLp alpha hAlpha beta hbeta0 hbetaSmall S hSmeas hSlt p hp hpTop

end Theorem12
