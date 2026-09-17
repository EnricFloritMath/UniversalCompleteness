import UniversalCompletenessHD.GeometryDensity
import UniversalCompletenessHD.RecoveryUniqueness
import UniversalCompletenessHD.LpCompleteness

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace UniversalCompletenessHD

/- Proof idea: assemble the five component exports into the transparent
conclusion structure. No mathematics or convention change occurs here. -/
theorem universal_completeness_higher_dimension
    (d : Nat) (hd : 0 < d) (alpha beta : RealVec d)
    (hAlpha : RationallyIndependentWithOneHD alpha)
    (hPole : PoleNonresonant alpha beta)
    (hBeta : euclideanNormHD beta < 1 / 2) :
    UniversalCompletenessHDConclusion d alpha beta := by
  exact
    { uniformlyDiscrete :=
        modulatedLambdaSetHD_uniformlyDiscrete alpha beta hBeta
      countEstimate :=
        modulatedLambdaSetHD_countEstimate hd alpha beta hBeta
      uniformDensity :=
        modulatedLambdaSetHD_uniformDensityOne hd alpha beta hBeta
      universalL1 :=
        modulatedLambdaSetHD_universalL1 d hd alpha beta hAlpha hPole hBeta
      completeLp :=
        modulatedLambdaSetHD_completeLp d hd alpha beta hAlpha hPole hBeta }

end UniversalCompletenessHD
