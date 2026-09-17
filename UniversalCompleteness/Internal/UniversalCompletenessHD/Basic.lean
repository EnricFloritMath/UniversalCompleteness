import UniversalCompletenessHD.PublicAssembly

/-!
# Expanded higher-dimensional completeness theorem

This module expands the higher-dimensional completeness theorem.
The statement displays every hypothesis and conclusion directly.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace UniversalCompletenessHD

/-
This theorem expands the corresponding statement in the paper, displaying
every hypothesis, Fourier sign, half-open cube, measure, count cast, and
finite-p endpoint. Its proof projects the corresponding fields of
`universal_completeness_higher_dimension`.
-/
theorem universal_completeness_higher_dimension_basic
    (d : Nat) (hd : 0 < d) (alpha beta : Fin d → Real)
    (hAlpha : ∀ (q0 : Rat) (q : Fin d → Rat),
      (q0 : Real) + ∑ i, (q i : Real) * alpha i = 0 →
        q0 = 0 ∧ ∀ i, q i = 0)
    (hPole : ∀ (q0 : Rat) (q : Fin d → Rat),
      (q0 : Real) * (1 + ∑ i, alpha i * beta i) +
          ∑ i, (q i : Real) * beta i = 0 →
        q0 = 0 ∧ ∀ i, q i = 0)
    (hBeta : Real.sqrt (∑ i, beta i ^ 2) < 1 / 2) :
  let theta : IntVec d → Real := fun n =>
    Int.fract (∑ i, (n i : Real) * alpha i) - 1 / 2
  let delta : IntVec d → RealVec d := fun n i => theta n * beta i
  let lambda : IntVec d → RealVec d := fun n i =>
    (n i : Real) + delta n i
  let Lambda : Set (RealVec d) := Set.range lambda
  (∃ rho : Real, 0 < rho ∧
    ∀ x, x ∈ Lambda → ∀ y, y ∈ Lambda → x ≠ y →
      rho ≤ Real.sqrt (∑ i, (x i - y i) ^ 2)) ∧
  (0 ≤ cubeCountConstantHD d beta ∧
    (∀ x : RealVec d, ∀ R : Real, 1 ≤ R →
      (Lambda ∩ {y | ∀ i, x i ≤ y i ∧ y i < x i + R}).Finite) ∧
    ∀ x : RealVec d, ∀ R : Real, 1 ≤ R →
      abs
        (((((Lambda ∩ {y | ∀ i, x i ≤ y i ∧ y i < x i + R}).ncard :
            Nat) : Real) - R ^ d)) ≤
        cubeCountConstantHD d beta * (R ^ (d - 1) + 1)) ∧
  ((∀ x : RealVec d, ∀ R : Real, 0 ≤ R →
      (Lambda ∩ {y | ∀ i, x i ≤ y i ∧ y i < x i + R}).Finite) ∧
    ∀ epsilon : Real, 0 < epsilon →
      ∃ R0 : Real, 0 < R0 ∧
        ∀ x : RealVec d, ∀ R : Real, R0 ≤ R →
          abs
            (((((Lambda ∩ {y | ∀ i, x i ≤ y i ∧ y i < x i + R}).ncard :
                Nat) : Real) / R ^ d) - 1) < epsilon) ∧
  (∀ (S : Set (RealVec d)), MeasurableSet S →
    volume S < ENNReal.ofReal 1 →
    ∀ (f : RealVec d → Complex),
      Integrable f (volume.restrict S) →
      (∀ xi : RealVec d, xi ∈ Lambda →
        (∫ x : RealVec d,
          f x * starRingEnd Complex (fourierCharHD xi x)
            ∂(volume.restrict S)) = 0) →
      f =ᵐ[volume.restrict S] (fun _ => 0)) ∧
  (∀ (S : Set (RealVec d)) (hSmeas : MeasurableSet S)
      (hSlt : volume S < ENNReal.ofReal 1)
      (p : ENNReal) (hp : 1 ≤ p) (hpTop : p ≠ ∞),
    letI : Fact (1 ≤ p) := ⟨hp⟩
    Dense
      (↑(Submodule.span Complex
        (Set.range (fun xi : {xi : RealVec d // xi ∈ Lambda} =>
          positiveExponentialLpHD S hSmeas p hp
            (ne_of_lt (lt_of_lt_of_le hSlt le_top)) xi.1))) :
        Set (Lp Complex p (volume.restrict S)))) := by
  have h := universal_completeness_higher_dimension
    d hd alpha beta hAlpha hPole hBeta
  rcases h with ⟨huniform, hcount, hdensity, hL1, hLp⟩
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change IsUniformlyDiscreteHD (modulatedLambdaSetHD alpha beta)
    exact huniform
  · rcases hcount with ⟨hC, hfinite, herror⟩
    refine ⟨hC, ?_, ?_⟩
    · change ∀ x : RealVec d, ∀ R : Real, 1 ≤ R →
        (modulatedLambdaSetHD alpha beta ∩ realCubeHD x R).Finite
      exact hfinite
    · change ∀ x : RealVec d, ∀ R : Real, 1 ≤ R →
        abs (((realFrequencyCubeCountHD (modulatedLambdaSetHD alpha beta) x R :
          Nat) : Real) - R ^ d) ≤
          cubeCountConstantHD d beta * (R ^ (d - 1) + 1)
      exact herror
  · rcases hdensity with ⟨hfinite, hlimit⟩
    refine ⟨?_, ?_⟩
    · change ∀ x : RealVec d, ∀ R : Real, 0 ≤ R →
        (modulatedLambdaSetHD alpha beta ∩ realCubeHD x R).Finite
      exact hfinite
    · change ∀ epsilon : Real, 0 < epsilon →
        ∃ R0 : Real, 0 < R0 ∧ ∀ x : RealVec d, ∀ R : Real, R0 ≤ R →
          abs (((realFrequencyCubeCountHD
            (modulatedLambdaSetHD alpha beta) x R : Nat) : Real) / R ^ d - 1) <
            epsilon
      exact hlimit
  · change UniversalL1UniquenessNegHD (modulatedLambdaSetHD alpha beta)
    exact hL1
  · change UniversalFiniteLpCompletenessHD (modulatedLambdaSetHD alpha beta)
    exact hLp

end UniversalCompletenessHD
