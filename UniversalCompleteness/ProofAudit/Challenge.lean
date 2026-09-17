import UniversalCompletenessHD.Definitions

/-!
# Trusted challenge: higher-dimensional universal completeness

This file states the target type for the optional proof comparison. Its proof
is intentionally a placeholder: Comparator checks a separately built solution
against this statement. The challenge imports only the definitions needed to
state it, and no module from the solution proof chain.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace ProofAudit

theorem target_universal_completeness_higher_dimension_basic
    (d : Nat) (hd : 0 < d) (alpha beta : Fin d → Real)
    (hAlpha : ∀ (q0 : Rat) (q : Fin d → Rat),
      (q0 : Real) + ∑ i, (q i : Real) * alpha i = 0 →
        q0 = 0 ∧ ∀ i, q i = 0)
    (hPole : ∀ (q0 : Rat) (q : Fin d → Rat),
      (q0 : Real) * (1 + ∑ i, alpha i * beta i) +
          ∑ i, (q i : Real) * beta i = 0 →
        q0 = 0 ∧ ∀ i, q i = 0)
    (hBeta : Real.sqrt (∑ i, beta i ^ 2) < 1 / 2) :
  let theta : UniversalCompletenessHD.IntVec d → Real := fun n =>
    Int.fract (∑ i, (n i : Real) * alpha i) - 1 / 2
  let delta : UniversalCompletenessHD.IntVec d →
      UniversalCompletenessHD.RealVec d := fun n i => theta n * beta i
  let lambda : UniversalCompletenessHD.IntVec d →
      UniversalCompletenessHD.RealVec d := fun n i =>
    (n i : Real) + delta n i
  let Lambda : Set (UniversalCompletenessHD.RealVec d) := Set.range lambda
  (∃ rho : Real, 0 < rho ∧
    ∀ x, x ∈ Lambda → ∀ y, y ∈ Lambda → x ≠ y →
      rho ≤ Real.sqrt (∑ i, (x i - y i) ^ 2)) ∧
  (0 ≤ UniversalCompletenessHD.cubeCountConstantHD d beta ∧
    (∀ x : UniversalCompletenessHD.RealVec d, ∀ R : Real, 1 ≤ R →
      (Lambda ∩ {y | ∀ i, x i ≤ y i ∧ y i < x i + R}).Finite) ∧
    ∀ x : UniversalCompletenessHD.RealVec d, ∀ R : Real, 1 ≤ R →
      abs
        (((((Lambda ∩ {y | ∀ i, x i ≤ y i ∧ y i < x i + R}).ncard :
            Nat) : Real) - R ^ d)) ≤
        UniversalCompletenessHD.cubeCountConstantHD d beta *
          (R ^ (d - 1) + 1)) ∧
  ((∀ x : UniversalCompletenessHD.RealVec d, ∀ R : Real, 0 ≤ R →
      (Lambda ∩ {y | ∀ i, x i ≤ y i ∧ y i < x i + R}).Finite) ∧
    ∀ epsilon : Real, 0 < epsilon →
      ∃ R0 : Real, 0 < R0 ∧
        ∀ x : UniversalCompletenessHD.RealVec d, ∀ R : Real, R0 ≤ R →
          abs
            (((((Lambda ∩ {y | ∀ i, x i ≤ y i ∧ y i < x i + R}).ncard :
                Nat) : Real) / R ^ d) - 1) < epsilon) ∧
  (∀ (S : Set (UniversalCompletenessHD.RealVec d)), MeasurableSet S →
    volume S < ENNReal.ofReal 1 →
    ∀ (f : UniversalCompletenessHD.RealVec d → Complex),
      Integrable f (volume.restrict S) →
      (∀ xi : UniversalCompletenessHD.RealVec d, xi ∈ Lambda →
        (∫ x : UniversalCompletenessHD.RealVec d,
          f x * starRingEnd Complex
            (UniversalCompletenessHD.fourierCharHD xi x)
            ∂(volume.restrict S)) = 0) →
      f =ᵐ[volume.restrict S] (fun _ => 0)) ∧
  (∀ (S : Set (UniversalCompletenessHD.RealVec d))
      (hSmeas : MeasurableSet S)
      (hSlt : volume S < ENNReal.ofReal 1)
      (p : ENNReal) (hp : 1 ≤ p) (hpTop : p ≠ ∞),
    letI : Fact (1 ≤ p) := ⟨hp⟩
    Dense
      (↑(Submodule.span Complex
        (Set.range (fun xi :
            {xi : UniversalCompletenessHD.RealVec d // xi ∈ Lambda} =>
          UniversalCompletenessHD.positiveExponentialLpHD S hSmeas p hp
            (ne_of_lt (lt_of_lt_of_le hSlt le_top)) xi.1))) :
        Set (Lp Complex p (volume.restrict S)))) := by
  sorry

end ProofAudit
