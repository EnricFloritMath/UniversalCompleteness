import Theorem12.GenericAuxiliary
import Theorem12.SupportSlicing
import Theorem12.PoleCoordinates
import Theorem12.MeromorphicSeries
import Theorem12.FourierZeros

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace Theorem12.Internal

/- Proof idea: take the nonnegative ENNReal `tsum` of the translated slice-support indicators. -/
def multiplicityENN {alpha : ℝ} {beta : ℚ} {S : Set ℝ} {f : ℝ → ℂ}
    (data : PositiveInputData alpha beta S f) (y : AddCircle (1 : ℝ)) : ENNReal := by
  classical
  exact ∑' j : ℤ,
    if y - ((((floorBeta beta j : ℤ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ)) ∈
        sliceSupport data j then 1 else 0

/- Proof idea: prove each translated measurable-support indicator AEMeasurable and apply
the ENNReal measurable-`tsum` theorem. -/
theorem aemeasurable_multiplicityENN {alpha : ℝ} {beta : ℚ} {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f) : AEMeasurable (multiplicityENN data) AddCircle.haarAddCircle := by
  unfold multiplicityENN
  apply AEMeasurable.tsum
  intro j
  apply Measurable.aemeasurable
  apply Measurable.ite
  · exact (measurableSet_sliceSupport data j).preimage
      (measurable_id.sub measurable_const)
  · exact measurable_const
  · exact measurable_const

/- Proof idea: apply Tonelli to the nonnegative series, use Haar translation invariance termwise,
then identify the sum of slice-support measures with `supportMassENN`. -/
theorem lintegral_multiplicityENN {alpha : ℝ} {beta : ℚ} {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f) : (∫⁻ y : AddCircle (1 : ℝ), multiplicityENN data y ∂AddCircle.haarAddCircle) = supportMassENN data := by
  classical
  rw [show multiplicityENN data = fun y => ∑' j : ℤ,
      if y - ((((floorBeta beta j : ℤ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ)) ∈
          sliceSupport data j then 1 else 0 from rfl]
  rw [lintegral_tsum]
  · rw [← tsum_sliceSupport_measure data]
    congr 1
    funext j
    let a : AddCircle (1 : ℝ) :=
      ((((floorBeta beta j : ℤ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ))
    let g : AddCircle (1 : ℝ) → ENNReal :=
      (sliceSupport data j).indicator 1
    calc
      (∫⁻ y : AddCircle (1 : ℝ),
          (if y - a ∈ sliceSupport data j then 1 else 0)
          ∂AddCircle.haarAddCircle) =
          ∫⁻ y : AddCircle (1 : ℝ), g (y - a) ∂AddCircle.haarAddCircle := by
            apply lintegral_congr
            intro y
            by_cases hy : y - a ∈ sliceSupport data j <;> simp [g, hy]
      _ = ∫⁻ y : AddCircle (1 : ℝ), g y ∂AddCircle.haarAddCircle :=
        Theorem12.Generic.lintegral_addCircle_sub g a
      _ = AddCircle.haarAddCircle (sliceSupport data j) := by
        simpa only [g] using
          (lintegral_indicator_one (μ := AddCircle.haarAddCircle)
            (measurableSet_sliceSupport data j))
  · intro j
    apply Measurable.aemeasurable
    apply Measurable.ite
    · exact (measurableSet_sliceSupport data j).preimage
        (measurable_id.sub measurable_const)
    · exact measurable_const
    · exact measurable_const

/- Proof idea: combine the non-top support mass with the exact lintegral identity and the
finite-lintegral-implies-finite-a.e. bridge. -/
theorem multiplicityENN_lt_top_ae {alpha : ℝ} {beta : ℚ} {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f) (hSlt : volume S < 1) : ∀ᵐ y : AddCircle (1 : ℝ) ∂AddCircle.haarAddCircle, multiplicityENN data y < ∞ := by
  apply ae_lt_top' (aemeasurable_multiplicityENN data)
  rw [lintegral_multiplicityENN]
  exact supportMassENN_ne_top data hSlt

/- Proof idea: transparently convert the ENNReal multiplicity with `ENNReal.toReal`; all
mathematical uses separately carry finiteness. -/
def multiplicity {alpha : ℝ} {beta : ℚ} {S : Set ℝ} {f : ℝ → ℂ}
    (data : PositiveInputData alpha beta S f) (y : AddCircle (1 : ℝ)) : ℝ :=
  (multiplicityENN data y).toReal

/- Proof idea: convert the finite ENNReal lintegral identity to the real integral of `toReal`
and use the support-mass real/ENNReal round-trip. -/
theorem integrable_multiplicity {alpha : ℝ} {beta : ℚ} {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f) (hSlt : volume S < 1) : Integrable (multiplicity data) AddCircle.haarAddCircle ∧ (∫ y : AddCircle (1 : ℝ), multiplicity data y ∂AddCircle.haarAddCircle) = supportMass data := by
  have hfinite : (∫⁻ y : AddCircle (1 : ℝ), multiplicityENN data y
      ∂AddCircle.haarAddCircle) ≠ ∞ := by
    rw [lintegral_multiplicityENN]
    exact supportMassENN_ne_top data hSlt
  constructor
  · exact integrable_toReal_of_lintegral_ne_top
      (aemeasurable_multiplicityENN data) hfinite
  · rw [show multiplicity data = fun y => (multiplicityENN data y).toReal from rfl,
      integral_toReal (aemeasurable_multiplicityENN data)
        (multiplicityENN_lt_top_ae data hSlt),
      lintegral_multiplicityENN]
    rfl

/- Proof idea: take the `ncard` of the locally finite real pole set inside the centered closed interval. -/
def realPoleCount {alpha : ℝ} {beta : ℚ} {S : Set ℝ} {f : ℝ → ℂ}
    (data : PositiveInputData alpha beta S f) (x : AddCircle (1 : ℝ)) (R : ℝ) : ℕ :=
  (realPoleSet data x ∩ Set.Icc (-R) R).ncard

/- Proof idea: rewrite the torus coordinate, use the off-bad residue/support equivalence,
derive finiteness from the finite ENNReal indicator sum, and convert that sum to `ncard`. -/
theorem ncard_active_second_eq_multiplicity {alpha : ℝ} {beta : ℚ} {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f) (x : AddCircle (1 : ℝ)) (q : ℤ) (hxBad : x ∉ sineBad alpha beta) (hfinite : multiplicityENN data (x - ((((q : ℤ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ))) < ∞) : Set.Finite {a : ActiveIndex data x | a.1.2 = q} ∧ (({a : ActiveIndex data x | a.1.2 = q}.ncard : ℕ) : ENNReal) = multiplicityENN data (x - ((((q : ℤ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ))) := by
  classical
  let P : ℤ → Prop := fun j =>
    uCoordClass alpha beta x j q ∈ sliceSupport data j
  have hcoord : ∀ j : ℤ,
      x - ((((q : ℤ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ)) -
          ((((floorBeta beta j : ℤ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ)) =
        uCoordClass alpha beta x j q := by
    intro j
    unfold uCoordClass
    have hlabel : (((floorBeta beta j + q : ℤ) : ℝ) * alpha) =
        (floorBeta beta j : ℝ) * alpha + (q : ℝ) * alpha := by
      norm_num only [Int.cast_add]
      ring
    rw [hlabel, AddCircle.coe_add]
    abel
  have hmult : multiplicityENN data
      (x - ((((q : ℤ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ))) =
      ∑' j : ℤ, if P j then 1 else 0 := by
    unfold multiplicityENN
    congr 1
    funext j
    rw [hcoord]
  have hsum_ne : (∑' j : ℤ, if P j then (1 : ENNReal) else 0) ≠ ∞ := by
    rw [← hmult]
    exact hfinite.ne
  have hP : Set.Finite {j : ℤ | P j} := by
    have hlev := ENNReal.finite_const_le_of_tsum_ne_top hsum_ne
      (ε := (1 : ENNReal)) one_ne_zero
    convert hlev using 1
    ext j
    by_cases hj : P j <;> simp [hj]
  let sec : Set (ActiveIndex data x) := {a | a.1.2 = q}
  let fstIndex : ActiveIndex data x → ℤ := fun a => a.1.1
  have hmaps : Set.MapsTo fstIndex sec {j : ℤ | P j} := by
    intro a ha
    have hres := a.2
    have hq : a.1.2 = q := ha
    rw [hq] at hres
    exact (residueCoord_ne_zero_iff data x hxBad a.1.1 q).mp hres
  have hinj : Set.InjOn fstIndex sec := by
    intro a ha b hb hab
    apply Subtype.ext
    apply Prod.ext
    · exact hab
    · exact ha.trans hb.symm
  have hactive : Set.Finite {a : ActiveIndex data x | a.1.2 = q} := by
    exact Set.Finite.of_injOn hmaps hinj hP
  refine ⟨hactive, ?_⟩
  rw [hmult, Theorem12.Generic.ennreal_tsum_indicator_eq_ncard P hP]
  norm_cast
  apply Set.ncard_congr (fun a _ => fstIndex a)
  · exact hmaps
  · intro a b ha hb hab
    exact hinj ha hb hab
  intro j hj
  let a : ActiveIndex data x :=
    ⟨(j, q), (residueCoord_ne_zero_iff data x hxBad j q).mpr hj⟩
  exact ⟨a, rfl, rfl⟩

/- Proof idea: apply the supplied inverse-rotation two-sided ergodic adapter to the integrable
real multiplicity and rewrite its mean as `supportMass`. -/
theorem multiplicity_twoSided_average_ae {alpha : ℝ} {beta : ℚ} {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f) (hAlpha : Irrational alpha) (hSlt : volume S < 1) : ∀ᵐ x : AddCircle (1 : ℝ) ∂AddCircle.haarAddCircle, Tendsto (fun N : ℕ => (2 * (N : ℝ) + 1)⁻¹ * ∑ q ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), multiplicity data (x - ((((q : ℤ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ)))) atTop (nhds (supportMass data)) := by
  simpa [(integrable_multiplicity data hSlt).2] using
    (Theorem12.Generic.twoSided_average_irrationalRotation alpha hAlpha
      (multiplicity data) (integrable_multiplicity data hSlt).1)

/- Proof idea: translate the conull finite-multiplicity set by each integer rotation and
intersect the resulting countable family. -/
theorem multiplicity_all_orbit_finite_ae {alpha : ℝ} {beta : ℚ} {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f) (hSlt : volume S < 1) : ∀ᵐ x : AddCircle (1 : ℝ) ∂AddCircle.haarAddCircle, ∀ q : ℤ, multiplicityENN data (x - ((((q : ℤ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ))) < ∞ := by
  apply ae_all_iff.2
  intro q
  let a : AddCircle (1 : ℝ) :=
    ((((q : ℤ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ))
  have hmp := Theorem12.Generic.measurePreserving_addCircle_sub a
  have hfin := multiplicityENN_lt_top_ae data hSlt
  change (fun x : AddCircle (1 : ℝ) => x - a) ⁻¹'
    {y | multiplicityENN data y < ∞} ∈ ae AddCircle.haarAddCircle
  exact hmp.quasiMeasurePreserving.tendsto_ae hfin

/- Proof idea: store the analytic certificate, simultaneous orbit finiteness, and the complete
two-sided real Birkhoff limit at the same parameter. -/
structure PoleAveragePointData {alpha : ℝ} {beta : ℚ} {S : Set ℝ} {f : ℝ → ℂ}
    (data : PositiveInputData alpha beta S f) (x : AddCircle (1 : ℝ)) : Prop where
  analytic : AnalyticParameter data x
  orbitFinite : ∀ q : ℤ,
    multiplicityENN data
      (x - ((((q : ℤ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ))) < ∞
  averageTendsto : Tendsto
    (fun N : ℕ => (2 * (N : ℝ) + 1)⁻¹ *
      ∑ q ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        multiplicity data
          (x - ((((q : ℤ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ))))
    atTop (nhds (supportMass data))

/- Proof idea: use the integer interval from the ceiling of the negative radius to its floor. -/
private def integerWindow (R : ℝ) : Finset ℤ :=
  Finset.Icc (Int.ceil (-R)) (Int.floor R)

/- Proof idea: use the `3/2` displacement bound, exact finite section cardinalities, and
pole-coordinate injectivity to compare the two integer-window sums with the closed count. -/
theorem realPoleCount_sandwich {alpha : ℝ} {beta : ℚ} {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f) (x : AddCircle (1 : ℝ)) (hAlpha : Irrational alpha) (hbeta0 : beta ≠ 0) (hbetaSmall : |(beta : ℝ)| < 1 / 2) (point : PoleAveragePointData data x) (R : ℝ) (hR : 2 < R) :
    (∑ q ∈ integerWindow (R - 2),
      multiplicity data
        (x - ((((q : ℤ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ)))) ≤
        (realPoleCount data x R : ℝ) ∧
      (realPoleCount data x R : ℝ) ≤
        ∑ q ∈ integerWindow (R + 2),
          multiplicity data
            (x - ((((q : ℤ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ))) := by
  classical
  let fiber : ℤ → Set (ActiveIndex data x) := fun q => {a | a.1.2 = q}
  have hfiber (q : ℤ) : (fiber q).Finite :=
    (ncard_active_second_eq_multiplicity data x q point.analytic.1
      (point.orbitFinite q)).1
  have hmult (q : ℤ) :
      multiplicity data
          (x - ((((q : ℤ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ))) =
        ((fiber q).ncard : ℝ) := by
    have h := (ncard_active_second_eq_multiplicity data x q point.analytic.1
      (point.orbitFinite q)).2
    unfold multiplicity
    rw [← h]
    simp [fiber]
  have hdisj : (Set.univ : Set ℤ).PairwiseDisjoint fiber := by
    intro q _ r _ hqr
    change Disjoint (fiber q) (fiber r)
    rw [Set.disjoint_left]
    intro a haq har
    exact hqr (haq.symm.trans har)
  let activeWindow (T : ℝ) : Set (ActiveIndex data x) :=
    {a | a.1.2 ∈ integerWindow T}
  have hactiveWindow (T : ℝ) : (activeWindow T).Finite := by
    have hfin : (↑(integerWindow T) : Set ℤ).Finite :=
      (integerWindow T).finite_toSet
    have hunion : activeWindow T =
        ⋃ q ∈ (↑(integerWindow T) : Set ℤ), fiber q := by
      ext a
      simp [activeWindow, fiber]
    rw [hunion]
    exact hfin.biUnion fun q _ => hfiber q
  have hwindowCard (T : ℝ) :
      (activeWindow T).ncard =
        ∑ q ∈ integerWindow T, (fiber q).ncard := by
    let fiberFin : ℤ → Finset (ActiveIndex data x) :=
      fun q => (hfiber q).toFinset
    have hpair : (↑(integerWindow T) : Set ℤ).PairwiseDisjoint fiberFin := by
      intro q _ r _ hqr
      simpa [fiberFin] using hdisj (Set.mem_univ q) (Set.mem_univ r) hqr
    have hcoe : (↑((integerWindow T).biUnion fiberFin) :
        Set (ActiveIndex data x)) = activeWindow T := by
      ext a
      simp [fiberFin, activeWindow, fiber]
    rw [← hcoe, Set.ncard_coe_finset, Finset.card_biUnion hpair]
    apply Finset.sum_congr rfl
    intro q hq
    exact (Set.ncard_eq_toFinset_card (fiber q) (hfiber q)).symm
  let bounded (T : ℝ) : Set (ActiveIndex data x) :=
    {a | poleCoord alpha beta x a.1.1 a.1.2 ∈ Set.Icc (-T) T}
  have hboundedFinite : (bounded R).Finite := by
    let pole : ActiveIndex data x → ℝ := fun a =>
      poleCoord alpha beta x a.1.1 a.1.2
    have hmaps : Set.MapsTo pole (bounded R)
        (realPoleSet data x ∩ Set.Icc (-R) R) := by
      intro a ha
      exact ⟨⟨a, rfl⟩, ha⟩
    have hinj : Set.InjOn pole (bounded R) := by
      intro a _ b _ hab
      apply Subtype.ext
      exact poleCoord_injective alpha hAlpha beta hbeta0 x hab
    exact Set.Finite.of_injOn hmaps hinj
      (finite_realPoleSet_inter_Icc data x point.analytic R (by linarith))
  have hboundedCard : (bounded R).ncard = realPoleCount data x R := by
    unfold realPoleCount
    let pole : ActiveIndex data x → ℝ := fun a =>
      poleCoord alpha beta x a.1.1 a.1.2
    apply Set.ncard_congr (fun a _ => pole a)
    · intro a ha
      exact ⟨⟨a, rfl⟩, ha⟩
    · intro a b _ _ hab
      apply Subtype.ext
      exact poleCoord_injective alpha hAlpha beta hbeta0 x hab
    · intro p hp
      rcases hp.1 with ⟨a, rfl⟩
      exact ⟨a, hp.2, rfl⟩
  have hlower : activeWindow (R - 2) ⊆ bounded R := by
    intro a ha
    have hq : |(a.1.2 : ℝ)| ≤ R - 2 :=
      (show a.1.2 ∈ integerWindow (R - 2) ↔ _ by
        simp only [integerWindow, Finset.mem_Icc, Int.ceil_le, Int.le_floor,
          abs_le]).mp ha
    have hpq :=
      abs_poleCoord_sub_q_lt alpha beta hbetaSmall x a.1.1 a.1.2
    rw [Set.mem_setOf_eq, Set.mem_Icc]
    rw [← abs_le]
    exact (calc
      |poleCoord alpha beta x a.1.1 a.1.2| ≤
          |poleCoord alpha beta x a.1.1 a.1.2 - (a.1.2 : ℝ)| +
            |(a.1.2 : ℝ)| := by
              simpa only [sub_add_cancel] using
                abs_add_le
                  (poleCoord alpha beta x a.1.1 a.1.2 - (a.1.2 : ℝ))
                  (a.1.2 : ℝ)
      _ < 3 / 2 + (R - 2) := add_lt_add_of_lt_of_le hpq hq
      _ ≤ R := by linarith).le
  have hupper : bounded R ⊆ activeWindow (R + 2) := by
    intro a ha
    have hp : |poleCoord alpha beta x a.1.1 a.1.2| ≤ R := by
      rw [abs_le]
      exact ha
    have hpq :=
      abs_poleCoord_sub_q_lt alpha beta hbetaSmall x a.1.1 a.1.2
    have hq : |(a.1.2 : ℝ)| ≤ R + 2 := by
      exact (calc
        |(a.1.2 : ℝ)| ≤
            |(a.1.2 : ℝ) - poleCoord alpha beta x a.1.1 a.1.2| +
              |poleCoord alpha beta x a.1.1 a.1.2| := by
                simpa only [sub_add_cancel] using
                  abs_add_le
                    ((a.1.2 : ℝ) - poleCoord alpha beta x a.1.1 a.1.2)
                    (poleCoord alpha beta x a.1.1 a.1.2)
        _ < 3 / 2 + R :=
          add_lt_add_of_lt_of_le (by simpa [abs_sub_comm] using hpq) hp
        _ ≤ R + 2 := by linarith).le
    exact (show a.1.2 ∈ integerWindow (R + 2) ↔ _ by
      simp only [integerWindow, Finset.mem_Icc, Int.ceil_le, Int.le_floor,
        abs_le]).mpr hq
  constructor
  · simp_rw [hmult]
    norm_cast
    rw [← hwindowCard, ← hboundedCard]
    exact Set.ncard_le_ncard hlower hboundedFinite
  · simp_rw [hmult]
    norm_cast
    rw [← hwindowCard, ← hboundedCard]
    exact Set.ncard_le_ncard hupper (hactiveWindow (R + 2))

/- Proof idea: specialize the count sandwich to integer radii, normalize shifted two-sided sums,
and squeeze using `point.averageTendsto`. -/
theorem realPoleCount_density_nat {alpha : ℝ} {beta : ℚ} {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f) (x : AddCircle (1 : ℝ)) (hAlpha : Irrational alpha) (hbeta0 : beta ≠ 0) (hbetaSmall : |(beta : ℝ)| < 1 / 2) (point : PoleAveragePointData data x) : Tendsto (fun N : ℕ => (realPoleCount data x (N : ℝ) : ℝ) / (2 * (N : ℝ))) atTop (nhds (supportMass data)) := by
  let sum : ℕ → ℝ := fun N =>
    ∑ q ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      multiplicity data
        (x - ((((q : ℤ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ)))
  let avg : ℕ → ℝ := fun N => (2 * (N : ℝ) + 1)⁻¹ * sum N
  have havg : Tendsto avg atTop (nhds (supportMass data)) :=
    point.averageTendsto
  have hsubTop : Tendsto (fun N : ℕ => N - 2) atTop atTop := by
    apply tendsto_atTop.2
    intro M
    filter_upwards [eventually_ge_atTop (M + 2)] with N hN
    omega
  have haddTop : Tendsto (fun N : ℕ => N + 2) atTop atTop :=
    tendsto_add_atTop_nat 2
  have hinv : Tendsto (fun N : ℕ => ((N : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_nhds_zero_nat
  let lowerRatio : ℕ → ℝ := fun N =>
    (2 * ((N - 2 : ℕ) : ℝ) + 1) / (2 * (N : ℝ))
  let upperRatio : ℕ → ℝ := fun N =>
    (2 * ((N + 2 : ℕ) : ℝ) + 1) / (2 * (N : ℝ))
  have hlowerRatio : Tendsto lowerRatio atTop (nhds 1) := by
    have hlim : Tendsto
        (fun N : ℕ => 1 - (3 / 2 : ℝ) * ((N : ℝ))⁻¹)
        atTop (nhds 1) := by
      simpa using tendsto_const_nhds.sub (tendsto_const_nhds.mul hinv)
    apply hlim.congr'
    filter_upwards [eventually_ge_atTop 2] with N hN
    simp only [lowerRatio]
    have hN0 : (N : ℝ) ≠ 0 := by positivity
    rw [Nat.cast_sub hN]
    norm_num only [Nat.cast_ofNat]
    field_simp
    ring
  have hupperRatio : Tendsto upperRatio atTop (nhds 1) := by
    have hlim : Tendsto
        (fun N : ℕ => 1 + (5 / 2 : ℝ) * ((N : ℝ))⁻¹)
        atTop (nhds 1) := by
      simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul hinv)
    apply hlim.congr'
    filter_upwards [eventually_gt_atTop 0] with N hN
    simp only [upperRatio]
    have hN0 : (N : ℝ) ≠ 0 := by positivity
    norm_num only [Nat.cast_add, Nat.cast_ofNat]
    field_simp
    ring
  let lower : ℕ → ℝ := fun N => lowerRatio N * avg (N - 2)
  let upper : ℕ → ℝ := fun N => upperRatio N * avg (N + 2)
  have hlower : Tendsto lower atTop (nhds (supportMass data)) := by
    simpa [lower] using hlowerRatio.mul (havg.comp hsubTop)
  have hupper : Tendsto upper atTop (nhds (supportMass data)) := by
    simpa [upper] using hupperRatio.mul (havg.comp haddTop)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · filter_upwards [eventually_ge_atTop 3] with N hN
    have hR : 2 < (N : ℝ) := by exact_mod_cast hN
    have hsand := (realPoleCount_sandwich data x hAlpha hbeta0 hbetaSmall
      point (N : ℝ) hR).1
    have hiw : integerWindow ((N : ℝ) - 2) =
        Finset.Icc (-((N - 2 : ℕ) : ℤ)) ((N - 2 : ℕ) : ℤ) := by
      have hN2 : 2 ≤ N := by omega
      have hNm : (N : ℝ) - 2 = ((N - 2 : ℕ) : ℝ) := by
        rw [Nat.cast_sub hN2]
        norm_num
      ext q
      simp only [integerWindow, Finset.mem_Icc, Int.ceil_le, Int.le_floor]
      rw [hNm]
      norm_cast
    rw [hiw] at hsand
    have hden : (2 * (N : ℝ)) ≠ 0 := by positivity
    have hfactor : lower N =
        (∑ q ∈ Finset.Icc (-((N - 2 : ℕ) : ℤ)) ((N - 2 : ℕ) : ℤ),
          multiplicity data
            (x - ((((q : ℤ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ)))) /
          (2 * (N : ℝ)) := by
      simp only [lower, lowerRatio, avg, sum]
      have hm : (2 * ((N - 2 : ℕ) : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      apply Finset.sum_congr rfl
      intro q hq
      congr 3
      ring
    rw [hfactor]
    exact div_le_div_of_nonneg_right hsand (by positivity)
  · filter_upwards [eventually_ge_atTop 3] with N hN
    have hR : 2 < (N : ℝ) := by exact_mod_cast hN
    have hsand := (realPoleCount_sandwich data x hAlpha hbeta0 hbetaSmall
      point (N : ℝ) hR).2
    have hiw : integerWindow ((N : ℝ) + 2) =
        Finset.Icc (-((N + 2 : ℕ) : ℤ)) ((N + 2 : ℕ) : ℤ) := by
      ext q
      simp only [integerWindow, Finset.mem_Icc, Int.ceil_le, Int.le_floor]
      norm_num only [Nat.cast_add, Nat.cast_ofNat]
      norm_cast
    rw [hiw] at hsand
    have hden : (2 * (N : ℝ)) ≠ 0 := by positivity
    have hfactor :
        (∑ q ∈ Finset.Icc (-((N + 2 : ℕ) : ℤ)) ((N + 2 : ℕ) : ℤ),
          multiplicity data
            (x - ((((q : ℤ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ)))) /
          (2 * (N : ℝ)) = upper N := by
      simp only [upper, upperRatio, avg, sum]
      have hm : (2 * ((N + 2 : ℕ) : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      apply Finset.sum_congr rfl
      intro q hq
      congr 3
      ring
    rw [← hfactor]
    exact div_le_div_of_nonneg_right hsand (by positivity)

/- Proof idea: sandwich every large real radius between neighboring natural radii and use
monotonicity plus the floor/ceiling ratios tending to one. -/
theorem realPoleCount_density {alpha : ℝ} {beta : ℚ} {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f) (x : AddCircle (1 : ℝ)) (hAlpha : Irrational alpha) (hbeta0 : beta ≠ 0) (hbetaSmall : |(beta : ℝ)| < 1 / 2) (point : PoleAveragePointData data x) : Tendsto (fun R : ℝ => (realPoleCount data x R : ℝ) / (2 * R)) atTop (nhds (supportMass data)) := by
  have hnat :=
    realPoleCount_density_nat data x hAlpha hbeta0 hbetaSmall point
  let natNorm : ℕ → ℝ := fun N =>
    (realPoleCount data x (N : ℝ) : ℝ) / (2 * (N : ℝ))
  have hnat' : Tendsto natNorm atTop (nhds (supportMass data)) := hnat
  let lower : ℝ → ℝ := fun R => natNorm ⌊R⌋₊ * ((⌊R⌋₊ : ℝ) / R)
  let upper : ℝ → ℝ := fun R => natNorm ⌈R⌉₊ * ((⌈R⌉₊ : ℝ) / R)
  have hlower : Tendsto lower atTop (nhds (supportMass data)) := by
    simpa [lower] using
      (hnat'.comp (tendsto_nat_floor_atTop :
        Tendsto (fun R : ℝ => ⌊R⌋₊) atTop atTop)).mul
        (tendsto_nat_floor_div_atTop :
          Tendsto (fun R : ℝ => (⌊R⌋₊ : ℝ) / R) atTop (nhds 1))
  have hupper : Tendsto upper atTop (nhds (supportMass data)) := by
    simpa [upper] using
      (hnat'.comp (tendsto_nat_ceil_atTop :
        Tendsto (fun R : ℝ => ⌈R⌉₊) atTop atTop)).mul
        (tendsto_nat_ceil_div_atTop :
          Tendsto (fun R : ℝ => (⌈R⌉₊ : ℝ) / R) atTop (nhds 1))
  have hcountMono {r t : ℝ} (hr : 0 ≤ r) (hrt : r ≤ t) :
      realPoleCount data x r ≤ realPoleCount data x t := by
    unfold realPoleCount
    apply Set.ncard_le_ncard
    · rintro p ⟨hpPole, hpL, hpU⟩
      exact ⟨hpPole, by constructor <;> linarith⟩
    · exact finite_realPoleSet_inter_Icc data x point.analytic t (hr.trans hrt)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with R hR
    have hR0 : 0 < R := lt_trans zero_lt_one hR
    have hfloorPos : 0 < ⌊R⌋₊ := Nat.floor_pos.mpr hR.le
    have hfloorR : (⌊R⌋₊ : ℝ) ≤ R := Nat.floor_le hR0.le
    have hc : realPoleCount data x (⌊R⌋₊ : ℝ) ≤ realPoleCount data x R :=
      hcountMono (Nat.cast_nonneg _) hfloorR
    have heq : lower R =
        (realPoleCount data x (⌊R⌋₊ : ℝ) : ℝ) / (2 * R) := by
      simp only [lower, natNorm]
      have hf : (⌊R⌋₊ : ℝ) ≠ 0 := by positivity
      field_simp
    rw [heq]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hc) (by positivity)
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with R hR
    have hR0 : 0 < R := lt_trans zero_lt_one hR
    have hceilPos : 0 < ⌈R⌉₊ := Nat.ceil_pos.mpr hR0
    have hRceil : R ≤ (⌈R⌉₊ : ℝ) := Nat.le_ceil R
    have hc : realPoleCount data x R ≤ realPoleCount data x (⌈R⌉₊ : ℝ) :=
      hcountMono hR0.le hRceil
    have heq :
        (realPoleCount data x (⌈R⌉₊ : ℝ) : ℝ) / (2 * R) = upper R := by
      simp only [upper, natNorm]
      have hf : (⌈R⌉₊ : ℝ) ≠ 0 := by positivity
      field_simp
    rw [← heq]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hc) (by positivity)

/- Proof idea: take the `ncard` of the embedded complex pole set inside the open metric ball. -/
def complexOpenPoleCount {alpha : ℝ} {beta : ℚ} {S : Set ℝ} {f : ℝ → ℂ}
    (data : PositiveInputData alpha beta S f) (x : AddCircle (1 : ℝ)) (R : ℝ) : ℕ :=
  (complexPoleSet data x ∩ Metric.ball 0 R).ncard

/- Proof idea: restrict the injective `Complex.ofReal` image correspondence to the real open
interval and complex open disk, then apply finite-set `ncard` congruence. -/
theorem complexOpenPoleCount_eq_realOpen {alpha : ℝ} {beta : ℚ} {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f) (x : AddCircle (1 : ℝ)) (hx : AnalyticParameter data x) (R : ℝ) (hR : 0 < R) : complexOpenPoleCount data x R = (realPoleSet data x ∩ Set.Ioo (-R) R).ncard := by
  have hset : complexPoleSet data x ∩ Metric.ball 0 R =
      Complex.ofReal '' (realPoleSet data x ∩ Set.Ioo (-R) R) := by
    ext z
    constructor
    · rintro ⟨⟨p, hp, rfl⟩, hpR⟩
      refine ⟨p, ⟨hp, ?_⟩, rfl⟩
      simpa [Metric.mem_ball, abs_lt] using hpR
    · rintro ⟨p, ⟨hp, hpR⟩, rfl⟩
      refine ⟨⟨p, hp, rfl⟩, ?_⟩
      simpa [Metric.mem_ball, abs_lt] using hpR
  rw [complexOpenPoleCount, hset]
  exact Set.ncard_image_of_injective _ Complex.ofReal_injective

/- Proof idea: identify the complex count with the real open count, observe that the centered
closed and open intervals differ by at most their two endpoints, and subtract in integers. -/
theorem realClosed_complexOpen_count_error_le_two {alpha : ℝ} {beta : ℚ} {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f) (x : AddCircle (1 : ℝ)) (hx : AnalyticParameter data x) (R : ℝ) (hR : 0 < R) : |((realPoleCount data x R : ℕ) : ℤ) - ((complexOpenPoleCount data x R : ℕ) : ℤ)| ≤ 2 := by
  let A : Set ℝ := realPoleSet data x ∩ Set.Icc (-R) R
  let B : Set ℝ := realPoleSet data x ∩ Set.Ioo (-R) R
  have hAfin : A.Finite := by
    exact finite_realPoleSet_inter_Icc data x hx R hR.le
  have hBA : B ⊆ A := by
    rintro p ⟨hpPole, hpL, hpU⟩
    exact ⟨hpPole, hpL.le, hpU.le⟩
  have hBfin : B.Finite := hAfin.subset hBA
  have hBAcard : B.ncard ≤ A.ncard := Set.ncard_le_ncard hBA hAfin
  have hAsub : A ⊆ B ∪ ({-R, R} : Set ℝ) := by
    rintro p ⟨hpPole, hpL, hpU⟩
    by_cases hlow : -R < p
    · by_cases hupp : p < R
      · exact Or.inl ⟨hpPole, hlow, hupp⟩
      · right
        have hpR : p = R := le_antisymm hpU (not_lt.mp hupp)
        simp [hpR]
    · right
      have hpR : p = -R := le_antisymm (not_lt.mp hlow) hpL
      simp [hpR]
  have hAcard : A.ncard ≤ B.ncard + 2 := by
    have hpairCard : ({-R, R} : Set ℝ).ncard ≤ 2 := by
      calc
        ({-R, R} : Set ℝ).ncard ≤ ({R} : Set ℝ).ncard + 1 :=
          Set.ncard_insert_le _ _
        _ = 2 := by simp
    calc
      A.ncard ≤ (B ∪ ({-R, R} : Set ℝ)).ncard :=
        Set.ncard_le_ncard hAsub (hBfin.union (Set.toFinite {-R, R}))
      _ ≤ B.ncard + ({-R, R} : Set ℝ).ncard := Set.ncard_union_le _ _
      _ ≤ B.ncard + 2 := Nat.add_le_add_left hpairCard _
  rw [complexOpenPoleCount_eq_realOpen data x hx R hR]
  change |(A.ncard : ℤ) - (B.ncard : ℤ)| ≤ 2
  rw [abs_of_nonneg (by omega)]
  omega

/- Proof idea: divide the uniform integer count error by `2*R`, show it tends to zero, and
transfer the all-real-radii density limit. -/
theorem complexOpenPoleCount_density {alpha : ℝ} {beta : ℚ} {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f) (x : AddCircle (1 : ℝ)) (hx : AnalyticParameter data x) (hreal : Tendsto (fun R : ℝ => (realPoleCount data x R : ℝ) / (2 * R)) atTop (nhds (supportMass data))) : Tendsto (fun R : ℝ => (complexOpenPoleCount data x R : ℝ) / (2 * R)) atTop (nhds (supportMass data)) := by
  let a : ℝ → ℝ := fun R => (realPoleCount data x R : ℝ) / (2 * R)
  let b : ℝ → ℝ := fun R => (complexOpenPoleCount data x R : ℝ) / (2 * R)
  have hbound : ∀ᶠ R : ℝ in atTop, |b R - a R| ≤ R⁻¹ := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    have herrZ := realClosed_complexOpen_count_error_le_two data x hx R hR
    have herrR : |(realPoleCount data x R : ℝ) -
        (complexOpenPoleCount data x R : ℝ)| ≤ (2 : ℝ) := by
      exact_mod_cast herrZ
    have hden : 0 < 2 * R := mul_pos (by norm_num) hR
    calc
      |b R - a R| =
          |(complexOpenPoleCount data x R : ℝ) -
            (realPoleCount data x R : ℝ)| / (2 * R) := by
        simp only [a, b]
        rw [← sub_div, abs_div, abs_of_pos hden]
      _ ≤ 2 / (2 * R) :=
        div_le_div_of_nonneg_right (by simpa [abs_sub_comm] using herrR) hden.le
      _ = R⁻¹ := by
        field_simp
  have habs : Tendsto (fun R : ℝ => |b R - a R|) atTop (nhds 0) :=
    squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) hbound
      (tendsto_inv_atTop_zero : Tendsto (fun R : ℝ => R⁻¹) atTop (nhds 0))
  have hdiff : Tendsto (fun R : ℝ => b R - a R) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa [Real.norm_eq_abs] using habs
  have ha : Tendsto a atTop (nhds (supportMass data)) := hreal
  simpa [a, b, sub_add_cancel] using ha.add hdiff

/- Proof idea: store the Fourier-good certificate, simultaneous orbit finiteness, and the
all-real-radii real pole-density limit at one fixed parameter. -/
structure PoleGoodParameter {alpha : ℝ} {beta : ℚ} {S : Set ℝ} {f : ℝ → ℂ}
    (data : PositiveInputData alpha beta S f) (x : AddCircle (1 : ℝ)) : Prop where
  fourierGood : FourierGoodParameter data x
  orbitFinite : ∀ q : ℤ,
    multiplicityENN data
      (x - ((((q : ℤ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ))) < ∞
  poleDensity : Tendsto
    (fun R : ℝ => (realPoleCount data x R : ℝ) / (2 * R))
    atTop (nhds (supportMass data))

/- Proof idea: intersect the Fourier-good, Birkhoff-average, and all-orbit-finite conull sets;
construct `PoleAveragePointData`, derive real pole density, and fill `PoleGoodParameter`. -/
theorem poleGoodParameter_ae {alpha : ℝ} {beta : ℚ} {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f) (hAlpha : Irrational alpha) (hbeta0 : beta ≠ 0) (hbetaSmall : |(beta : ℝ)| < 1 / 2) (hSlt : volume S < 1) : ∀ᵐ x : AddCircle (1 : ℝ) ∂AddCircle.haarAddCircle, PoleGoodParameter data x := by
  filter_upwards [fourierGoodParameter_ae data hbeta0 hbetaSmall hSlt,
    multiplicity_twoSided_average_ae data hAlpha hSlt,
    multiplicity_all_orbit_finite_ae data hSlt] with x hxFourier hxAverage hxFinite
  let point : PoleAveragePointData data x :=
    { analytic := hxFourier.analytic
      orbitFinite := hxFinite
      averageTendsto := hxAverage }
  exact
    { fourierGood := hxFourier
      orbitFinite := hxFinite
      poleDensity := realPoleCount_density data x hAlpha hbeta0 hbetaSmall point }

end Theorem12.Internal
