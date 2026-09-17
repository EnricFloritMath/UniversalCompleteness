import UniversalCompletenessHD.Summability
import Theorem12.GenericAuxiliary
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Topology.Algebra.InfiniteSum.UniformOn

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace UniversalCompletenessHD.Internal

/- Proof idea: express the bounded real-pole set as the image of the finite active-index
set supplied by `finite_activePole_IccHD`.  Finiteness precedes every later use of `Set.ncard`. -/
theorem finite_realPoleSetHD_inter_Icc {d : Nat} {alpha beta : RealVec d}
    {S : Set (RealVec d)} {f : RealVec d → Complex}
    (data : PositiveInputDataHD alpha beta S f) (x : Torus d)
    (hx : AnalyticParameterHD data x) (R : Real) (hR : 0 ≤ R) :
    Set.Finite (realPoleSetHD data x ∩ Set.Icc (-R) R) := by
  refine
    (finite_activePole_IccHD data alpha beta x hx.poleWeightFinite R hR).image
      (fun a : IntVec d × Int ↦ poleCoordHD alpha beta x a.1 a.2) |>.subset ?_
  rintro y ⟨⟨a, rfl⟩, haIcc⟩
  exact ⟨a.1, ⟨a.2, haIcc⟩, rfl⟩

/- Proof idea: transport `finite_realPoleSetHD_inter_Icc` through `Complex.ofReal`, using
`Complex.norm_real` to identify the real interval with the complex closed ball. -/
theorem finite_complexPoleSetHD_inter_closedBall {d : Nat} {alpha beta : RealVec d}
    {S : Set (RealVec d)} {f : RealVec d → Complex}
    (data : PositiveInputDataHD alpha beta S f) (x : Torus d)
    (hx : AnalyticParameterHD data x) (R : Real) (hR : 0 ≤ R) :
    Set.Finite (complexPoleSetHD data x ∩ Metric.closedBall 0 R) := by
  refine
    (finite_realPoleSetHD_inter_Icc data x hx R hR).image Complex.ofReal |>.subset ?_
  rintro z ⟨⟨p, hp, rfl⟩, hpR⟩
  refine ⟨p, ⟨hp, ?_⟩, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_real] at hpR
  exact abs_le.mp hpR

/- Proof idea: bound the compact set, use the regularized-kernel quadratic estimate for
large real poles, and isolate the finitely many remaining active indices. -/
theorem activeTerm_compact_majorantHD {d : Nat} {alpha beta : RealVec d}
    {S : Set (RealVec d)} {f : RealVec d → Complex}
    (data : PositiveInputDataHD alpha beta S f) (x : Torus d)
    (hx : AnalyticParameterHD data x) (K : Set Complex)
    (hKcompact : IsCompact K) (hK : Disjoint K (complexPoleSetHD data x)) :
    ∃ CK : Real, 0 ≤ CK ∧ ∃ A0 : Set (ActiveIndexHD data x), A0.Finite ∧
      ∀ a : ActiveIndexHD data x, a ∉ A0 → ∀ z ∈ K,
        ‖activeTermHD data x a z‖ ≤
          CK * ‖residueCoordHD data alpha beta x a.1.1 a.1.2‖ /
            (1 + (poleCoordHD alpha beta x a.1.1 a.1.2) ^ 2) := by
  classical
  obtain ⟨C, hCpos, hC⟩ := hKcompact.isBounded.exists_pos_norm_le
  let B : Real := 2 * C + 1
  let A0 : Set (ActiveIndexHD data x) :=
    {a | |poleCoordHD alpha beta x a.1.1 a.1.2| ≤ B}
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hpairFinite := finite_activePole_IccHD data alpha beta x
    hx.poleWeightFinite B hB
  have hA0 : A0.Finite := by
    refine (hpairFinite.preimage Subtype.val_injective.injOn).subset ?_
    intro a ha
    exact ⟨a.2, abs_le.mp ha⟩
  refine ⟨4 * C, by positivity, A0, hA0, ?_⟩
  intro a ha z hz
  let p : Real := poleCoordHD alpha beta x a.1.1 a.1.2
  have hpLarge : B < |p| := lt_of_not_ge ha
  have hBpos : 0 < B := by
    dsimp [B]
    positivity
  have hpAbsPos : 0 < |p| := lt_trans hBpos hpLarge
  have hp0 : p ≠ 0 := abs_pos.mp hpAbsPos
  have hzNorm : ‖z‖ ≤ C := hC z hz
  have hpzLower : |p| - ‖z‖ ≤ ‖z - (p : Complex)‖ := by
    simpa [Complex.norm_real, norm_sub_rev] using norm_sub_norm_le (p : Complex) z
  have hpHalf : |p| / 2 ≤ ‖z - (p : Complex)‖ := by
    dsimp [B] at hpLarge
    nlinarith
  have hdistPos : 0 < ‖z - (p : Complex)‖ :=
    lt_of_lt_of_le (half_pos hpAbsPos) hpHalf
  have hzp : z - (p : Complex) ≠ 0 := norm_ne_zero_iff.mp hdistPos.ne'
  have hk : regularizedKernelHD p z =
      z / ((p : Complex) * (z - (p : Complex))) := by
    unfold regularizedKernelHD
    field_simp [hp0, hzp]
    ring
  rw [activeTermHD]
  change ‖residueCoordHD data alpha beta x a.1.1 a.1.2 *
      regularizedKernelHD p z‖ ≤ _
  rw [hk, norm_mul, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  change
    ‖residueCoordHD data alpha beta x a.1.1 a.1.2‖ *
        (‖z‖ / (|p| * ‖z - (p : Complex)‖)) ≤
      4 * C * ‖residueCoordHD data alpha beta x a.1.1 a.1.2‖ /
        (1 + p ^ 2)
  by_cases hr : ‖residueCoordHD data alpha beta x a.1.1 a.1.2‖ = 0
  · simp [hr]
  rw [mul_comm (4 * C), mul_div_assoc]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  rw [div_le_iff₀ (mul_pos hpAbsPos hdistPos)]
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : 0 < 1 + p ^ 2)]
  have hpOne : 1 < |p| := by
    dsimp [B] at hpLarge
    nlinarith
  have hpSq : p ^ 2 = |p| ^ 2 := by rw [sq_abs]
  rw [hpSq]
  have hleft : ‖z‖ * (1 + |p| ^ 2) ≤ C * (1 + |p| ^ 2) :=
    mul_le_mul_of_nonneg_right hzNorm (by positivity)
  have hone : 1 + |p| ^ 2 ≤ 2 * |p| ^ 2 := by
    nlinarith [sq_nonneg (|p| - 1)]
  have hmid : C * (1 + |p| ^ 2) ≤ C * (2 * |p| ^ 2) :=
    mul_le_mul_of_nonneg_left hone hCpos.le
  have hright : C * (2 * |p| ^ 2) ≤
      4 * C * (|p| * ‖z - (p : Complex)‖) := by
    have hmul := mul_le_mul_of_nonneg_left hpHalf
      (show 0 ≤ 4 * C * |p| by positivity)
    nlinarith
  exact hleft.trans (hmid.trans hright)

private theorem exists_cofinite_activeTerm_bound_on_compactHD {d : Nat}
    {alpha beta : RealVec d} {S : Set (RealVec d)} {f : RealVec d → Complex}
    (data : PositiveInputDataHD alpha beta S f) (x : Torus d)
    (hx : AnalyticParameterHD data x) (K : Set Complex)
    (hKcompact : IsCompact K) :
    ∃ CK : Real, 0 ≤ CK ∧ ∃ A0 : Set (ActiveIndexHD data x), A0.Finite ∧
      ∀ a : ActiveIndexHD data x, a ∉ A0 → ∀ z ∈ K,
        ‖activeTermHD data x a z‖ ≤
          CK * ‖residueCoordHD data alpha beta x a.1.1 a.1.2‖ /
            (1 + (poleCoordHD alpha beta x a.1.1 a.1.2) ^ 2) := by
  classical
  obtain ⟨C, hCpos, hC⟩ := hKcompact.isBounded.exists_pos_norm_le
  let B : Real := 2 * C + 1
  let A0 : Set (ActiveIndexHD data x) :=
    {a | |poleCoordHD alpha beta x a.1.1 a.1.2| ≤ B}
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hpairFinite := finite_activePole_IccHD data alpha beta x
    hx.poleWeightFinite B hB
  have hA0 : A0.Finite := by
    refine (hpairFinite.preimage Subtype.val_injective.injOn).subset ?_
    intro a ha
    exact ⟨a.2, abs_le.mp ha⟩
  refine ⟨4 * C, by positivity, A0, hA0, ?_⟩
  intro a ha z hz
  let p : Real := poleCoordHD alpha beta x a.1.1 a.1.2
  have hpLarge : B < |p| := lt_of_not_ge ha
  have hBpos : 0 < B := by
    dsimp [B]
    positivity
  have hpAbsPos : 0 < |p| := lt_trans hBpos hpLarge
  have hp0 : p ≠ 0 := abs_pos.mp hpAbsPos
  have hzNorm : ‖z‖ ≤ C := hC z hz
  have hpzLower : |p| - ‖z‖ ≤ ‖z - (p : Complex)‖ := by
    simpa [Complex.norm_real, norm_sub_rev] using norm_sub_norm_le (p : Complex) z
  have hpHalf : |p| / 2 ≤ ‖z - (p : Complex)‖ := by
    dsimp [B] at hpLarge
    nlinarith
  have hdistPos : 0 < ‖z - (p : Complex)‖ :=
    lt_of_lt_of_le (half_pos hpAbsPos) hpHalf
  have hzp : z - (p : Complex) ≠ 0 := norm_ne_zero_iff.mp hdistPos.ne'
  have hk : regularizedKernelHD p z =
      z / ((p : Complex) * (z - (p : Complex))) := by
    unfold regularizedKernelHD
    field_simp [hp0, hzp]
    ring
  rw [activeTermHD]
  change ‖residueCoordHD data alpha beta x a.1.1 a.1.2 *
      regularizedKernelHD p z‖ ≤ _
  rw [hk, norm_mul, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  change
    ‖residueCoordHD data alpha beta x a.1.1 a.1.2‖ *
        (‖z‖ / (|p| * ‖z - (p : Complex)‖)) ≤
      4 * C * ‖residueCoordHD data alpha beta x a.1.1 a.1.2‖ /
        (1 + p ^ 2)
  by_cases hr : ‖residueCoordHD data alpha beta x a.1.1 a.1.2‖ = 0
  · simp [hr]
  rw [mul_comm (4 * C), mul_div_assoc]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  rw [div_le_iff₀ (mul_pos hpAbsPos hdistPos)]
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : 0 < 1 + p ^ 2)]
  have hpOne : 1 < |p| := by
    dsimp [B] at hpLarge
    nlinarith
  have hpSq : p ^ 2 = |p| ^ 2 := by rw [sq_abs]
  rw [hpSq]
  have hleft : ‖z‖ * (1 + |p| ^ 2) ≤ C * (1 + |p| ^ 2) :=
    mul_le_mul_of_nonneg_right hzNorm (by positivity)
  have hone : 1 + |p| ^ 2 ≤ 2 * |p| ^ 2 := by
    nlinarith [sq_nonneg (|p| - 1)]
  have hmid : C * (1 + |p| ^ 2) ≤ C * (2 * |p| ^ 2) :=
    mul_le_mul_of_nonneg_left hone hCpos.le
  have hright : C * (2 * |p| ^ 2) ≤
      4 * C * (|p| * ‖z - (p : Complex)‖) := by
    have hmul := mul_le_mul_of_nonneg_left hpHalf
      (show 0 ≤ 4 * C * |p| by positivity)
    nlinarith
  exact hleft.trans (hmid.trans hright)

private theorem analyticAt_activeTermHD_of_ne_pole {d : Nat}
    {alpha beta : RealVec d} {S : Set (RealVec d)} {f : RealVec d → Complex}
    (data : PositiveInputDataHD alpha beta S f) (x : Torus d)
    (a : ActiveIndexHD data x) {z : Complex}
    (hz : z ≠ (poleCoordHD alpha beta x a.1.1 a.1.2 : Complex)) :
    AnalyticAt Complex (activeTermHD data x a) z := by
  change AnalyticAt Complex
    (fun w => residueCoordHD data alpha beta x a.1.1 a.1.2 *
      (1 / (w - (poleCoordHD alpha beta x a.1.1 a.1.2 : Complex)) +
        1 / (poleCoordHD alpha beta x a.1.1 a.1.2 : Complex))) z
  exact analyticAt_const.mul <|
    (analyticAt_const.div (analyticAt_id.sub analyticAt_const)
      (sub_ne_zero.mpr hz)).add analyticAt_const

private theorem isClosed_complexPoleSetHD {d : Nat} {alpha beta : RealVec d}
    {S : Set (RealVec d)} {f : RealVec d → Complex}
    (data : PositiveInputDataHD alpha beta S f) (x : Torus d)
    (hx : AnalyticParameterHD data x) : IsClosed (complexPoleSetHD data x) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro z hz
  let R : Real := ‖z‖ + 1
  have hR : 0 ≤ R := by
    dsimp [R]
    positivity
  have hzball : z ∈ Metric.ball (0 : Complex) R := by
    simp [Metric.mem_ball, R]
  let P : Set Complex := complexPoleSetHD data x ∩ Metric.closedBall 0 R
  have hPfinite : P.Finite := finite_complexPoleSetHD_inter_closedBall data x hx R hR
  have hzP : z ∉ P := fun hzP => hz hzP.1
  have hopen : IsOpen (Metric.ball (0 : Complex) R \ P) :=
    IsOpen.sdiff Metric.isOpen_ball hPfinite.isClosed
  refine mem_of_superset (hopen.mem_nhds ⟨hzball, hzP⟩) ?_
  intro w hw
  rw [Set.mem_compl_iff]
  intro hwPole
  exact hw.2 ⟨hwPole, Metric.ball_subset_closedBall hw.1⟩

private theorem analyticAt_sq_mul_activeTermHD_at_pole {d : Nat}
    {alpha beta : RealVec d} {S : Set (RealVec d)} {f : RealVec d → Complex}
    (data : PositiveInputDataHD alpha beta S f) (x : Torus d)
    (hx : AnalyticParameterHD data x)
    (a : ActiveIndexHD data x) :
    AnalyticAt Complex
      (fun w => (w - (poleCoordHD alpha beta x a.1.1 a.1.2 : Complex)) ^ 2 *
        activeTermHD data x a w)
      (poleCoordHD alpha beta x a.1.1 a.1.2 : Complex) := by
  let p : Real := poleCoordHD alpha beta x a.1.1 a.1.2
  let r : Complex := residueCoordHD data alpha beta x a.1.1 a.1.2
  have hp0 : p ≠ 0 := by
    dsimp [p]
    simpa using poleCoordHD_not_int_of_not_sineBad alpha beta x hx.offBad
      a.1.1 a.1.2 0
  have heq :
      (fun w : Complex => (w - (p : Complex)) ^ 2 * activeTermHD data x a w) =
        (fun w : Complex =>
          r * ((w - (p : Complex)) + (w - (p : Complex)) ^ 2 / (p : Complex))) := by
    funext w
    by_cases hwp : w = (p : Complex)
    · subst w
      simp [activeTermHD, regularizedKernelHD, p, r]
    · rw [activeTermHD, regularizedKernelHD]
      change (w - (p : Complex)) ^ 2 *
          (r * (1 / (w - (p : Complex)) + 1 / (p : Complex))) = _
      have hsub : w - (p : Complex) ≠ 0 := sub_ne_zero.mpr hwp
      field_simp [hp0, hsub]
  rw [heq]
  fun_prop

/- Proof idea: apply the Weierstrass M-test to the cofinite majorized tail and add the
finite analytic head; identify the resulting pointwise sum with `activeMHD`. -/
theorem hasSum_activeM_locallyUniformlyHD {d : Nat} {alpha beta : RealVec d}
    {S : Set (RealVec d)} {f : RealVec d → Complex}
    (data : PositiveInputDataHD alpha beta S f) (x : Torus d)
    (hx : AnalyticParameterHD data x) (K : Set Complex)
    (hKcompact : IsCompact K) (hK : Disjoint K (complexPoleSetHD data x)) :
    HasSumUniformlyOn (fun a : ActiveIndexHD data x => activeTermHD data x a)
      (activeMHD data x) K := by
  classical
  rcases activeTerm_compact_majorantHD data x hx K hKcompact hK with
    ⟨CK, hCK, A0, hA0, htail⟩
  have hweight : Summable (fun a : ActiveIndexHD data x =>
      ‖residueCoordHD data alpha beta x a.1.1 a.1.2‖ /
        (1 + (poleCoordHD alpha beta x a.1.1 a.1.2) ^ 2)) := by
    change Summable
      ((fun a : IntVec d × Int => ‖residueCoordHD data alpha beta x a.1 a.2‖ /
        (1 + (poleCoordHD alpha beta x a.1 a.2) ^ 2)) ∘ Subtype.val)
    exact (summable_residue_weightHD data alpha beta x hx.poleWeightFinite).subtype _
  have hmajorant := hweight.mul_left CK
  rw [hasSumUniformlyOn_iff_tendstoUniformlyOn]
  change TendstoUniformlyOn
    (fun t : Finset (ActiveIndexHD data x) => fun z =>
      ∑ a ∈ t, activeTermHD data x a z)
    (fun z => ∑' a : ActiveIndexHD data x, activeTermHD data x a z) atTop K
  exact tendstoUniformlyOn_tsum_of_cofinite_eventually hmajorant
      (show ∀ᶠ a : ActiveIndexHD data x in cofinite, ∀ z ∈ K,
          ‖activeTermHD data x a z‖ ≤
            CK * (‖residueCoordHD data alpha beta x a.1.1 a.1.2‖ /
              (1 + (poleCoordHD alpha beta x a.1.1 a.1.2) ^ 2)) by
        filter_upwards [hA0.compl_mem_cofinite] with a ha z hz
        simpa [mul_div_assoc] using htail a ha z hz)

/- Proof idea: use the locally uniform analytic limit on compact neighbourhoods contained
in the complement of the locally finite complex pole set. -/
theorem analyticOn_activeM_compl_polesHD {d : Nat} {alpha beta : RealVec d}
    {S : Set (RealVec d)} {f : RealVec d → Complex}
    (data : PositiveInputDataHD alpha beta S f) (x : Torus d)
    (hx : AnalyticParameterHD data x) :
    AnalyticOn Complex (activeMHD data x) (Set.univ \ complexPoleSetHD data x) := by
  classical
  have hanTerm (a : ActiveIndexHD data x) {z : Complex}
      (hz : z ≠ (poleCoordHD alpha beta x a.1.1 a.1.2 : Complex)) :
      AnalyticAt Complex (activeTermHD data x a) z := by
    have hp0 : poleCoordHD alpha beta x a.1.1 a.1.2 ≠ 0 := by
      simpa using poleCoordHD_not_int_of_not_sineBad alpha beta x hx.offBad
        a.1.1 a.1.2 0
    change AnalyticAt Complex
      (fun w => residueCoordHD data alpha beta x a.1.1 a.1.2 *
        (1 / (w - (poleCoordHD alpha beta x a.1.1 a.1.2 : Complex)) +
          1 / (poleCoordHD alpha beta x a.1.1 a.1.2 : Complex))) z
    exact analyticAt_const.mul <|
      (analyticAt_const.div (analyticAt_id.sub analyticAt_const)
        (sub_ne_zero.mpr hz)).add analyticAt_const
  have hclosed : IsClosed (complexPoleSetHD data x) := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro z hz
    let R : Real := ‖z‖ + 1
    have hR : 0 ≤ R := by
      dsimp [R]
      positivity
    have hzball : z ∈ Metric.ball (0 : Complex) R := by
      simp [Metric.mem_ball, R]
    let P : Set Complex := complexPoleSetHD data x ∩ Metric.closedBall 0 R
    have hPfinite : P.Finite := finite_complexPoleSetHD_inter_closedBall data x hx R hR
    have hzP : z ∉ P := fun hzP => hz hzP.1
    have hopen : IsOpen (Metric.ball (0 : Complex) R \ P) :=
      IsOpen.sdiff Metric.isOpen_ball hPfinite.isClosed
    refine mem_of_superset (hopen.mem_nhds ⟨hzball, hzP⟩) ?_
    intro w hw
    rw [Set.mem_compl_iff]
    intro hwPole
    exact hw.2 ⟨hwPole, Metric.ball_subset_closedBall hw.1⟩
  intro z hz
  have hzcompl : z ∈ (complexPoleSetHD data x)ᶜ := hz.2
  obtain ⟨K, ⟨hzK, hKcompact⟩, hKsub⟩ :=
    (compact_basis_nhds z).mem_iff.mp (hclosed.isOpen_compl.mem_nhds hzcompl)
  have hKdisj : Disjoint K (complexPoleSetHD data x) :=
    Set.disjoint_left.2 fun w hwK hwP => (hKsub hwK) hwP
  have hconv :=
    (hasSum_activeM_locallyUniformlyHD data x hx K hKcompact hKdisj).tendstoUniformlyOn
  have hlocal : TendstoLocallyUniformlyOn
      (fun t : Finset (ActiveIndexHD data x) => fun w =>
        ∑ a ∈ t, activeTermHD data x a w)
      (activeMHD data x) atTop (interior K) :=
    hconv.tendstoLocallyUniformlyOn.mono interior_subset
  have hpartials : ∀ᶠ t : Finset (ActiveIndexHD data x) in atTop,
      DifferentiableOn Complex (fun w => ∑ a ∈ t, activeTermHD data x a w)
        (interior K) := by
    filter_upwards [] with t
    exact DifferentiableOn.fun_sum fun a _ w hw =>
      (hanTerm a <| by
        intro hwp
        have hpMem : (poleCoordHD alpha beta x a.1.1 a.1.2 : Complex) ∈
            complexPoleSetHD data x :=
          ⟨poleCoordHD alpha beta x a.1.1 a.1.2, ⟨a, rfl⟩, rfl⟩
        exact Set.disjoint_left.1 hKdisj (interior_subset hw) (hwp ▸ hpMem)).differentiableAt
        |>.differentiableWithinAt
  have hdiff := hlocal.differentiableOn hpartials isOpen_interior
  have hzInt : z ∈ interior K := mem_of_mem_nhds (interior_mem_nhds.mpr hzK)
  exact ((hdiff.analyticOnNhd isOpen_interior) z hzInt).analyticWithinAt

/- Proof idea: off the pole set use `analyticOn_activeM_compl_polesHD`; at a pole split off the unique active
term and prove the remaining locally uniformly convergent tail analytic. -/
theorem meromorphicOn_activeMHD {d : Nat} {alpha beta : RealVec d}
    {S : Set (RealVec d)} {f : RealVec d → Complex}
    (data : PositiveInputDataHD alpha beta S f) (x : Torus d)
    (hx : AnalyticParameterHD data x) :
    MeromorphicOn (activeMHD data x) Set.univ := by
  classical
  intro z _
  let R : Real := ‖z‖ + 1
  have hR : 0 ≤ R := by
    dsimp [R]
    positivity
  let P : Set Complex := complexPoleSetHD data x ∩ Metric.closedBall 0 R
  have hPfinite : P.Finite := finite_complexPoleSetHD_inter_closedBall data x hx R hR
  let Q : Set Complex := P \ {z}
  have hQfinite : Q.Finite := hPfinite.sdiff
  have hzU : z ∈ Metric.ball (0 : Complex) R \ Q := by
    refine ⟨?_, ?_⟩
    · simp [Metric.mem_ball, R]
    · simp [Q]
  have hUopen : IsOpen (Metric.ball (0 : Complex) R \ Q) :=
    IsOpen.sdiff Metric.isOpen_ball hQfinite.isClosed
  obtain ⟨K, ⟨hzK, hKcompact⟩, hKsub⟩ :=
    (compact_basis_nhds z).mem_iff.mp (hUopen.mem_nhds hzU)
  rcases exists_cofinite_activeTerm_bound_on_compactHD data x hx K hKcompact with
    ⟨CK, hCK, A0, hA0, htail⟩
  obtain ⟨D, hDpos, hD⟩ := hKcompact.isBounded.exists_pos_norm_le
  let E : Real := (D + ‖z‖) ^ 2
  have hE : 0 ≤ E := sq_nonneg _
  have hweight : Summable (fun a : ActiveIndexHD data x =>
      ‖residueCoordHD data alpha beta x a.1.1 a.1.2‖ /
        (1 + (poleCoordHD alpha beta x a.1.1 a.1.2) ^ 2)) := by
    change Summable
      ((fun a : IntVec d × Int => ‖residueCoordHD data alpha beta x a.1 a.2‖ /
        (1 + (poleCoordHD alpha beta x a.1 a.2) ^ 2)) ∘ Subtype.val)
    exact (summable_residue_weightHD data alpha beta x hx.poleWeightFinite).subtype _
  have hmajorant := hweight.mul_left (E * CK)
  have hbound : ∀ᶠ a : ActiveIndexHD data x in cofinite, ∀ w ∈ K,
      ‖(w - z) ^ 2 * activeTermHD data x a w‖ ≤
        (E * CK) *
          (‖residueCoordHD data alpha beta x a.1.1 a.1.2‖ /
            (1 + (poleCoordHD alpha beta x a.1.1 a.1.2) ^ 2)) := by
    filter_upwards [hA0.compl_mem_cofinite] with a ha w hw
    have hwsub : ‖w - z‖ ≤ D + ‖z‖ :=
      (norm_sub_le w z).trans (add_le_add (hD w hw) le_rfl)
    have hpow : ‖w - z‖ ^ 2 ≤ E := by
      dsimp [E]
      exact pow_le_pow_left₀ (norm_nonneg _) hwsub 2
    rw [norm_mul, norm_pow]
    calc
      ‖w - z‖ ^ 2 * ‖activeTermHD data x a w‖
          ≤ E * ‖activeTermHD data x a w‖ :=
        mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
      _ ≤ E * (CK * ‖residueCoordHD data alpha beta x a.1.1 a.1.2‖ /
            (1 + (poleCoordHD alpha beta x a.1.1 a.1.2) ^ 2)) :=
        mul_le_mul_of_nonneg_left (htail a ha w hw) hE
      _ = (E * CK) *
          (‖residueCoordHD data alpha beta x a.1.1 a.1.2‖ /
            (1 + (poleCoordHD alpha beta x a.1.1 a.1.2) ^ 2)) := by ring
  have hconv : TendstoUniformlyOn
      (fun t : Finset (ActiveIndexHD data x) => fun w =>
        ∑ a ∈ t, (w - z) ^ 2 * activeTermHD data x a w)
      (fun w => ∑' a : ActiveIndexHD data x,
        (w - z) ^ 2 * activeTermHD data x a w) atTop K :=
    tendstoUniformlyOn_tsum_of_cofinite_eventually hmajorant hbound
  have hlocal := hconv.tendstoLocallyUniformlyOn.mono interior_subset
  have hpartials : ∀ᶠ t : Finset (ActiveIndexHD data x) in atTop,
      DifferentiableOn Complex
        (fun w => ∑ a ∈ t, (w - z) ^ 2 * activeTermHD data x a w)
        (interior K) := by
    filter_upwards [] with t
    exact DifferentiableOn.fun_sum fun a _ w hw => by
      by_cases hwp : w = (poleCoordHD alpha beta x a.1.1 a.1.2 : Complex)
      · have hpMem : w ∈ complexPoleSetHD data x := by
          rw [hwp]
          exact ⟨poleCoordHD alpha beta x a.1.1 a.1.2, ⟨a, rfl⟩, rfl⟩
        have hwU := hKsub (interior_subset hw)
        have hpz : w = z := by
          by_contra hwz
          exact hwU.2 ⟨⟨hpMem, Metric.ball_subset_closedBall hwU.1⟩, hwz⟩
        have hcenter : z = (poleCoordHD alpha beta x a.1.1 a.1.2 : Complex) :=
          hpz.symm.trans hwp
        simpa [hcenter, hwp] using
          (analyticAt_sq_mul_activeTermHD_at_pole data x hx a).differentiableAt
            |>.differentiableWithinAt
      · exact (((analyticAt_id.sub analyticAt_const).pow 2).mul
          (analyticAt_activeTermHD_of_ne_pole data x a hwp)).differentiableAt
          |>.differentiableWithinAt
  have hdiff := hlocal.differentiableOn hpartials isOpen_interior
  have hzInt : z ∈ interior K := mem_of_mem_nhds (interior_mem_nhds.mpr hzK)
  have hanalyticTsum : AnalyticAt Complex
      (fun w => ∑' a : ActiveIndexHD data x,
        (w - z) ^ 2 * activeTermHD data x a w) z :=
    (hdiff.analyticOnNhd isOpen_interior) z hzInt
  refine ⟨2, ?_⟩
  change AnalyticAt Complex (fun w => (w - z) ^ 2 * activeMHD data x w) z
  convert hanalyticTsum using 1
  funext w
  simp only [activeMHD, tsum_mul_left]

/- Proof idea: every active pole is nonzero away from `sineBadHD`, so each regularized
kernel vanishes at the origin; pass the equality through the summable series. -/
theorem activeMHD_zero {d : Nat} {alpha beta : RealVec d}
    {S : Set (RealVec d)} {f : RealVec d → Complex}
    (data : PositiveInputDataHD alpha beta S f) (x : Torus d)
    (hx : AnalyticParameterHD data x) :
    activeMHD data x 0 = 0 := by
  have hterm (a : ActiveIndexHD data x) : activeTermHD data x a 0 = 0 := by
    have hp0 : poleCoordHD alpha beta x a.1.1 a.1.2 ≠ 0 := by
      simpa using poleCoordHD_not_int_of_not_sineBad alpha beta x hx.offBad
        a.1.1 a.1.2 0
    simp [activeTermHD, regularizedKernelHD, hp0]
  rw [activeMHD]
  simp_rw [hterm]
  exact tsum_zero

/- Proof idea: isolate the unique active term and port the proved punctured-neighbourhood
simple-pole factor argument; never evaluate an inverse at the pole itself. -/
theorem meromorphicOrderAt_activeM_poleHD {d : Nat} {alpha beta : RealVec d}
    {S : Set (RealVec d)} {f : RealVec d → Complex}
    (data : PositiveInputDataHD alpha beta S f) (x : Torus d)
    (hx : AnalyticParameterHD data x) (a : ActiveIndexHD data x) :
    meromorphicOrderAt (activeMHD data x)
      (poleCoordHD alpha beta x a.1.1 a.1.2 : Complex) =
        (-1 : WithTop Int) := by
  classical
  let p : Complex := (poleCoordHD alpha beta x a.1.1 a.1.2 : Complex)
  let r : Complex := residueCoordHD data alpha beta x a.1.1 a.1.2
  let T : Finset (ActiveIndexHD data x) := {a}
  let H : Complex → Complex := fun w =>
    ∑' b : {b : ActiveIndexHD data x // b ∉ T}, activeTermHD data x b.1 w
  have hp0real : poleCoordHD alpha beta x a.1.1 a.1.2 ≠ 0 := by
    simpa using poleCoordHD_not_int_of_not_sineBad alpha beta x hx.offBad
      a.1.1 a.1.2 0
  have hp0 : p ≠ 0 := Complex.ofReal_ne_zero.mpr hp0real
  let R : Real := ‖p‖ + 1
  have hR : 0 ≤ R := by
    dsimp [R]
    positivity
  let P : Set Complex := complexPoleSetHD data x ∩ Metric.closedBall 0 R
  have hPfinite : P.Finite := finite_complexPoleSetHD_inter_closedBall data x hx R hR
  let Q : Set Complex := P \ {p}
  have hQfinite : Q.Finite := hPfinite.sdiff
  have hpPole : p ∈ complexPoleSetHD data x := by
    exact ⟨poleCoordHD alpha beta x a.1.1 a.1.2, ⟨a, rfl⟩, rfl⟩
  have hpU : p ∈ Metric.ball (0 : Complex) R \ Q := by
    refine ⟨?_, ?_⟩
    · simp [Metric.mem_ball, R]
    · simp [Q]
  have hUopen : IsOpen (Metric.ball (0 : Complex) R \ Q) :=
    IsOpen.sdiff Metric.isOpen_ball hQfinite.isClosed
  obtain ⟨K, ⟨hpK, hKcompact⟩, hKsub⟩ :=
    (compact_basis_nhds p).mem_iff.mp (hUopen.mem_nhds hpU)
  rcases exists_cofinite_activeTerm_bound_on_compactHD data x hx K hKcompact with
    ⟨CK, hCK, A0, hA0, htail⟩
  have hweight : Summable (fun b : ActiveIndexHD data x =>
      ‖residueCoordHD data alpha beta x b.1.1 b.1.2‖ /
        (1 + (poleCoordHD alpha beta x b.1.1 b.1.2) ^ 2)) := by
    change Summable
      ((fun b : IntVec d × Int => ‖residueCoordHD data alpha beta x b.1 b.2‖ /
        (1 + (poleCoordHD alpha beta x b.1 b.2) ^ 2)) ∘ Subtype.val)
    exact (summable_residue_weightHD data alpha beta x hx.poleWeightFinite).subtype _
  have hweightTail : Summable
      (fun b : {b : ActiveIndexHD data x // b ∉ T} =>
        ‖residueCoordHD data alpha beta x b.1.1.1 b.1.1.2‖ /
          (1 + (poleCoordHD alpha beta x b.1.1.1 b.1.1.2) ^ 2)) := by
    change Summable
      ((fun b : ActiveIndexHD data x =>
        ‖residueCoordHD data alpha beta x b.1.1 b.1.2‖ /
          (1 + (poleCoordHD alpha beta x b.1.1 b.1.2) ^ 2)) ∘ Subtype.val)
    exact hweight.subtype _
  have hA0tail :
      ((fun b : {b : ActiveIndexHD data x // b ∉ T} => b.1) ⁻¹' A0).Finite :=
    hA0.preimage Subtype.val_injective.injOn
  have htailConv : TendstoUniformlyOn
      (fun t : Finset {b : ActiveIndexHD data x // b ∉ T} => fun w =>
        ∑ b ∈ t, activeTermHD data x b.1 w)
      H atTop K := by
    dsimp [H]
    exact tendstoUniformlyOn_tsum_of_cofinite_eventually (hweightTail.mul_left CK)
      (show ∀ᶠ b : {b : ActiveIndexHD data x // b ∉ T} in cofinite,
          ∀ w ∈ K, ‖activeTermHD data x b.1 w‖ ≤
            CK * (‖residueCoordHD data alpha beta x b.1.1.1 b.1.1.2‖ /
              (1 + (poleCoordHD alpha beta x b.1.1.1 b.1.1.2) ^ 2)) by
        filter_upwards [hA0tail.compl_mem_cofinite] with b hb w hw
        simpa [mul_div_assoc] using htail b.1 hb w hw)
  have htailPartials :
      ∀ᶠ t : Finset {b : ActiveIndexHD data x // b ∉ T} in atTop,
      DifferentiableOn Complex (fun w => ∑ b ∈ t, activeTermHD data x b.1 w)
        (interior K) := by
    filter_upwards [] with t
    exact DifferentiableOn.fun_sum fun b _ w hw => by
      have hne : w ≠ (poleCoordHD alpha beta x b.1.1.1 b.1.1.2 : Complex) := by
        intro hwp
        have hwPole : w ∈ complexPoleSetHD data x := by
          rw [hwp]
          exact ⟨poleCoordHD alpha beta x b.1.1.1 b.1.1.2, ⟨b.1, rfl⟩, rfl⟩
        have hwU := hKsub (interior_subset hw)
        have hwpEq : w = p := by
          by_contra hnep
          exact hwU.2 ⟨⟨hwPole, Metric.ball_subset_closedBall hwU.1⟩, hnep⟩
        have hpoles :
            poleCoordHD alpha beta x b.1.1.1 b.1.1.2 =
              poleCoordHD alpha beta x a.1.1 a.1.2 := by
          exact Complex.ofReal_injective (hwp.symm.trans hwpEq)
        have hpair : b.1.1 = a.1 := hx.poleInjective hpoles
        have hactive : b.1 = a := Subtype.ext hpair
        exact b.2 (by simp [T, hactive])
      exact (analyticAt_activeTermHD_of_ne_pole data x b.1 hne).differentiableAt
        |>.differentiableWithinAt
  have hHdiff :=
    htailConv.tendstoLocallyUniformlyOn.mono interior_subset |>.differentiableOn
      htailPartials isOpen_interior
  have hpInt : p ∈ interior K := mem_of_mem_nhds (interior_mem_nhds.mpr hpK)
  have hHanalytic : AnalyticAt Complex H p :=
    (hHdiff.analyticOnNhd isOpen_interior) p hpInt
  have hmajorant := hweight.mul_left CK
  have hsum : ∀ w ∈ K, Summable (fun b : ActiveIndexHD data x =>
      activeTermHD data x b w) := by
    intro w hw
    exact Summable.of_norm_bounded_eventually hmajorant <| by
      filter_upwards [hA0.compl_mem_cofinite] with b hb
      simpa [mul_div_assoc] using htail b hb w hw
  have hdecomp : ∀ w ∈ K, activeMHD data x w = activeTermHD data x a w + H w := by
    intro w hw
    have hsplit := (hsum w hw).sum_add_tsum_subtype_compl T
    simpa [activeMHD, H, T] using hsplit.symm
  let numerator : Complex → Complex := fun w =>
    r + (w - p) * (r / p + H w)
  have hnumAnalytic : AnalyticAt Complex numerator p := by
    dsimp [numerator]
    exact analyticAt_const.add <|
      (analyticAt_id.sub analyticAt_const).mul
        (analyticAt_const.add hHanalytic)
  have hnumValue : numerator p = r := by
    simp [numerator]
  have hevent : activeMHD data x =ᶠ[nhdsWithin p {w : Complex | w ≠ p}]
      (fun w => numerator w / (w - p)) := by
    have hKevent : ∀ᶠ w in nhdsWithin p {w : Complex | w ≠ p}, w ∈ K :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds hpK
    filter_upwards [hKevent, self_mem_nhdsWithin] with w hwK hwp
    have hdecompw := hdecomp w hwK
    dsimp [numerator]
    rw [hdecompw]
    change r * (1 / (w - p) + 1 / p) + H w =
      (r + (w - p) * (r / p + H w)) / (w - p)
    have hwp' : w - p ≠ 0 := sub_ne_zero.mpr hwp
    field_simp [hp0, hwp']
    ring
  have hmer : MeromorphicAt (activeMHD data x) p :=
    meromorphicOn_activeMHD data x hx p (Set.mem_univ p)
  apply (meromorphicOrderAt_eq_int_iff hmer).2
  refine ⟨numerator, hnumAnalytic, ?_, ?_⟩
  · rw [hnumValue]
    exact a.2
  · filter_upwards [hevent] with z hz
    rw [hz]
    simp only [zpow_neg, zpow_one, smul_eq_mul]
    change numerator z / (z - p) = (z - p)⁻¹ * numerator z
    simp [div_eq_mul_inv, mul_comm]

/- Proof idea: outside the pole set use analyticity; inside it choose the unique active
index and apply the exact order `-1` theorem. -/
theorem activeMHD_hasPoleAt_iff {d : Nat} {alpha beta : RealVec d}
    {S : Set (RealVec d)} {f : RealVec d → Complex}
    (data : PositiveInputDataHD alpha beta S f) (x : Torus d)
    (hx : AnalyticParameterHD data x) (z : Complex) :
    meromorphicOrderAt (activeMHD data x) z < (0 : WithTop Int) ↔
      z ∈ complexPoleSetHD data x := by
  constructor
  · intro hneg
    by_contra hz
    have hzmem : z ∈ Set.univ \ complexPoleSetHD data x := ⟨Set.mem_univ z, hz⟩
    have hopen : IsOpen (Set.univ \ complexPoleSetHD data x) :=
      IsOpen.sdiff isOpen_univ (isClosed_complexPoleSetHD data x hx)
    have hanWithin := analyticOn_activeM_compl_polesHD data x hx z hzmem
    have han : AnalyticAt Complex (activeMHD data x) z := by
      rw [← analyticWithinAt_univ]
      exact hanWithin.mono_of_mem_nhdsWithin (by simpa using hopen.mem_nhds hzmem)
    exact (not_lt_of_ge han.meromorphicOrderAt_nonneg) hneg
  · rintro ⟨p, ⟨a, rfl⟩, rfl⟩
    rw [meromorphicOrderAt_activeM_poleHD data x hx a]
    exact WithTop.coe_lt_coe.mpr (neg_one_lt_zero : (-1 : Int) < 0)

/- Proof idea: fill the generic counting-data record using global meromorphicity, a genuine
simple pole, finite integer orders, and local finiteness of the divisor support. -/
theorem activeMHD_countingData {d : Nat} {alpha beta : RealVec d}
    {S : Set (RealVec d)} {f : RealVec d → Complex}
    (data : PositiveInputDataHD alpha beta S f) (x : Torus d)
    (hx : AnalyticParameterHD data x) (hactive : Nonempty (ActiveIndexHD data x)) :
    Nonempty (Theorem12.Generic.MeromorphicCountingData (activeMHD data x)) := by
  classical
  let F : Complex → Complex := activeMHD data x
  have hmer : MeromorphicOn F Set.univ := meromorphicOn_activeMHD data x hx
  obtain ⟨a⟩ := hactive
  let p : Complex := (poleCoordHD alpha beta x a.1.1 a.1.2 : Complex)
  have hpOrder : meromorphicOrderAt F p = (-1 : WithTop Int) := by
    exact meromorphicOrderAt_activeM_poleHD data x hx a
  have hpFinite : meromorphicOrderAt F p ≠ (⊤ : WithTop Int) := by
    rw [hpOrder]
    exact WithTop.coe_ne_top
  have horderFinite : ∀ z : Complex, meromorphicOrderAt F z ≠ (⊤ : WithTop Int) := by
    have hall :=
      (hmer.exists_meromorphicOrderAt_ne_top_iff_forall_mem isConnected_univ).1
        ⟨p, Set.mem_univ p, hpFinite⟩
    exact fun z => hall z (Set.mem_univ z)
  let ord : Complex → Int := fun z => (meromorphicOrderAt F z).untop₀
  refine ⟨⟨hmer, horderFinite, ord, ?_, ?_⟩⟩
  · intro z
    dsimp [ord]
    exact WithTop.coe_untop₀_of_ne_top (horderFinite z)
  · intro R
    have hmerBall : MeromorphicOn F (Metric.closedBall (0 : Complex) R) :=
      fun z _ => hmer z (Set.mem_univ z)
    have hdivFinite :
        (MeromorphicOn.divisor F (Metric.closedBall (0 : Complex) R)).support.Finite :=
      (MeromorphicOn.divisor F (Metric.closedBall (0 : Complex) R)).finiteSupport
        (isCompact_closedBall (0 : Complex) R)
    refine hdivFinite.subset ?_
    rintro z ⟨hzord, hzR⟩
    rw [Function.mem_support, MeromorphicOn.divisor_apply hmerBall hzR]
    exact hzord

end UniversalCompletenessHD.Internal
