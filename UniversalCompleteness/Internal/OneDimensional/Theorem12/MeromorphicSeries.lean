import Theorem12.GenericAuxiliary
import Theorem12.PoleCoordinates
import Theorem12.Summability
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Topology.Algebra.InfiniteSum.UniformOn

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace Theorem12.Internal

/- Proof idea: transparently conjoin exclusion from the sine-zero locus with finiteness
of the full ENNReal weighted pole sum. -/
def AnalyticParameter {alpha : ℝ} {beta : ℚ} {S : Set ℝ} {f : ℝ → ℂ}
    (data : PositiveInputData alpha beta S f) (x : AddCircle (1 : ℝ)) : Prop :=
  x ∉ sineBad alpha beta ∧
    (∑' a : ℤ × ℤ, poleWeightENN data alpha beta x a) < ∞

/- Proof idea: transparently subtype the fixed integer-pair index set by nonvanishing residue. -/
def ActiveIndex {alpha : ℝ} {beta : ℚ} {S : Set ℝ} {f : ℝ → ℂ}
    (data : PositiveInputData alpha beta S f) (x : AddCircle (1 : ℝ)) :=
  {a : ℤ × ℤ // residueCoord data alpha beta x a.1 a.2 ≠ 0}

/- Proof idea: transparently take the range of the real pole coordinate over active indices. -/
def realPoleSet {alpha : ℝ} {beta : ℚ} {S : Set ℝ} {f : ℝ → ℂ}
    (data : PositiveInputData alpha beta S f) (x : AddCircle (1 : ℝ)) : Set ℝ :=
  Set.range (fun a : ActiveIndex data x => poleCoord alpha beta x a.1.1 a.1.2)

/- Proof idea: transparently embed the typed real pole set into `ℂ` with `Complex.ofReal`. -/
def complexPoleSet {alpha : ℝ} {beta : ℚ} {S : Set ℝ} {f : ℝ → ℂ}
    (data : PositiveInputData alpha beta S f) (x : AddCircle (1 : ℝ)) : Set ℂ :=
  Complex.ofReal '' realPoleSet data x

/- Proof idea: use `finite_activePair_pole_Icc` on the finite weighted sum, express the intersection as
the image of the finite active-pair set, and take its finite image without injectivity. -/
theorem finite_realPoleSet_inter_Icc {alpha : ℝ} {beta : ℚ} {S : Set ℝ} {f : ℝ → ℂ}
    (data : PositiveInputData alpha beta S f) (x : AddCircle (1 : ℝ))
    (hx : AnalyticParameter data x) (R : ℝ) (hR : 0 ≤ R) :
    Set.Finite (realPoleSet data x ∩ Set.Icc (-R) R) := by
  refine
    (finite_activePair_pole_Icc data x hx.2 R hR).image
      (fun a : ℤ × ℤ => poleCoord alpha beta x a.1 a.2) |>.subset ?_
  rintro y ⟨⟨a, rfl⟩, haIcc⟩
  exact ⟨a.1, ⟨a.2, haIcc⟩, rfl⟩

/- Proof idea: pull the closed-ball intersection back to the real interval using
`‖Complex.ofReal p‖ = |p|`, then use `finite_realPoleSet_inter_Icc` and finite images. -/
theorem finite_complexPoleSet_inter_closedBall {alpha : ℝ} {beta : ℚ}
    {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f)
    (x : AddCircle (1 : ℝ)) (hx : AnalyticParameter data x) (R : ℝ) (hR : 0 ≤ R) :
    Set.Finite (complexPoleSet data x ∩ Metric.closedBall 0 R) := by
  refine
    (finite_realPoleSet_inter_Icc data x hx R hR).image Complex.ofReal |>.subset ?_
  rintro z ⟨⟨p, hp, rfl⟩, hpR⟩
  refine ⟨p, ⟨hp, ?_⟩, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_real] at hpR
  exact (abs_le.mp hpR)

/- Proof idea: transparently use `z / (p * (z-p))`; denominator nonvanishing is supplied
only to later algebraic theorems and is not hidden in this total definition. -/
def regularizedKernel (p : ℝ) (z : ℂ) : ℂ :=
  z / ((p : ℂ) * (z - (p : ℂ)))

/- Proof idea: transparently multiply the exact source residue by the regularized kernel
at the corresponding real pole coordinate. -/
def activeTerm {alpha : ℝ} {beta : ℚ} {S : Set ℝ} {f : ℝ → ℂ}
    (data : PositiveInputData alpha beta S f) (x : AddCircle (1 : ℝ))
    (a : ActiveIndex data x) (z : ℂ) : ℂ :=
  residueCoord data alpha beta x a.1.1 a.1.2 *
    regularizedKernel (poleCoord alpha beta x a.1.1 a.1.2) z

/- Proof idea: transparently take the complex `tsum` of active terms over the fixed
parameter's active subtype; convergence is asserted only under `AnalyticParameter` below. -/
def activeM {alpha : ℝ} {beta : ℚ} {S : Set ℝ} {f : ℝ → ℂ}
    (data : PositiveInputData alpha beta S f) (x : AddCircle (1 : ℝ)) (z : ℂ) : ℂ :=
  ∑' a : ActiveIndex data x, activeTerm data x a z

end Theorem12.Internal

namespace Theorem12.ScaffoldAxioms

open Theorem12.Internal

private theorem exists_cofinite_activeTerm_bound_on_compact {alpha : ℝ} {beta : ℚ}
    {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f)
    (x : AddCircle (1 : ℝ)) (hx : AnalyticParameter data x)
    (K : Set ℂ) (hKcompact : IsCompact K) :
    ∃ CK : ℝ, 0 ≤ CK ∧ ∃ A0 : Set (ActiveIndex data x), A0.Finite ∧
      ∀ a : ActiveIndex data x, a ∉ A0 → ∀ z ∈ K,
        ‖activeTerm data x a z‖ ≤
          CK * ‖residueCoord data alpha beta x a.1.1 a.1.2‖ /
            (1 + (poleCoord alpha beta x a.1.1 a.1.2) ^ 2) := by
  classical
  obtain ⟨C, hCpos, hC⟩ := hKcompact.isBounded.exists_pos_norm_le
  let B : ℝ := 2 * C + 1
  let A0 : Set (ActiveIndex data x) :=
    {a | |poleCoord alpha beta x a.1.1 a.1.2| ≤ B}
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hpairFinite := finite_activePair_pole_Icc data x hx.2 B hB
  have hA0 : A0.Finite := by
    refine (hpairFinite.preimage Subtype.val_injective.injOn).subset ?_
    intro a ha
    exact ⟨a.2, (abs_le.mp ha)⟩
  refine ⟨4 * C, by positivity, A0, hA0, ?_⟩
  intro a ha z hz
  let p : ℝ := poleCoord alpha beta x a.1.1 a.1.2
  have hpLarge : B < |p| := lt_of_not_ge ha
  have hBpos : 0 < B := by
    dsimp [B]
    positivity
  have hpAbsPos : 0 < |p| := lt_trans hBpos hpLarge
  have hzNorm : ‖z‖ ≤ C := hC z hz
  have hpzLower : |p| - ‖z‖ ≤ ‖z - (p : ℂ)‖ := by
    simpa [Complex.norm_real, norm_sub_rev] using norm_sub_norm_le (p : ℂ) z
  have hpHalf : |p| / 2 ≤ ‖z - (p : ℂ)‖ := by
    dsimp [B] at hpLarge
    nlinarith
  have hdistPos : 0 < ‖z - (p : ℂ)‖ := lt_of_lt_of_le (half_pos hpAbsPos) hpHalf
  rw [activeTerm, regularizedKernel, norm_mul, norm_div, norm_mul,
    Complex.norm_real, Real.norm_eq_abs]
  change
    ‖residueCoord data alpha beta x a.1.1 a.1.2‖ *
        (‖z‖ / (|p| * ‖z - (p : ℂ)‖)) ≤
      4 * C * ‖residueCoord data alpha beta x a.1.1 a.1.2‖ / (1 + p ^ 2)
  by_cases hr : ‖residueCoord data alpha beta x a.1.1 a.1.2‖ = 0
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
  have hright : C * (2 * |p| ^ 2) ≤ 4 * C * (|p| * ‖z - (p : ℂ)‖) := by
    have hmul :=
      mul_le_mul_of_nonneg_left hpHalf
        (show 0 ≤ 4 * C * |p| by positivity)
    nlinarith
  exact hleft.trans (hmid.trans hright)

/-
This public helper has exactly the compact estimate; the private theorem below
is its sole consumer and introduces no stronger assumption or conclusion.
-/
theorem series_010_norm_activeTerm_le_on_compact {alpha : ℝ} {beta : ℚ}
    {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f)
    (x : AddCircle (1 : ℝ)) (hx : AnalyticParameter data x)
    (K : Set ℂ) (hKcompact : IsCompact K) (hK : Disjoint K (complexPoleSet data x)) :
    ∃ CK : ℝ, 0 ≤ CK ∧ ∃ A0 : Set (ActiveIndex data x), A0.Finite ∧
      (∀ a : ActiveIndex data x, a ∉ A0 → ∀ z ∈ K,
        ‖activeTerm data x a z‖ ≤
          CK * ‖residueCoord data alpha beta x a.1.1 a.1.2‖ /
            (1 + (poleCoord alpha beta x a.1.1 a.1.2) ^ 2)) ∧
      (∀ a : ActiveIndex data x, a ∈ A0 → AnalyticOnNhd ℂ (activeTerm data x a) K) := by
  classical
  rcases exists_cofinite_activeTerm_bound_on_compact data x hx K hKcompact with
    ⟨CK, hCK, A0, hA0, htail⟩
  refine ⟨CK, hCK, A0, hA0, htail, ?_⟩
  intro a _ z hz
  have hp0 : poleCoord alpha beta x a.1.1 a.1.2 ≠ 0 := by
    simpa using poleCoord_not_int_of_not_sineBad alpha beta x hx.1 a.1.1 a.1.2 0
  have hpMem : (poleCoord alpha beta x a.1.1 a.1.2 : ℂ) ∈ complexPoleSet data x := by
    exact ⟨poleCoord alpha beta x a.1.1 a.1.2, ⟨a, rfl⟩, rfl⟩
  have hzp : z ≠ (poleCoord alpha beta x a.1.1 a.1.2 : ℂ) := by
    exact fun hEq => Set.disjoint_left.1 hK hz (hEq ▸ hpMem)
  change AnalyticAt ℂ
    (fun w => residueCoord data alpha beta x a.1.1 a.1.2 *
      (w / ((poleCoord alpha beta x a.1.1 a.1.2 : ℂ) *
        (w - (poleCoord alpha beta x a.1.1 a.1.2 : ℂ))))) z
  exact analyticAt_const.mul <|
    analyticAt_id.div
      (analyticAt_const.mul (analyticAt_id.sub analyticAt_const))
      (mul_ne_zero (Complex.ofReal_ne_zero.mpr hp0) (sub_ne_zero.mpr hzp))

end Theorem12.ScaffoldAxioms

namespace Theorem12.Internal

/- Proof idea: bound `z` on compact `K`, obtain quadratic decay for all sufficiently large
real poles, and isolate the finitely many bounded poles as the analytic exceptional set. -/
private theorem norm_activeTerm_le_on_compact {alpha : ℝ} {beta : ℚ}
    {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f)
    (x : AddCircle (1 : ℝ)) (hx : AnalyticParameter data x)
    (K : Set ℂ) (hKcompact : IsCompact K) (hK : Disjoint K (complexPoleSet data x)) :
    ∃ CK : ℝ, 0 ≤ CK ∧ ∃ A0 : Set (ActiveIndex data x), A0.Finite ∧
      (∀ a : ActiveIndex data x, a ∉ A0 → ∀ z ∈ K,
        ‖activeTerm data x a z‖ ≤
          CK * ‖residueCoord data alpha beta x a.1.1 a.1.2‖ /
            (1 + (poleCoord alpha beta x a.1.1 a.1.2) ^ 2)) ∧
      (∀ a : ActiveIndex data x, a ∈ A0 → AnalyticOnNhd ℂ (activeTerm data x a) K) :=
  Theorem12.ScaffoldAxioms.series_010_norm_activeTerm_le_on_compact
    data x hx K hKcompact hK

/- Proof idea: combine the finite analytic head and the uniformly summable majorized tail
from `norm_activeTerm_le_on_compact`, identifying its pointwise sum with the transparent `activeM` `tsum`. -/
theorem hasSum_activeM_locallyUniformly {alpha : ℝ} {beta : ℚ}
    {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f)
    (x : AddCircle (1 : ℝ)) (hx : AnalyticParameter data x)
    (K : Set ℂ) (hKcompact : IsCompact K) (hK : Disjoint K (complexPoleSet data x)) :
    HasSumUniformlyOn (fun a : ActiveIndex data x => activeTerm data x a)
      (activeM data x) K := by
  classical
  rcases norm_activeTerm_le_on_compact data x hx K hKcompact hK with
    ⟨CK, hCK, A0, hA0, htail, _⟩
  have hweight : Summable (fun a : ActiveIndex data x =>
      ‖residueCoord data alpha beta x a.1.1 a.1.2‖ /
        (1 + (poleCoord alpha beta x a.1.1 a.1.2) ^ 2)) := by
    change Summable
      ((fun a : ℤ × ℤ => ‖residueCoord data alpha beta x a.1 a.2‖ /
        (1 + (poleCoord alpha beta x a.1 a.2) ^ 2)) ∘ Subtype.val)
    exact (summable_residue_and_indicator_weight data x hx.2).1.subtype _
  have hmajorant := hweight.mul_left CK
  rw [hasSumUniformlyOn_iff_tendstoUniformlyOn]
  change TendstoUniformlyOn
    (fun t : Finset (ActiveIndex data x) => fun z => ∑ a ∈ t, activeTerm data x a z)
    (fun z => ∑' a : ActiveIndex data x, activeTerm data x a z) atTop K
  exact tendstoUniformlyOn_tsum_of_cofinite_eventually hmajorant
      (show ∀ᶠ a : ActiveIndex data x in cofinite, ∀ z ∈ K,
          ‖activeTerm data x a z‖ ≤
            CK * (‖residueCoord data alpha beta x a.1.1 a.1.2‖ /
              (1 + (poleCoord alpha beta x a.1.1 a.1.2) ^ 2)) by
        filter_upwards [hA0.compl_mem_cofinite] with a ha z hz
        simpa [mul_div_assoc] using htail a ha z hz)

private theorem analyticAt_activeTerm_of_ne_pole {alpha : ℝ} {beta : ℚ}
    {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f)
    (x : AddCircle (1 : ℝ)) (hx : AnalyticParameter data x)
    (a : ActiveIndex data x) {z : ℂ}
    (hz : z ≠ (poleCoord alpha beta x a.1.1 a.1.2 : ℂ)) :
    AnalyticAt ℂ (activeTerm data x a) z := by
  have hp0 : poleCoord alpha beta x a.1.1 a.1.2 ≠ 0 := by
    simpa using poleCoord_not_int_of_not_sineBad alpha beta x hx.1 a.1.1 a.1.2 0
  change AnalyticAt ℂ
    (fun w => residueCoord data alpha beta x a.1.1 a.1.2 *
      (w / ((poleCoord alpha beta x a.1.1 a.1.2 : ℂ) *
        (w - (poleCoord alpha beta x a.1.1 a.1.2 : ℂ))))) z
  exact analyticAt_const.mul <|
    analyticAt_id.div
      (analyticAt_const.mul (analyticAt_id.sub analyticAt_const))
      (mul_ne_zero (Complex.ofReal_ne_zero.mpr hp0) (sub_ne_zero.mpr hz))

private theorem isClosed_complexPoleSet {alpha : ℝ} {beta : ℚ}
    {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f)
    (x : AddCircle (1 : ℝ)) (hx : AnalyticParameter data x) :
    IsClosed (complexPoleSet data x) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro z hz
  let R : ℝ := ‖z‖ + 1
  have hR : 0 ≤ R := by
    dsimp [R]
    positivity
  have hzball : z ∈ Metric.ball (0 : ℂ) R := by
    simp [Metric.mem_ball, R]
  let P : Set ℂ := complexPoleSet data x ∩ Metric.closedBall 0 R
  have hPfinite : P.Finite := finite_complexPoleSet_inter_closedBall data x hx R hR
  have hzP : z ∉ P := fun hzP => hz hzP.1
  have hopen : IsOpen (Metric.ball (0 : ℂ) R \ P) :=
    IsOpen.sdiff Metric.isOpen_ball hPfinite.isClosed
  refine mem_of_superset (hopen.mem_nhds ⟨hzball, hzP⟩) ?_
  intro w hw
  rw [Set.mem_compl_iff]
  intro hwPole
  exact hw.2 ⟨hwPole, Metric.ball_subset_closedBall hw.1⟩

private theorem analyticOn_activeM_compl_poles {alpha : ℝ} {beta : ℚ}
    {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f)
    (x : AddCircle (1 : ℝ)) (hx : AnalyticParameter data x) :
    AnalyticOn ℂ (activeM data x) (Set.univ \ complexPoleSet data x) := by
  classical
  intro z hz
  have hzcompl : z ∈ (complexPoleSet data x)ᶜ := hz.2
  obtain ⟨K, ⟨hzK, hKcompact⟩, hKsub⟩ :=
    (compact_basis_nhds z).mem_iff.mp
      ((isClosed_complexPoleSet data x hx).isOpen_compl.mem_nhds hzcompl)
  have hKdisj : Disjoint K (complexPoleSet data x) :=
    Set.disjoint_left.2 fun w hwK hwP => (hKsub hwK) hwP
  have hconv :=
    (hasSum_activeM_locallyUniformly data x hx K hKcompact hKdisj).tendstoUniformlyOn
  have hlocal : TendstoLocallyUniformlyOn
      (fun t : Finset (ActiveIndex data x) => fun w => ∑ a ∈ t, activeTerm data x a w)
      (activeM data x) atTop (interior K) :=
    hconv.tendstoLocallyUniformlyOn.mono interior_subset
  have hpartials : ∀ᶠ t : Finset (ActiveIndex data x) in atTop,
      DifferentiableOn ℂ (fun w => ∑ a ∈ t, activeTerm data x a w) (interior K) := by
    filter_upwards [] with t
    exact DifferentiableOn.fun_sum fun a _ w hw =>
      (analyticAt_activeTerm_of_ne_pole data x hx a <| by
        intro hwp
        have hpMem : (poleCoord alpha beta x a.1.1 a.1.2 : ℂ) ∈
            complexPoleSet data x :=
          ⟨poleCoord alpha beta x a.1.1 a.1.2, ⟨a, rfl⟩, rfl⟩
        exact Set.disjoint_left.1 hKdisj (interior_subset hw) (hwp ▸ hpMem)).differentiableAt
        |>.differentiableWithinAt
  have hdiff := hlocal.differentiableOn hpartials isOpen_interior
  have hzInt : z ∈ interior K := mem_of_mem_nhds (interior_mem_nhds.mpr hzK)
  exact ((hdiff.analyticOnNhd isOpen_interior) z hzInt).analyticWithinAt

private theorem analyticAt_sq_mul_activeTerm_at_pole {alpha : ℝ} {beta : ℚ}
    {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f)
    (x : AddCircle (1 : ℝ)) (hx : AnalyticParameter data x)
    (a : ActiveIndex data x) :
    AnalyticAt ℂ
      (fun w =>
        (w - (poleCoord alpha beta x a.1.1 a.1.2 : ℂ)) ^ 2 *
          activeTerm data x a w)
      (poleCoord alpha beta x a.1.1 a.1.2 : ℂ) := by
  let p : ℝ := poleCoord alpha beta x a.1.1 a.1.2
  let r : ℂ := residueCoord data alpha beta x a.1.1 a.1.2
  have hp0 : p ≠ 0 := by
    dsimp [p]
    simpa using poleCoord_not_int_of_not_sineBad alpha beta x hx.1 a.1.1 a.1.2 0
  have heq :
      (fun w : ℂ => (w - (p : ℂ)) ^ 2 * activeTerm data x a w) =
        (fun w : ℂ => r * (w * (w - (p : ℂ)) / (p : ℂ))) := by
    funext w
    by_cases hwp : w = (p : ℂ)
    · subst w
      simp [activeTerm, regularizedKernel, p, r]
    · rw [activeTerm, regularizedKernel]
      change (w - (p : ℂ)) ^ 2 * (r * (w / ((p : ℂ) * (w - (p : ℂ))))) =
        r * (w * (w - (p : ℂ)) / (p : ℂ))
      field_simp [Complex.ofReal_ne_zero.mpr hp0, hwp]
  rw [heq]
  fun_prop

private theorem meromorphicAt_activeM {alpha : ℝ} {beta : ℚ}
    {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f)
    (x : AddCircle (1 : ℝ)) (hx : AnalyticParameter data x) (z : ℂ) :
    MeromorphicAt (activeM data x) z := by
  classical
  let R : ℝ := ‖z‖ + 1
  have hR : 0 ≤ R := by
    dsimp [R]
    positivity
  let P : Set ℂ := complexPoleSet data x ∩ Metric.closedBall 0 R
  have hPfinite : P.Finite := finite_complexPoleSet_inter_closedBall data x hx R hR
  let Q : Set ℂ := P \ {z}
  have hQfinite : Q.Finite := hPfinite.sdiff
  have hzU : z ∈ Metric.ball (0 : ℂ) R \ Q := by
    refine ⟨?_, ?_⟩
    · simp [Metric.mem_ball, R]
    · simp [Q]
  have hUopen : IsOpen (Metric.ball (0 : ℂ) R \ Q) :=
    IsOpen.sdiff Metric.isOpen_ball hQfinite.isClosed
  obtain ⟨K, ⟨hzK, hKcompact⟩, hKsub⟩ :=
    (compact_basis_nhds z).mem_iff.mp (hUopen.mem_nhds hzU)
  rcases Theorem12.ScaffoldAxioms.exists_cofinite_activeTerm_bound_on_compact
      data x hx K hKcompact with ⟨CK, hCK, A0, hA0, htail⟩
  obtain ⟨D, hDpos, hD⟩ := hKcompact.isBounded.exists_pos_norm_le
  let E : ℝ := (D + ‖z‖) ^ 2
  have hE : 0 ≤ E := sq_nonneg _
  have hweight : Summable (fun a : ActiveIndex data x =>
      ‖residueCoord data alpha beta x a.1.1 a.1.2‖ /
        (1 + (poleCoord alpha beta x a.1.1 a.1.2) ^ 2)) := by
    change Summable
      ((fun a : ℤ × ℤ => ‖residueCoord data alpha beta x a.1 a.2‖ /
        (1 + (poleCoord alpha beta x a.1 a.2) ^ 2)) ∘ Subtype.val)
    exact (summable_residue_and_indicator_weight data x hx.2).1.subtype _
  have hmajorant := hweight.mul_left (E * CK)
  have hbound : ∀ᶠ a : ActiveIndex data x in cofinite, ∀ w ∈ K,
      ‖(w - z) ^ 2 * activeTerm data x a w‖ ≤
        (E * CK) *
          (‖residueCoord data alpha beta x a.1.1 a.1.2‖ /
            (1 + (poleCoord alpha beta x a.1.1 a.1.2) ^ 2)) := by
    filter_upwards [hA0.compl_mem_cofinite] with a ha w hw
    have hwsub : ‖w - z‖ ≤ D + ‖z‖ :=
      (norm_sub_le w z).trans (add_le_add (hD w hw) le_rfl)
    have hpow : ‖w - z‖ ^ 2 ≤ E := by
      dsimp [E]
      exact pow_le_pow_left₀ (norm_nonneg _) hwsub 2
    rw [norm_mul, norm_pow]
    calc
      ‖w - z‖ ^ 2 * ‖activeTerm data x a w‖
          ≤ E * ‖activeTerm data x a w‖ :=
        mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
      _ ≤ E * (CK * ‖residueCoord data alpha beta x a.1.1 a.1.2‖ /
            (1 + (poleCoord alpha beta x a.1.1 a.1.2) ^ 2)) :=
        mul_le_mul_of_nonneg_left (htail a ha w hw) hE
      _ = (E * CK) *
          (‖residueCoord data alpha beta x a.1.1 a.1.2‖ /
            (1 + (poleCoord alpha beta x a.1.1 a.1.2) ^ 2)) := by ring
  have hconv : TendstoUniformlyOn
      (fun t : Finset (ActiveIndex data x) => fun w =>
        ∑ a ∈ t, (w - z) ^ 2 * activeTerm data x a w)
      (fun w => ∑' a : ActiveIndex data x, (w - z) ^ 2 * activeTerm data x a w)
      atTop K :=
    tendstoUniformlyOn_tsum_of_cofinite_eventually hmajorant hbound
  have hlocal := hconv.tendstoLocallyUniformlyOn.mono interior_subset
  have hpartials : ∀ᶠ t : Finset (ActiveIndex data x) in atTop,
      DifferentiableOn ℂ
        (fun w => ∑ a ∈ t, (w - z) ^ 2 * activeTerm data x a w) (interior K) := by
    filter_upwards [] with t
    exact DifferentiableOn.fun_sum fun a _ w hw => by
      by_cases hwp : w = (poleCoord alpha beta x a.1.1 a.1.2 : ℂ)
      · have hpMem : w ∈ complexPoleSet data x := by
          rw [hwp]
          exact ⟨poleCoord alpha beta x a.1.1 a.1.2, ⟨a, rfl⟩, rfl⟩
        have hwU := hKsub (interior_subset hw)
        have hpz : w = z := by
          by_contra hwz
          exact hwU.2 ⟨⟨hpMem, Metric.ball_subset_closedBall hwU.1⟩, hwz⟩
        have hcenter : z = (poleCoord alpha beta x a.1.1 a.1.2 : ℂ) :=
          hpz.symm.trans hwp
        simpa [hcenter, hwp] using
          (analyticAt_sq_mul_activeTerm_at_pole data x hx a).differentiableAt
            |>.differentiableWithinAt
      · exact (((analyticAt_id.sub analyticAt_const).pow 2).mul
          (analyticAt_activeTerm_of_ne_pole data x hx a hwp)).differentiableAt
          |>.differentiableWithinAt
  have hdiff := hlocal.differentiableOn hpartials isOpen_interior
  have hzInt : z ∈ interior K := mem_of_mem_nhds (interior_mem_nhds.mpr hzK)
  have hanalyticTsum : AnalyticAt ℂ
      (fun w => ∑' a : ActiveIndex data x, (w - z) ^ 2 * activeTerm data x a w) z :=
    (hdiff.analyticOnNhd isOpen_interior) z hzInt
  refine ⟨2, ?_⟩
  change AnalyticAt ℂ (fun w => (w - z) ^ 2 * activeM data x w) z
  convert hanalyticTsum using 1
  funext w
  simp only [activeM, tsum_mul_left]

/- Proof idea: use locally uniform analytic convergence off poles; near any point split the
locally finite pole head from an analytic tail, then glue the finite meromorphic head and tail. -/
theorem meromorphicOn_activeM {alpha : ℝ} {beta : ℚ} {S : Set ℝ} {f : ℝ → ℂ}
    (data : PositiveInputData alpha beta S f) (x : AddCircle (1 : ℝ))
    (hx : AnalyticParameter data x) :
    MeromorphicOn (activeM data x) Set.univ ∧
      AnalyticOn ℂ (activeM data x) (Set.univ \ complexPoleSet data x) := by
  exact ⟨fun z _ => meromorphicAt_activeM data x hx z,
    analyticOn_activeM_compl_poles data x hx⟩

/- Proof idea: use off-badness to make every active pole nonzero, simplify each regularized
kernel at zero to zero, and identify the resulting `tsum` with `tsum_zero`. -/
theorem activeM_zero {alpha : ℝ} {beta : ℚ} {S : Set ℝ} {f : ℝ → ℂ}
    (data : PositiveInputData alpha beta S f) (x : AddCircle (1 : ℝ))
    (hx : AnalyticParameter data x) :
    activeM data x 0 = 0 := by
  have _ := hx
  simp [activeM, activeTerm, regularizedKernel]

/- Proof idea: literally package an analytic numerator, its exact residue value at the selected
pole, and equality to the quotient only on the punctured neighbourhood of that pole. -/
private structure SimplePoleFactorData {alpha : ℝ} {beta : ℚ}
    {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f)
    (x : AddCircle (1 : ℝ)) (a : ActiveIndex data x) where
  numerator : ℂ → ℂ
  analyticAt_numerator : AnalyticAt ℂ numerator
    (poleCoord alpha beta x a.1.1 a.1.2 : ℂ)
  numerator_at_pole :
    numerator (poleCoord alpha beta x a.1.1 a.1.2 : ℂ) =
      residueCoord data alpha beta x a.1.1 a.1.2
  eventuallyEq_punctured :
    activeM data x =ᶠ[
      nhdsWithin (poleCoord alpha beta x a.1.1 a.1.2 : ℂ)
        {z : ℂ | z ≠ (poleCoord alpha beta x a.1.1 a.1.2 : ℂ)}]
      (fun z => numerator z /
        (z - (poleCoord alpha beta x a.1.1 a.1.2 : ℂ)))

end Theorem12.Internal

namespace Theorem12.ScaffoldAxioms

open Theorem12.Internal

/-
The helper exposes exactly the four literal factor-data fields without leaking the private
structure name; the same-file private wrapper below performs only structural packaging.
-/
theorem series_018_exists_simplePoleFactorFields {alpha : ℝ} {beta : ℚ}
    {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f)
    (x : AddCircle (1 : ℝ)) (hAlpha : Irrational alpha) (hbeta0 : beta ≠ 0)
    (hx : AnalyticParameter data x) (a : ActiveIndex data x) :
    ∃ numerator : ℂ → ℂ,
      AnalyticAt ℂ numerator (poleCoord alpha beta x a.1.1 a.1.2 : ℂ) ∧
      numerator (poleCoord alpha beta x a.1.1 a.1.2 : ℂ) =
        residueCoord data alpha beta x a.1.1 a.1.2 ∧
      activeM data x =ᶠ[
        nhdsWithin (poleCoord alpha beta x a.1.1 a.1.2 : ℂ)
          {z : ℂ | z ≠ (poleCoord alpha beta x a.1.1 a.1.2 : ℂ)}]
        (fun z => numerator z /
          (z - (poleCoord alpha beta x a.1.1 a.1.2 : ℂ))) := by
  classical
  let p : ℂ := (poleCoord alpha beta x a.1.1 a.1.2 : ℂ)
  let T : Finset (ActiveIndex data x) := {a}
  let H : ℂ → ℂ := fun w =>
    ∑' b : {b : ActiveIndex data x // b ∉ T}, activeTerm data x b.1 w
  have hp0real : poleCoord alpha beta x a.1.1 a.1.2 ≠ 0 := by
    simpa using poleCoord_not_int_of_not_sineBad alpha beta x hx.1 a.1.1 a.1.2 0
  have hp0 : p ≠ 0 := Complex.ofReal_ne_zero.mpr hp0real
  let R : ℝ := ‖p‖ + 1
  have hR : 0 ≤ R := by
    dsimp [R]
    positivity
  let P : Set ℂ := complexPoleSet data x ∩ Metric.closedBall 0 R
  have hPfinite : P.Finite := finite_complexPoleSet_inter_closedBall data x hx R hR
  let Q : Set ℂ := P \ {p}
  have hQfinite : Q.Finite := hPfinite.sdiff
  have hpPole : p ∈ complexPoleSet data x := by
    exact ⟨poleCoord alpha beta x a.1.1 a.1.2, ⟨a, rfl⟩, rfl⟩
  have hpU : p ∈ Metric.ball (0 : ℂ) R \ Q := by
    refine ⟨?_, ?_⟩
    · simp [Metric.mem_ball, R]
    · simp [Q]
  have hUopen : IsOpen (Metric.ball (0 : ℂ) R \ Q) :=
    IsOpen.sdiff Metric.isOpen_ball hQfinite.isClosed
  obtain ⟨K, ⟨hpK, hKcompact⟩, hKsub⟩ :=
    (compact_basis_nhds p).mem_iff.mp (hUopen.mem_nhds hpU)
  rcases exists_cofinite_activeTerm_bound_on_compact data x hx K hKcompact with
    ⟨CK, hCK, A0, hA0, htail⟩
  have hweight : Summable (fun b : ActiveIndex data x =>
      ‖residueCoord data alpha beta x b.1.1 b.1.2‖ /
        (1 + (poleCoord alpha beta x b.1.1 b.1.2) ^ 2)) := by
    change Summable
      ((fun b : ℤ × ℤ => ‖residueCoord data alpha beta x b.1 b.2‖ /
        (1 + (poleCoord alpha beta x b.1 b.2) ^ 2)) ∘ Subtype.val)
    exact (summable_residue_and_indicator_weight data x hx.2).1.subtype _
  have hweightTail : Summable
      (fun b : {b : ActiveIndex data x // b ∉ T} =>
        ‖residueCoord data alpha beta x b.1.1.1 b.1.1.2‖ /
          (1 + (poleCoord alpha beta x b.1.1.1 b.1.1.2) ^ 2)) := by
    change Summable
      ((fun b : ActiveIndex data x =>
        ‖residueCoord data alpha beta x b.1.1 b.1.2‖ /
          (1 + (poleCoord alpha beta x b.1.1 b.1.2) ^ 2)) ∘ Subtype.val)
    exact hweight.subtype _
  have hA0tail :
      ((fun b : {b : ActiveIndex data x // b ∉ T} => b.1) ⁻¹' A0).Finite :=
    hA0.preimage Subtype.val_injective.injOn
  have htailConv : TendstoUniformlyOn
      (fun t : Finset {b : ActiveIndex data x // b ∉ T} => fun w =>
        ∑ b ∈ t, activeTerm data x b.1 w)
      H atTop K := by
    dsimp [H]
    exact tendstoUniformlyOn_tsum_of_cofinite_eventually (hweightTail.mul_left CK)
      (show ∀ᶠ b : {b : ActiveIndex data x // b ∉ T} in cofinite,
          ∀ w ∈ K, ‖activeTerm data x b.1 w‖ ≤
            CK * (‖residueCoord data alpha beta x b.1.1.1 b.1.1.2‖ /
              (1 + (poleCoord alpha beta x b.1.1.1 b.1.1.2) ^ 2)) by
        filter_upwards [hA0tail.compl_mem_cofinite] with b hb w hw
        simpa [mul_div_assoc] using htail b.1 hb w hw)
  have htailPartials : ∀ᶠ t : Finset {b : ActiveIndex data x // b ∉ T} in atTop,
      DifferentiableOn ℂ (fun w => ∑ b ∈ t, activeTerm data x b.1 w) (interior K) := by
    filter_upwards [] with t
    exact DifferentiableOn.fun_sum fun b _ w hw => by
      have hne : w ≠ (poleCoord alpha beta x b.1.1.1 b.1.1.2 : ℂ) := by
        intro hwp
        have hwPole : w ∈ complexPoleSet data x := by
          rw [hwp]
          exact ⟨poleCoord alpha beta x b.1.1.1 b.1.1.2, ⟨b.1, rfl⟩, rfl⟩
        have hwU := hKsub (interior_subset hw)
        have hwpEq : w = p := by
          by_contra hnep
          exact hwU.2 ⟨⟨hwPole, Metric.ball_subset_closedBall hwU.1⟩, hnep⟩
        have hpoles :
            poleCoord alpha beta x b.1.1.1 b.1.1.2 =
              poleCoord alpha beta x a.1.1 a.1.2 := by
          exact Complex.ofReal_injective (hwp.symm.trans hwpEq)
        have hpair : b.1.1 = a.1 :=
          poleCoord_injective alpha hAlpha beta hbeta0 x hpoles
        have hactive : b.1 = a := Subtype.ext hpair
        exact b.2 (by simp [T, hactive])
      exact (analyticAt_activeTerm_of_ne_pole data x hx b.1 hne).differentiableAt
        |>.differentiableWithinAt
  have hHdiff :=
    htailConv.tendstoLocallyUniformlyOn.mono interior_subset |>.differentiableOn
      htailPartials isOpen_interior
  have hpInt : p ∈ interior K := mem_of_mem_nhds (interior_mem_nhds.mpr hpK)
  have hHanalytic : AnalyticAt ℂ H p :=
    (hHdiff.analyticOnNhd isOpen_interior) p hpInt
  have hmajorant := hweight.mul_left CK
  have hsum : ∀ w ∈ K, Summable (fun b : ActiveIndex data x => activeTerm data x b w) := by
    intro w hw
    exact Summable.of_norm_bounded_eventually hmajorant <| by
      filter_upwards [hA0.compl_mem_cofinite] with b hb
      simpa [mul_div_assoc] using htail b hb w hw
  have hdecomp : ∀ w ∈ K, activeM data x w = activeTerm data x a w + H w := by
    intro w hw
    have hsplit := (hsum w hw).sum_add_tsum_subtype_compl T
    simpa [activeM, H, T] using hsplit.symm
  let numerator : ℂ → ℂ := fun w =>
    residueCoord data alpha beta x a.1.1 a.1.2 * w / p + (w - p) * H w
  refine ⟨numerator, ?_, ?_, ?_⟩
  · dsimp [numerator]
    exact ((analyticAt_const.mul analyticAt_id).div_const).add
      ((analyticAt_id.sub analyticAt_const).mul hHanalytic)
  · dsimp [numerator]
    change residueCoord data alpha beta x a.1.1 a.1.2 * p / p +
      (p - p) * H p = residueCoord data alpha beta x a.1.1 a.1.2
    field_simp [hp0]
    simp
  · have hKevent : ∀ᶠ w in nhdsWithin p {w : ℂ | w ≠ p}, w ∈ K :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds hpK
    filter_upwards [hKevent, self_mem_nhdsWithin] with w hwK hwp
    have hdecompw := hdecomp w hwK
    dsimp [numerator]
    rw [hdecompw]
    change
      residueCoord data alpha beta x a.1.1 a.1.2 *
          (w / (p * (w - p))) + H w =
        (residueCoord data alpha beta x a.1.1 a.1.2 * w / p + (w - p) * H w) /
          (w - p)
    have hwp' : w - p ≠ 0 := sub_ne_zero.mpr (by simpa [p] using hwp)
    field_simp [hp0, hwp']

end Theorem12.ScaffoldAxioms

namespace Theorem12.Internal

/- Proof idea: isolate the selected pole using injectivity, split `activeM` into that term and
an analytic tail, define the numerator without evaluating an inverse at the pole, and package it. -/
private theorem exists_simplePoleFactorData {alpha : ℝ} {beta : ℚ}
    {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f)
    (x : AddCircle (1 : ℝ)) (hAlpha : Irrational alpha) (hbeta0 : beta ≠ 0)
    (hx : AnalyticParameter data x) (a : ActiveIndex data x) :
    Nonempty (SimplePoleFactorData data x a) := by
  rcases Theorem12.ScaffoldAxioms.series_018_exists_simplePoleFactorFields
      data x hAlpha hbeta0 hx a with ⟨numerator, hanalytic, hvalue, heq⟩
  exact ⟨⟨numerator, hanalytic, hvalue, heq⟩⟩

/- Proof idea: obtain `exists_simplePoleFactorData` and apply the punctured factorization criterion;
its analytic numerator has the nonzero active residue value, giving exact integer order `-1`. -/
theorem meromorphicOrderAt_activeM_pole {alpha : ℝ} {beta : ℚ}
    {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f)
    (x : AddCircle (1 : ℝ)) (hAlpha : Irrational alpha) (hbeta0 : beta ≠ 0)
    (hx : AnalyticParameter data x) (a : ActiveIndex data x) :
    meromorphicOrderAt (activeM data x)
      (poleCoord alpha beta x a.1.1 a.1.2 : ℂ) = (-1 : WithTop ℤ) := by
  let p : ℂ := (poleCoord alpha beta x a.1.1 a.1.2 : ℂ)
  obtain ⟨factor⟩ := exists_simplePoleFactorData data x hAlpha hbeta0 hx a
  have hmer : MeromorphicAt (activeM data x) p :=
    (meromorphicOn_activeM data x hx).1 p (Set.mem_univ p)
  apply (meromorphicOrderAt_eq_int_iff hmer).2
  refine ⟨factor.numerator, factor.analyticAt_numerator, ?_, ?_⟩
  · rw [factor.numerator_at_pole]
    exact a.2
  · filter_upwards [factor.eventuallyEq_punctured] with z hz
    rw [hz]
    simp only [zpow_neg, zpow_one, smul_eq_mul]
    change factor.numerator z / (z - (poleCoord alpha beta x a.1.1 a.1.2 : ℂ)) =
      (z - p)⁻¹ * factor.numerator z
    simp [p, div_eq_mul_inv, mul_comm]

/- Proof idea: use analyticity off `complexPoleSet` in the forward direction; in the reverse
direction choose the unique active index and apply the exact order `-1` theorem. -/
theorem activeM_hasPoleAt_iff {alpha : ℝ} {beta : ℚ} {S : Set ℝ} {f : ℝ → ℂ}
    (data : PositiveInputData alpha beta S f) (x : AddCircle (1 : ℝ))
    (hAlpha : Irrational alpha) (hbeta0 : beta ≠ 0) (hx : AnalyticParameter data x)
    (z : ℂ) :
    meromorphicOrderAt (activeM data x) z < (0 : WithTop ℤ) ↔
      z ∈ complexPoleSet data x := by
  constructor
  · intro hneg
    by_contra hz
    have hzmem : z ∈ Set.univ \ complexPoleSet data x := ⟨Set.mem_univ z, hz⟩
    have hopen : IsOpen (Set.univ \ complexPoleSet data x) :=
      IsOpen.sdiff isOpen_univ (isClosed_complexPoleSet data x hx)
    have hanWithin := (meromorphicOn_activeM data x hx).2 z hzmem
    have han : AnalyticAt ℂ (activeM data x) z := by
      rw [← analyticWithinAt_univ]
      exact hanWithin.mono_of_mem_nhdsWithin (by simpa using hopen.mem_nhds hzmem)
    exact (not_lt_of_ge han.meromorphicOrderAt_nonneg) hneg
  · rintro ⟨p, ⟨a, rfl⟩, rfl⟩
    rw [meromorphicOrderAt_activeM_pole data x hAlpha hbeta0 hx a]
    exact WithTop.coe_lt_coe.mpr (neg_one_lt_zero : (-1 : ℤ) < 0)

/- Proof idea: combine global meromorphicity, one genuine simple pole for nontriviality,
finite integer orders, and divisor local finiteness to fill the generic counting structure. -/
theorem activeM_countingData {alpha : ℝ} {beta : ℚ} {S : Set ℝ} {f : ℝ → ℂ}
    (data : PositiveInputData alpha beta S f) (x : AddCircle (1 : ℝ))
    (hAlpha : Irrational alpha) (hbeta0 : beta ≠ 0) (hx : AnalyticParameter data x)
    (hactive : Nonempty (ActiveIndex data x)) :
    Nonempty (Theorem12.Generic.MeromorphicCountingData (activeM data x)) := by
  classical
  let F : ℂ → ℂ := activeM data x
  have hmer : MeromorphicOn F Set.univ := (meromorphicOn_activeM data x hx).1
  obtain ⟨a⟩ := hactive
  let p : ℂ := (poleCoord alpha beta x a.1.1 a.1.2 : ℂ)
  have hpOrder : meromorphicOrderAt F p = (-1 : WithTop ℤ) := by
    exact meromorphicOrderAt_activeM_pole data x hAlpha hbeta0 hx a
  have hpFinite : meromorphicOrderAt F p ≠ (⊤ : WithTop ℤ) := by
    rw [hpOrder]
    exact WithTop.coe_ne_top
  have horderFinite : ∀ z : ℂ, meromorphicOrderAt F z ≠ (⊤ : WithTop ℤ) := by
    have hall :=
      (hmer.exists_meromorphicOrderAt_ne_top_iff_forall_mem isConnected_univ).1
        ⟨p, Set.mem_univ p, hpFinite⟩
    exact fun z => hall z (Set.mem_univ z)
  let ord : ℂ → ℤ := fun z => (meromorphicOrderAt F z).untop₀
  refine ⟨⟨hmer, horderFinite, ord, ?_, ?_⟩⟩
  · intro z
    dsimp [ord]
    exact WithTop.coe_untop₀_of_ne_top (horderFinite z)
  · intro R
    have hmerBall : MeromorphicOn F (Metric.closedBall (0 : ℂ) R) :=
      fun z _ => hmer z (Set.mem_univ z)
    have hdivFinite :
        (MeromorphicOn.divisor F (Metric.closedBall (0 : ℂ) R)).support.Finite :=
      (MeromorphicOn.divisor F (Metric.closedBall (0 : ℂ) R)).finiteSupport
        (isCompact_closedBall (0 : ℂ) R)
    refine hdivFinite.subset ?_
    rintro z ⟨hzord, hzR⟩
    rw [Function.mem_support, MeromorphicOn.divisor_apply hmerBall hzR]
    exact hzord

end Theorem12.Internal
