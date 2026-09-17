import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.UniformSpace.UniformApproximation
import PeriodicWeakGapsHD.HigherDim.SmallPeaks
import PeriodicWeakGapsHD.HigherDim.EscapingEnumeration

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Topology ENNReal FourierTransform

namespace SpectralGapsPrelim.HigherDim

/-!
Recursive corrections, weighted limits, and the final higher-dimensional theorem.
-/

theorem finite_set_case {d : ℕ} (hd_pos : 0 < d)
    {A Lambda : Set (E d)} {alpha : ℝ} {x0 : E d}
    (hA : AContextHD d A)
    (halpha : AlphaLeDimHalf d alpha)
    (hLambda_fin : Lambda.Finite)
    (hx0 : x0 ∉ Lambda) :
    ∃ f P : E d → ℂ,
      WeightedFourierWitness alpha A f P ∧
      Continuous f ∧
      f x0 = 1 ∧
      ∀ lambda ∈ Lambda, f lambda = 0 := by
  classical
  have hE : ∀ e ∈ hLambda_fin.toFinset, e ≠ x0 := by
    intro e he heq
    have heLambda : e ∈ Lambda := (finite_toFinset_mem hLambda_fin e).mp he
    rw [heq] at heLambda
    exact hx0 heLambda
  obtain ⟨f, P, hW, hf_cont, hf_x0, hf_zero, _hsmall, _hnorm⟩ :=
    exists_small_peak_with_finite_zeros (d := d) hd_pos
      (A := A) (K := ∅) (alpha := alpha) (y := x0) (eps := 1)
      (E0 := hLambda_fin.toFinset) hA halpha isCompact_empty
      (by simp) hE zero_lt_one
  refine ⟨f, P, hW, hf_cont, hf_x0, ?_⟩
  intro lambda hlambda
  exact hf_zero lambda ((finite_toFinset_mem hLambda_fin lambda).mpr hlambda)

private lemma previousZeroSet_not_mem_current_aux {d : ℕ}
    {lambda : ℕ → E d} {x0 : E d}
    (hlambda_inj : Function.Injective lambda)
    (hx0 : ∀ n, x0 ≠ lambda n) (n : ℕ) :
    lambda n ∉ insert x0 ((Finset.range n).image lambda) := by
  classical
  intro hmem
  rw [Finset.mem_insert] at hmem
  rcases hmem with hcurrent_x0 | hcurrent_prev
  · exact hx0 n hcurrent_x0.symm
  · rcases Finset.mem_image.mp hcurrent_prev with ⟨j, hj, hcurrent_j⟩
    exact Nat.ne_of_lt (Finset.mem_range.mp hj) (hlambda_inj hcurrent_j)

private lemma weightedNorm_smul_lt_aux {d : ℕ}
    {A : Set (E d)} {alpha : ℝ}
    {P : E d → ℂ} {a : ℂ} {eps : ℝ}
    (heps : 0 < eps)
    (hP_mem : WeightedEnergyIntegrable alpha A P)
    (hP : weightedNorm alpha A P < eps / (1 + ‖a‖)) :
    weightedNorm alpha A (fun xi => a * P xi) < eps := by
  have hden_pos : 0 < 1 + ‖a‖ := by positivity
  have hmul :
      (1 + ‖a‖) * weightedNorm alpha A P < eps := by
    calc
      (1 + ‖a‖) * weightedNorm alpha A P
          < (1 + ‖a‖) * (eps / (1 + ‖a‖)) :=
            mul_lt_mul_of_pos_left hP hden_pos
      _ = eps := by field_simp [ne_of_gt hden_pos]
  have hnorm_nonneg : 0 ≤ weightedNorm alpha A P := by
    unfold weightedNorm
    exact ENNReal.toReal_nonneg
  have hle :
      ‖a‖ * weightedNorm alpha A P
        ≤ (1 + ‖a‖) * weightedNorm alpha A P := by
    exact mul_le_mul_of_nonneg_right
      (by nlinarith [norm_nonneg a]) hnorm_nonneg
  exact lt_of_le_of_lt (le_trans (weightedNorm_smul_le a hP_mem) hle) hmul

private lemma norm_mul_lt_aux {z w : ℂ} {eps : ℝ}
    (heps : 0 < eps)
    (hw : ‖w‖ < eps / (1 + ‖z‖)) :
    ‖z * w‖ < eps := by
  rw [norm_mul]
  have hden_pos : 0 < 1 + ‖z‖ := by positivity
  have hmul :
      (1 + ‖z‖) * ‖w‖ < eps := by
    calc
      (1 + ‖z‖) * ‖w‖
          < (1 + ‖z‖) * (eps / (1 + ‖z‖)) :=
            mul_lt_mul_of_pos_left hw hden_pos
      _ = eps := by field_simp [ne_of_gt hden_pos]
  have hle : ‖z‖ * ‖w‖ ≤ (1 + ‖z‖) * ‖w‖ := by
    exact mul_le_mul_of_nonneg_right
      (by nlinarith [norm_nonneg z]) (norm_nonneg w)
  exact lt_of_le_of_lt hle hmul

private theorem exists_recursive_correction_atom {d : ℕ} (hd_pos : 0 < d)
    {A : Set (E d)} {alpha : ℝ} {x0 : E d}
    {lambda : ℕ → E d}
    (hA : AContextHD d A)
    (halpha : AlphaLeDimHalf d alpha)
    (hlambda_inj : Function.Injective lambda)
    (hx0 : ∀ n, x0 ≠ lambda n)
    (g0 : E d → ℂ) (qPrev : ℕ → E d → ℂ) (n : ℕ) :
    ∃ qn Qn : E d → ℂ,
      WeightedFourierWitness alpha A qn Qn ∧
      qn x0 = 0 ∧
      (∀ j, j < n → qn (lambda j) = 0) ∧
      partialSum g0 qPrev n (lambda n) + qn (lambda n) = 0 ∧
      weightedNorm alpha A Qn < (1 / 2 : ℝ) ^ (n + 1) ∧
      (∀ x ∈ correctionCompact lambda n,
        ‖qn x‖ < (1 / 2 : ℝ) ^ (n + 1)) := by
  classical
  let a : ℂ := -partialSum g0 qPrev n (lambda n)
  let eta : ℝ := (1 / 2 : ℝ) ^ (n + 1)
  let eps : ℝ := eta / (1 + ‖a‖)
  have heta : 0 < eta := by
    unfold eta
    positivity
  have heps : 0 < eps := by
    exact div_pos heta (by positivity)
  have hE :
      ∀ e ∈ insert x0 ((Finset.range n).image lambda),
        e ≠ lambda n := by
    intro e he heq
    have hnot := previousZeroSet_not_mem_current_aux hlambda_inj hx0 n
    exact hnot (by simpa [heq] using he)
  obtain ⟨p, P, hW, _hp_cont, hp_y, hp_zero, hp_small, hP_small⟩ :=
    exists_small_peak_with_finite_zeros (d := d) hd_pos
      (A := A) (K := correctionCompact lambda n) (alpha := alpha)
      (y := lambda n) (eps := eps)
      (E0 := insert x0 ((Finset.range n).image lambda))
      hA halpha (correctionCompact_isCompact lambda n)
      (lambda_not_mem_correctionCompact lambda n) hE heps
  refine ⟨fun x => a * p x, fun xi => a * P xi, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact WeightedFourierWitness.smul a hW
  · have hx0_mem : x0 ∈ insert x0 ((Finset.range n).image lambda) := by
      simp
    simp [hp_zero x0 hx0_mem]
  · intro j hj
    have hj_mem : lambda j ∈ insert x0 ((Finset.range n).image lambda) := by
      simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_range]
      exact Or.inr ⟨j, hj, rfl⟩
    simp [hp_zero (lambda j) hj_mem]
  · simp [a, hp_y]
  · exact weightedNorm_smul_lt_aux heta hW.side.weightedMemLp hP_small
  · intro x hx
    exact norm_mul_lt_aux heta (hp_small x hx)

private noncomputable def recursiveCorrectionAtom {d : ℕ} (hd_pos : 0 < d)
    {A : Set (E d)} {alpha : ℝ} {x0 : E d}
    {lambda : ℕ → E d}
    (hA : AContextHD d A)
    (halpha : AlphaLeDimHalf d alpha)
    (hlambda_inj : Function.Injective lambda)
    (hx0 : ∀ n, x0 ≠ lambda n)
    (g0 : E d → ℂ) (qPrev : ℕ → E d → ℂ) (n : ℕ) :
    (E d → ℂ) × (E d → ℂ) :=
  let h := exists_recursive_correction_atom hd_pos
    hA halpha hlambda_inj hx0 g0 qPrev n
  (Classical.choose h, Classical.choose (Classical.choose_spec h))

private lemma recursiveCorrectionAtom_spec {d : ℕ} (hd_pos : 0 < d)
    {A : Set (E d)} {alpha : ℝ} {x0 : E d}
    {lambda : ℕ → E d}
    (hA : AContextHD d A)
    (halpha : AlphaLeDimHalf d alpha)
    (hlambda_inj : Function.Injective lambda)
    (hx0 : ∀ n, x0 ≠ lambda n)
    (g0 : E d → ℂ) (qPrev : ℕ → E d → ℂ) (n : ℕ) :
    let atom := recursiveCorrectionAtom hd_pos
      hA halpha hlambda_inj hx0 g0 qPrev n
    WeightedFourierWitness alpha A atom.1 atom.2 ∧
      atom.1 x0 = 0 ∧
      (∀ j, j < n → atom.1 (lambda j) = 0) ∧
      partialSum g0 qPrev n (lambda n) + atom.1 (lambda n) = 0 ∧
      weightedNorm alpha A atom.2 < (1 / 2 : ℝ) ^ (n + 1) ∧
      (∀ x ∈ correctionCompact lambda n,
        ‖atom.1 x‖ < (1 / 2 : ℝ) ^ (n + 1)) := by
  classical
  unfold recursiveCorrectionAtom
  exact Classical.choose_spec
    (Classical.choose_spec
      (exists_recursive_correction_atom hd_pos
        hA halpha hlambda_inj hx0 g0 qPrev n))

private noncomputable def recursiveCorrectionSeq {d : ℕ} (hd_pos : 0 < d)
    {A : Set (E d)} {alpha : ℝ} {x0 : E d}
    {lambda : ℕ → E d}
    (hA : AContextHD d A)
    (halpha : AlphaLeDimHalf d alpha)
    (hlambda_inj : Function.Injective lambda)
    (hx0 : ∀ n, x0 ≠ lambda n)
    (g0 : E d → ℂ) :
    ℕ → (E d → ℂ) × (E d → ℂ) :=
  WellFounded.fix Nat.lt_wfRel.wf (fun n rec =>
    let qPrev : ℕ → E d → ℂ := fun r =>
      if h : r < n then (rec r h).1 else 0
    recursiveCorrectionAtom hd_pos hA halpha hlambda_inj hx0 g0 qPrev n)

private lemma recursiveCorrectionSeq_eq {d : ℕ} (hd_pos : 0 < d)
    {A : Set (E d)} {alpha : ℝ} {x0 : E d}
    {lambda : ℕ → E d}
    (hA : AContextHD d A)
    (halpha : AlphaLeDimHalf d alpha)
    (hlambda_inj : Function.Injective lambda)
    (hx0 : ∀ n, x0 ≠ lambda n)
    (g0 : E d → ℂ) (n : ℕ) :
    recursiveCorrectionSeq hd_pos hA halpha hlambda_inj hx0 g0 n =
      recursiveCorrectionAtom hd_pos hA halpha hlambda_inj hx0 g0
        (fun r => if _ : r < n then
          (recursiveCorrectionSeq hd_pos hA halpha hlambda_inj hx0 g0 r).1
        else 0)
        n := by
  rw [recursiveCorrectionSeq]
  rw [WellFounded.fix_eq]

private lemma partialSum_if_lt_eq {d : ℕ}
    {g0 : E d → ℂ} {q : ℕ → E d → ℂ} {n : ℕ} {x : E d} :
    partialSum g0 (fun r => if _ : r < n then q r else 0) n x =
      partialSum g0 q n x := by
  unfold partialSum
  congr 1
  refine Finset.sum_congr rfl ?_
  intro r hr
  have hlt : r < n := by
    simpa using hr
  simp [hlt]

theorem recursive_corrections {d : ℕ} (hd_pos : 0 < d)
    {A : Set (E d)} {alpha : ℝ} {x0 : E d}
    {lambda : ℕ → E d}
    (hA : AContextHD d A)
    (halpha : AlphaLeDimHalf d alpha)
    (hlambda_inj : Function.Injective lambda)
    (hlambda_escape : Tendsto (fun n => ‖lambda n‖) atTop atTop)
    (hx0 : ∀ n, x0 ≠ lambda n) :
    ∃ g0 G0 : E d → ℂ,
    ∃ q Q : ℕ → E d → ℂ,
      WeightedFourierWitness alpha A g0 G0 ∧
      (∀ n, WeightedFourierWitness alpha A (q n) (Q n)) ∧
      g0 x0 = 1 ∧
      (∀ n, q n x0 = 0) ∧
      (∀ n j, j < n → q n (lambda j) = 0) ∧
      (∀ n, partialSum g0 q n x0 = 1) ∧
      (∀ n j, j < n → partialSum g0 q n (lambda j) = 0) ∧
      (∀ n,
        weightedNorm alpha A (Q n) < (1 / 2 : ℝ) ^ (n + 1)) ∧
      (∀ K : Set (E d), IsCompact K →
        ∀ᶠ n in atTop,
          ∀ x ∈ K, ‖q n x‖ < (1 / 2 : ℝ) ^ (n + 1)) := by
  classical
  obtain ⟨g0, G0, h0, _hg0_cont, hg0_x0, _hg0_zero, _hg0_small, _hG0_small⟩ :=
    exists_small_peak_with_finite_zeros (d := d) hd_pos
      (A := A) (K := ∅) (alpha := alpha) (y := x0) (eps := 1)
      (E0 := (∅ : Finset (E d))) hA halpha isCompact_empty
      (by simp) (by simp) zero_lt_one
  let seq := recursiveCorrectionSeq hd_pos hA halpha hlambda_inj hx0 g0
  let q : ℕ → E d → ℂ := fun n => (seq n).1
  let Q : ℕ → E d → ℂ := fun n => (seq n).2
  have hseq_spec :
      ∀ n,
        WeightedFourierWitness alpha A (q n) (Q n) ∧
        q n x0 = 0 ∧
        (∀ j, j < n → q n (lambda j) = 0) ∧
        partialSum g0 (fun r => if _ : r < n then q r else 0) n
            (lambda n) + q n (lambda n) = 0 ∧
        weightedNorm alpha A (Q n) < (1 / 2 : ℝ) ^ (n + 1) ∧
        (∀ x ∈ correctionCompact lambda n,
          ‖q n x‖ < (1 / 2 : ℝ) ^ (n + 1)) := by
    intro n
    let qPrev : ℕ → E d → ℂ := fun r => if _ : r < n then q r else 0
    have hspec :=
      recursiveCorrectionAtom_spec hd_pos hA halpha hlambda_inj hx0 g0 qPrev n
    have heq := recursiveCorrectionSeq_eq hd_pos hA halpha hlambda_inj hx0 g0 n
    change
      WeightedFourierWitness alpha A
          (recursiveCorrectionSeq hd_pos hA halpha hlambda_inj hx0 g0 n).1
          (recursiveCorrectionSeq hd_pos hA halpha hlambda_inj hx0 g0 n).2 ∧
        (recursiveCorrectionSeq hd_pos hA halpha hlambda_inj hx0 g0 n).1 x0 = 0 ∧
        (∀ j, j < n →
          (recursiveCorrectionSeq hd_pos hA halpha hlambda_inj hx0 g0 n).1
            (lambda j) = 0) ∧
        partialSum g0 qPrev n (lambda n) +
            (recursiveCorrectionSeq hd_pos hA halpha hlambda_inj hx0 g0 n).1
              (lambda n) = 0 ∧
        weightedNorm alpha A
            (recursiveCorrectionSeq hd_pos hA halpha hlambda_inj hx0 g0 n).2 <
          (1 / 2 : ℝ) ^ (n + 1) ∧
        (∀ x ∈ correctionCompact lambda n,
          ‖(recursiveCorrectionSeq hd_pos hA halpha hlambda_inj hx0 g0 n).1 x‖ <
            (1 / 2 : ℝ) ^ (n + 1))
    rw [heq]
    simpa [qPrev, q, Q, seq] using hspec
  have hq : ∀ n, WeightedFourierWitness alpha A (q n) (Q n) := by
    intro n
    exact (hseq_spec n).1
  have hq_x0 : ∀ n, q n x0 = 0 := by
    intro n
    exact (hseq_spec n).2.1
  have hq_prev : ∀ n j, j < n → q n (lambda j) = 0 := by
    intro n j hj
    exact (hseq_spec n).2.2.1 j hj
  have hcancel : ∀ n,
      partialSum g0 q n (lambda n) + q n (lambda n) = 0 := by
    intro n
    have h := (hseq_spec n).2.2.2.1
    rw [partialSum_if_lt_eq] at h
    exact h
  have hpartial_x0 : ∀ n, partialSum g0 q n x0 = 1 := by
    intro n
    unfold partialSum
    have hsum : (Finset.range n).sum (fun r => q r x0) = 0 := by
      exact Finset.sum_eq_zero fun r _hr => hq_x0 r
    simp [hsum, hg0_x0]
  have hpartial_lambda :
      ∀ n j, j < n → partialSum g0 q n (lambda j) = 0 := by
    intro n
    induction n with
    | zero =>
        intro j hj
        exact (Nat.not_lt_zero j hj).elim
    | succ n ih =>
        intro j hj
        by_cases hjn : j = n
        · subst j
          have hc := hcancel n
          unfold partialSum at hc ⊢
          rw [Finset.sum_range_succ]
          rw [← add_assoc]
          exact hc
        · have hjn_lt : j < n :=
            Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hj) hjn
          have hprev := ih j hjn_lt
          have hnew := hq_prev n j hjn_lt
          unfold partialSum at hprev ⊢
          rw [Finset.sum_range_succ]
          rw [hnew]
          simpa [add_assoc] using hprev
  have hnorm : ∀ n,
      weightedNorm alpha A (Q n) < (1 / 2 : ℝ) ^ (n + 1) := by
    intro n
    exact (hseq_spec n).2.2.2.2.1
  have hcompact :
      ∀ K : Set (E d), IsCompact K →
        ∀ᶠ n in atTop,
          ∀ x ∈ K, ‖q n x‖ < (1 / 2 : ℝ) ^ (n + 1) := by
    intro K hK
    filter_upwards [correctionCompact_eventually_contains_compact
      hlambda_escape hK] with n hn x hx
    exact (hseq_spec n).2.2.2.2.2 x (hn hx)
  exact
    ⟨g0, G0, q, Q, h0, hq, hg0_x0, hq_x0, hq_prev,
      hpartial_x0, hpartial_lambda, hnorm, hcompact⟩

theorem previousZeroSet_not_mem_current {d : ℕ}
    {lambda : ℕ → E d} {x0 : E d}
    (hlambda_inj : Function.Injective lambda)
    (hx0 : ∀ n, x0 ≠ lambda n) (n : ℕ) :
    lambda n ∉ insert x0 ((Finset.range n).image lambda) := by
  exact previousZeroSet_not_mem_current_aux hlambda_inj hx0 n

theorem currentPoint_not_mem_zeroFinset_of_injective {d : ℕ}
    {lambda : ℕ → E d} {x0 : E d}
    (hlambda_inj : Function.Injective lambda)
    (hx0 : ∀ n, x0 ≠ lambda n) (n : ℕ) :
    lambda n ∉ insert x0 ((Finset.range n).image lambda) := by
  exact previousZeroSet_not_mem_current hlambda_inj hx0 n

theorem weightedNorm_smul_lt_of_lt_div_one_add_norm {d : ℕ}
    {A : Set (E d)} {alpha : ℝ}
    {P : E d → ℂ} {a : ℂ} {eps : ℝ}
    (heps : 0 < eps)
    (hP_mem : WeightedEnergyIntegrable alpha A P)
    (hP : weightedNorm alpha A P < eps / (1 + ‖a‖)) :
    weightedNorm alpha A (fun xi => a * P xi) < eps := by
  exact weightedNorm_smul_lt_aux heps hP_mem hP

theorem norm_mul_lt_of_lt_div_one_add_norm {z w : ℂ} {eps : ℝ}
    (heps : 0 < eps)
    (hw : ‖w‖ < eps / (1 + ‖z‖)) :
    ‖z * w‖ < eps := by
  exact norm_mul_lt_aux heps hw

theorem weightedNorm_tail_geometric_bound {d : ℕ}
    {A : Set (E d)} {alpha : ℝ}
    {Q : ℕ → E d → ℂ}
    (hQ_mem : ∀ n, WeightedEnergyIntegrable alpha A (Q n))
    (h_norm :
      ∀ n, weightedNorm alpha A (Q n) < (1 / 2 : ℝ) ^ (n + 1)) :
    ∀ m n : ℕ, m ≤ n →
      weightedNorm alpha A
        (fun xi => (Finset.Ico m n).sum (fun r => Q r xi))
        ≤ (Finset.Ico m n).sum (fun r => (1 / 2 : ℝ) ^ (r + 1)) := by
  intro m n _hmn
  calc
    weightedNorm alpha A
        (fun xi => (Finset.Ico m n).sum (fun r => Q r xi))
        ≤ (Finset.Ico m n).sum (fun r => weightedNorm alpha A (Q r)) := by
          exact weightedNorm_finset_sum_le (Finset.Ico m n) Q
            (fun r _hr => hQ_mem r)
    _ ≤ (Finset.Ico m n).sum (fun r => (1 / 2 : ℝ) ^ (r + 1)) := by
          exact Finset.sum_le_sum fun r _hr => le_of_lt (h_norm r)

theorem partialFourierWitness {d : ℕ}
    {A : Set (E d)} {alpha : ℝ}
    {g0 G0 : E d → ℂ} {q Q : ℕ → E d → ℂ}
    (h0 : WeightedFourierWitness alpha A g0 G0)
    (hq : ∀ n, WeightedFourierWitness alpha A (q n) (Q n))
    (n : ℕ) :
    WeightedFourierWitness alpha A
      (partialSum g0 q n) (partialFourier G0 Q n) := by
  have hsum :
      WeightedFourierWitness alpha A
        (fun x => (Finset.range n).sum (fun r => q r x))
        (fun xi => (Finset.range n).sum (fun r => Q r xi)) :=
    WeightedFourierWitness.finset_sum (Finset.range n)
      (fun r _hr => hq r)
  have hadd := WeightedFourierWitness.add h0 hsum
  change
    WeightedFourierWitness alpha A
      (fun x => g0 x + (Finset.range n).sum (fun r => q r x))
      (fun xi => G0 xi + (Finset.range n).sum (fun r => Q r xi))
  exact hadd

private lemma weightedNorm_eq_norm_toLp {d : ℕ}
    {A : Set (E d)} {alpha : ℝ} {P : E d → ℂ}
    (hP_mem : WeightedEnergyIntegrable alpha A P) :
    weightedNorm alpha A P =
      ‖hP_mem.toLp P‖ := by
  rw [weightedNorm, Lp.norm_toLp]

private lemma aestronglyMeasurable_norm_rpow_hd {d : ℕ}
    (q : ℝ) (μ : Measure (E d)) :
    AEStronglyMeasurable (fun xi : E d => ‖xi‖ ^ q) μ := by
  refine (measurable_of_continuousOn_compl_singleton (0 : E d) ?_).aestronglyMeasurable
  intro x hx
  exact
    (continuousAt_id.norm.rpow_const
      (Or.inl (norm_ne_zero_iff.mpr hx))).continuousWithinAt

private lemma aestronglyMeasurable_sobolevWeight_hd {d : ℕ}
    (alpha : ℝ) (μ : Measure (E d)) :
    AEStronglyMeasurable (fun xi : E d => sobolevWeight alpha xi) μ := by
  unfold sobolevWeight sobolevPower
  split_ifs
  · fun_prop
  · exact
      aestronglyMeasurable_const.add
        (aestronglyMeasurable_norm_rpow_hd (d := d) (2 * alpha) μ)

private lemma aemeasurable_weightedDensity_hd {d : ℕ}
    (alpha : ℝ) (μ : Measure (E d)) :
    AEMeasurable
      (fun xi : E d => ENNReal.ofReal (sobolevWeight alpha xi)) μ := by
  exact
    ENNReal.measurable_ofReal.comp_aemeasurable
      (aestronglyMeasurable_sobolevWeight_hd alpha μ).aemeasurable

private lemma volume_restrict_spectrum_absolutelyContinuous_weightedMeasure
    {d : ℕ} {A : Set (E d)} {alpha : ℝ} :
    volume.restrict (spectrum A) ≪ weightedMeasure alpha A := by
  unfold weightedMeasure
  refine
    withDensity_absolutelyContinuous'
      (aemeasurable_weightedDensity_hd alpha
        (volume.restrict (spectrum A))) ?_
  exact Eventually.of_forall fun xi => by
    rw [ENNReal.ofReal_ne_zero_iff]
    exact sobolevWeight_pos alpha xi

private lemma weightedMeasure_ae_mem_spectrum {d : ℕ}
    {A : Set (E d)} {alpha : ℝ}
    (hA : AContextHD d A) :
    ∀ᵐ xi ∂weightedMeasure alpha A, xi ∈ spectrum A := by
  unfold weightedMeasure
  rw [ae_withDensity_iff'
    (aemeasurable_weightedDensity_hd alpha
      (volume.restrict (spectrum A)))]
  filter_upwards [ae_restrict_mem hA.measurableSet_spectrum] with xi hxi _hdens
  exact hxi

private lemma weightedLimitIndicator_ae {d : ℕ}
    {A : Set (E d)} {alpha : ℝ}
    (hA : AContextHD d A)
    (u : Lp (α := E d) ℂ 2 (weightedMeasure alpha A)) :
    (spectrum A).indicator (u : E d → ℂ)
      =ᵐ[weightedMeasure alpha A] (u : E d → ℂ) := by
  filter_upwards [weightedMeasure_ae_mem_spectrum (A := A) (alpha := alpha) hA] with xi hxi
  simp [hxi]

private lemma weightedLimitIndicator_aestronglyMeasurable {d : ℕ}
    {A : Set (E d)} {alpha : ℝ}
    (hA : AContextHD d A)
    (u : Lp (α := E d) ℂ 2 (weightedMeasure alpha A)) :
    AEStronglyMeasurable
      ((spectrum A).indicator (u : E d → ℂ)) volume := by
  have hbase :
      AEStronglyMeasurable (u : E d → ℂ)
        (volume.restrict (spectrum A)) :=
    (Lp.aestronglyMeasurable u).mono_ac
      (volume_restrict_spectrum_absolutelyContinuous_weightedMeasure
        (A := A) (alpha := alpha))
  exact
    (aestronglyMeasurable_indicator_iff hA.measurableSet_spectrum).2 hbase

private lemma weightedLimitIndicator_supported {d : ℕ}
    {A : Set (E d)} {alpha : ℝ}
    (u : Lp (α := E d) ℂ 2 (weightedMeasure alpha A)) :
    SupportedInSpectrumAE A ((spectrum A).indicator (u : E d → ℂ)) := by
  exact Eventually.of_forall fun xi hxi => by
    simp [hxi]

private lemma weightedLimitIndicator_zero {d : ℕ}
    {A : Set (E d)} {alpha : ℝ}
    (u : Lp (α := E d) ℂ 2 (weightedMeasure alpha A)) :
    ∀ xi, xi ∉ spectrum A →
      (spectrum A).indicator (u : E d → ℂ) xi = 0 := by
  intro xi hxi
  simp [hxi]

private lemma weightedPartialLp_eq {d : ℕ}
    {A : Set (E d)} {alpha : ℝ}
    {G0 : E d → ℂ} {Q : ℕ → E d → ℂ}
    (hG0_mem : MemLp G0 2 (weightedMeasure alpha A))
    (hQ_mem : ∀ n, MemLp (Q n) 2 (weightedMeasure alpha A))
    (n : ℕ) :
    (hG0_mem.toLp G0 +
        (Finset.range n).sum
          (fun r => (hQ_mem r).toLp (Q r)) :
        Lp (α := E d) ℂ 2 (weightedMeasure alpha A))
      =ᵐ[weightedMeasure alpha A]
      partialFourier G0 Q n := by
  let μ : Measure (E d) := weightedMeasure alpha A
  let u0 : Lp (α := E d) ℂ 2 μ := hG0_mem.toLp G0
  let u : ℕ → Lp (α := E d) ℂ 2 μ :=
    fun r => (hQ_mem r).toLp (Q r)
  change (u0 + (Finset.range n).sum u)
      =ᵐ[μ] partialFourier G0 Q n
  have hQ_ae :
      ∀ᵐ xi ∂μ,
        ∀ r ∈ Finset.range n,
          u r xi = Q r xi := by
    rw [Filter.eventually_all_finset]
    intro r _hr
    exact MemLp.coeFn_toLp (hQ_mem r)
  filter_upwards
    [Lp.coeFn_add u0 ((Finset.range n).sum u),
     Lp.coeFn_fun_finsetSum (Finset.range n) u,
     MemLp.coeFn_toLp hG0_mem, hQ_ae] with xi h_add h_sum hG0 hQ
  calc
    ((u0 + (Finset.range n).sum u :
        Lp (α := E d) ℂ 2 μ) : E d → ℂ) xi
        = u0 xi +
            (((Finset.range n).sum u :
              Lp (α := E d) ℂ 2 μ) : E d → ℂ) xi := by
            simpa [Pi.add_apply] using h_add
    _ = u0 xi +
          (Finset.range n).sum
            (fun r => u r xi) := by
            rw [h_sum]
    _ = G0 xi +
          (Finset.range n).sum
            (fun r => Q r xi) := by
            rw [hG0]
            congr 1
            exact Finset.sum_congr rfl fun r hr => hQ r hr
    _ = partialFourier G0 Q n xi := by
            rfl

theorem weightedSeriesTendsto_of_geometric_bound {d : ℕ}
    {A : Set (E d)} {alpha : ℝ}
    {g0 G0 : E d → ℂ}
    {q Q : ℕ → E d → ℂ}
    (hA : AContextHD d A)
    (h0 : WeightedFourierWitness alpha A g0 G0)
    (hq : ∀ n, WeightedFourierWitness alpha A (q n) (Q n))
    (h_norm :
      ∀ n, weightedNorm alpha A (Q n) < (1 / 2 : ℝ) ^ (n + 1)) :
    ∃ H : E d → ℂ,
      WeightedFourierSide alpha A H ∧
      (∀ xi, xi ∉ spectrum A → H xi = 0) ∧
      weightedSeriesTendsto alpha A G0 Q H ∧
      Tendsto
        (fun n =>
          eLpNorm
            (fun xi => partialFourier G0 Q n xi - H xi)
            2 volume)
        atTop (nhds 0) := by
  -- First use the finitary tail estimate to show the partial Fourier sums are
  -- Cauchy in the weighted `Lp` space. After choosing an `Lp` limit
  -- representative `Hraw`, set `H := Set.indicator (spectrum A) Hraw`; the
  -- indicator version represents the same weighted class because all partial
  -- sums are supported in `spectrum A` a.e. Finally apply
  -- `weightedL2_tendsto_to_global_L2_tendsto` to obtain global `L2` convergence.
  let μ : Measure (E d) := weightedMeasure alpha A
  let hG0_mem : MemLp G0 2 μ := h0.side.weightedMemLp
  let hQ_mem : ∀ n, MemLp (Q n) 2 μ := fun n => (hq n).side.weightedMemLp
  let u0 : Lp (α := E d) ℂ 2 μ := hG0_mem.toLp G0
  let u : ℕ → Lp (α := E d) ℂ 2 μ :=
    fun n => (hQ_mem n).toLp (Q n)
  have hu_norm : ∀ n, ‖u n‖ ≤ (1 / 2 : ℝ) ^ (n + 1) := by
    intro n
    have hnorm_eq :
        weightedNorm alpha A (Q n) = ‖u n‖ := by
      exact
        weightedNorm_eq_norm_toLp
          (A := A) (alpha := alpha) (P := Q n) (hQ_mem n)
    rw [← hnorm_eq]
    exact le_of_lt (h_norm n)
  have hsummable_half :
      Summable fun n : ℕ => ((1 / 2 : ℝ) ^ (n + 1)) := by
    simpa [pow_succ'] using (summable_geometric_two.mul_left (1 / 2 : ℝ))
  have hu_summable : Summable u :=
    Summable.of_norm_bounded hsummable_half hu_norm
  let uLim : Lp (α := E d) ℂ 2 μ := u0 + ∑' n, u n
  let H : E d → ℂ := (spectrum A).indicator (uLim : E d → ℂ)
  have hH_ae : H =ᵐ[μ] (uLim : E d → ℂ) := by
    simpa [H, μ] using
      weightedLimitIndicator_ae (A := A) (alpha := alpha) hA uLim
  have hH_weighted : MemLp H 2 μ :=
    (Lp.memLp uLim).ae_eq hH_ae.symm
  have hH_aemeas : AEStronglyMeasurable H volume := by
    simpa [H, μ] using
      weightedLimitIndicator_aestronglyMeasurable
        (A := A) (alpha := alpha) hA uLim
  have hH_supported : SupportedInSpectrumAE A H := by
    simpa [H, μ] using
      weightedLimitIndicator_supported (A := A) (alpha := alpha) uLim
  have hH_memL2 : MemLp H 2 volume :=
    weighted_memLp_volume_of_supported hA hH_aemeas hH_supported hH_weighted
  have hH_side : WeightedFourierSide alpha A H :=
    ⟨hH_aemeas, hH_supported, hH_weighted, hH_memL2⟩
  have hH_toLp : hH_weighted.toLp H = uLim := by
    have hcongr :
        hH_weighted.toLp H =
          (Lp.memLp uLim).toLp (uLim : E d → ℂ) :=
      MemLp.toLp_congr hH_weighted (Lp.memLp uLim) hH_ae
    simpa using hcongr
  have hpartial_toLp :
      ∀ n,
        ((partialFourierWitness h0 hq n).side.weightedMemLp).toLp
            (partialFourier G0 Q n)
          =
        u0 + (Finset.range n).sum u := by
    intro n
    have hpartial_ae :
        (u0 + (Finset.range n).sum u :
          Lp (α := E d) ℂ 2 μ)
          =ᵐ[μ] partialFourier G0 Q n := by
      simpa [u0, u, hG0_mem, hQ_mem, μ] using
        weightedPartialLp_eq
          (A := A) (alpha := alpha) (G0 := G0) (Q := Q)
          hG0_mem hQ_mem n
    have hcongr :
        (Lp.memLp (u0 + (Finset.range n).sum u :
          Lp (α := E d) ℂ 2 μ)).toLp
            ((u0 + (Finset.range n).sum u :
              Lp (α := E d) ℂ 2 μ) : E d → ℂ)
          =
        ((partialFourierWitness h0 hq n).side.weightedMemLp).toLp
          (partialFourier G0 Q n) :=
      MemLp.toLp_congr
        (Lp.memLp (u0 + (Finset.range n).sum u :
          Lp (α := E d) ℂ 2 μ))
        ((partialFourierWitness h0 hq n).side.weightedMemLp)
        hpartial_ae
    rw [Lp.toLp_coeFn] at hcongr
    exact hcongr.symm
  have hsum_tendsto :
      Tendsto (fun n : ℕ => (Finset.range n).sum u) atTop
        (nhds (∑' n, u n)) :=
    hu_summable.hasSum.tendsto_sum_nat
  have hLp_tendsto :
      Tendsto (fun n : ℕ => u0 + (Finset.range n).sum u) atTop
        (nhds uLim) := by
    simpa [uLim] using tendsto_const_nhds.add hsum_tendsto
  have hdiffLp_tendsto :
      Tendsto
        (fun n : ℕ => (u0 + (Finset.range n).sum u) - uLim)
        atTop (nhds 0) := by
    simpa using
      hLp_tendsto.sub
        (tendsto_const_nhds :
          Tendsto (fun _ : ℕ => uLim) atTop (nhds uLim))
  have hweighted_tendsto :
      Tendsto
        (fun n =>
          eLpNorm
            (fun xi => partialFourier G0 Q n xi - H xi)
            2 μ)
        atTop (nhds 0) := by
    have henorm_tendsto :
        Tendsto
          (fun n : ℕ => ‖(u0 + (Finset.range n).sum u) - uLim‖ₑ)
          atTop (nhds 0) := by
      simpa using hdiffLp_tendsto.enorm
    refine henorm_tendsto.congr' ?_
    refine Eventually.of_forall fun n => ?_
    let hpart_mem :
        MemLp (partialFourier G0 Q n) 2 μ :=
      (partialFourierWitness h0 hq n).side.weightedMemLp
    let diff : E d → ℂ := fun xi => partialFourier G0 Q n xi - H xi
    have hdiff_mem : MemLp diff 2 μ := hpart_mem.sub hH_weighted
    have htoLp_sub :
        hdiff_mem.toLp diff =
          hpart_mem.toLp (partialFourier G0 Q n) -
            hH_weighted.toLp H := by
      exact MemLp.toLp_sub hpart_mem hH_weighted
    calc
      ‖(u0 + (Finset.range n).sum u) - uLim‖ₑ
          = ‖hdiff_mem.toLp diff‖ₑ := by
          rw [htoLp_sub, hpartial_toLp n, hH_toLp]
      _ = eLpNorm diff 2 μ := Lp.enorm_toLp hdiff_mem
      _ = eLpNorm (fun xi => partialFourier G0 Q n xi - H xi) 2 μ := rfl
  have hDiff :
      ∀ n,
        WeightedFourierSide alpha A
          (fun xi => partialFourier G0 Q n xi - H xi) := by
    intro n
    let hpart := (partialFourierWitness h0 hq n).side
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact hpart.aestronglyMeasurable.sub hH_aemeas
    · filter_upwards [hpart.supported, hH_supported] with xi hpart_supp hH_supp hxi
      simp [hpart_supp hxi, hH_supp hxi]
    · exact hpart.weightedMemLp.sub hH_weighted
    · exact hpart.memL2.sub hH_memL2
  refine ⟨H, hH_side, ?_, ?_, ?_⟩
  · simpa [H, μ] using
      weightedLimitIndicator_zero (A := A) (alpha := alpha) uLim
  · simpa [weightedSeriesTendsto, weightedL2Tendsto, μ] using hweighted_tendsto
  · exact
      weightedL2_tendsto_to_global_L2_tendsto
        hA hDiff
        (by simpa [μ] using hweighted_tendsto)

private lemma summable_half_pow_succ :
    Summable fun n : ℕ => ((1 / 2 : ℝ) ^ (n + 1)) := by
  simpa [pow_succ'] using (summable_geometric_two.mul_left (1 / 2 : ℝ))

private lemma tendstoUniformlyOn_correction_tsum_of_geometric_bound {d : ℕ}
    {q : ℕ → E d → ℂ}
    (h_compact :
      ∀ K : Set (E d), IsCompact K →
        ∀ᶠ n in atTop,
          ∀ x ∈ K, ‖q n x‖ < (1 / 2 : ℝ) ^ (n + 1))
    (K : Set (E d)) (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun N x => (Finset.range N).sum (fun n => q n x))
      (fun x => ∑' n, q n x) atTop K := by
  refine
    tendstoUniformlyOn_tsum_nat_eventually
      (u := fun n : ℕ => ((1 / 2 : ℝ) ^ (n + 1)))
      summable_half_pow_succ ?_
  filter_upwards [h_compact K hK] with n hn x hx
  exact le_of_lt (hn x hx)

private lemma tendstoUniformlyOn_partialSum_tsum_of_geometric_bound {d : ℕ}
    {g0 : E d → ℂ} {q : ℕ → E d → ℂ}
    (h_compact :
      ∀ K : Set (E d), IsCompact K →
        ∀ᶠ n in atTop,
          ∀ x ∈ K, ‖q n x‖ < (1 / 2 : ℝ) ^ (n + 1))
    (K : Set (E d)) (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun N x => partialSum g0 q N x)
      (fun x => g0 x + ∑' n, q n x) atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro eps heps
  have hcorr :=
    Metric.tendstoUniformlyOn_iff.mp
      (tendstoUniformlyOn_correction_tsum_of_geometric_bound
        h_compact K hK) eps heps
  filter_upwards [hcorr] with N hN x hx
  have hxN := hN x hx
  simpa [partialSum, dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm,
    add_assoc] using hxN

private lemma continuous_partialSum {d : ℕ}
    {g0 : E d → ℂ} {q : ℕ → E d → ℂ}
    (hg0_cont : Continuous g0)
    (hq_cont : ∀ n, Continuous (q n))
    (n : ℕ) :
    Continuous (fun x => partialSum g0 q n x) := by
  change Continuous (fun x =>
    g0 x + (Finset.range n).sum (fun r => q r x))
  exact
    hg0_cont.add
      (continuous_finsetSum (Finset.range n) (fun r _hr => hq_cont r))

theorem locallyUniformLimit_of_geometric_bound {d : ℕ}
    {g0 : E d → ℂ} {q : ℕ → E d → ℂ}
    (hg0_cont : Continuous g0)
    (hq_cont : ∀ n, Continuous (q n))
    (h_compact :
      ∀ K : Set (E d), IsCompact K →
        ∀ᶠ n in atTop,
          ∀ x ∈ K, ‖q n x‖ < (1 / 2 : ℝ) ^ (n + 1)) :
    ∃ f : E d → ℂ,
      Continuous f ∧
      LocallyUniformLimit (fun n x => partialSum g0 q n x) f := by
  let f : E d → ℂ := fun x => g0 x + ∑' n, q n x
  have hpartial_compact :
      ∀ K : Set (E d), IsCompact K →
        TendstoUniformlyOn (fun n x => partialSum g0 q n x) f atTop K := by
    intro K hK
    simpa [f] using
      tendstoUniformlyOn_partialSum_tsum_of_geometric_bound
        (g0 := g0) (q := q) h_compact K hK
  have hloc :
      TendstoLocallyUniformly (fun n x => partialSum g0 q n x) f atTop := by
    rw [tendstoLocallyUniformly_iff_forall_isCompact]
    intro K hK
    exact hpartial_compact K hK
  have hf_cont : Continuous f :=
    hloc.continuous
      (Frequently.of_forall fun n => continuous_partialSum hg0_cont hq_cont n)
  refine ⟨f, hf_cont, ?_⟩
  intro K hK eps heps
  have hK_unif := Metric.tendstoUniformlyOn_iff.mp (hpartial_compact K hK) eps heps
  filter_upwards [hK_unif] with n hn x hx
  simpa [dist_comm] using hn x hx

private lemma memLp_restrict_closedBall_of_continuous {d : ℕ}
    {f : E d → ℂ} (hf : Continuous f) (R : ℝ) :
    MemLp f 2 (volume.restrict (Metric.closedBall (0 : E d) R)) := by
  let B : Set (E d) := Metric.closedBall (0 : E d) R
  haveI : IsFiniteMeasure (volume.restrict B) :=
    (isFiniteMeasure_restrict).2
      (by
        simpa [B] using
          (measure_closedBall_lt_top
            (μ := (volume : Measure (E d))) (x := (0 : E d)) (r := R)).ne)
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall (0 : E d) R).exists_bound_of_continuousOn
      hf.continuousOn
  refine MemLp.of_bound hf.aestronglyMeasurable.restrict C ?_
  filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
  exact hC x hx

private lemma tendsto_Lp_restrict_closedBall_of_locallyUniform {d : ℕ}
    {F : ℕ → E d → ℂ} {f : E d → ℂ}
    (hF_cont : ∀ n, Continuous (F n))
    (hf_cont : Continuous f)
    (h_loc_unif : LocallyUniformLimit F f)
    (R : ℝ) :
    Tendsto
      (fun n : ℕ =>
        (memLp_restrict_closedBall_of_continuous (hF_cont n) R).toLp
          (F n))
      atTop
      (nhds
        ((memLp_restrict_closedBall_of_continuous hf_cont R).toLp f :
          Lp (α := E d) ℂ 2
            (volume.restrict (Metric.closedBall (0 : E d) R)))) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine Metric.tendsto_atTop.2 ?_
  intro eps heps
  let B : Set (E d) := Metric.closedBall (0 : E d) R
  let scale : ℝ := (volume B ^ (1 / (2 : ℝ))).toReal
  let delta : ℝ := eps / (2 * (scale + 1))
  have hscale_nonneg : 0 ≤ scale := ENNReal.toReal_nonneg
  have hden_pos : 0 < 2 * (scale + 1) := by nlinarith
  have hdelta_pos : 0 < delta := div_pos heps hden_pos
  have hloc := h_loc_unif B (isCompact_closedBall (0 : E d) R) delta hdelta_pos
  rcases eventually_atTop.1 hloc with ⟨N, hN⟩
  refine ⟨N, fun n hnN => ?_⟩
  have hn := hN n hnN
  let μB : Measure (E d) := volume.restrict B
  let hFn_mem := memLp_restrict_closedBall_of_continuous (hF_cont n) R
  let hf_mem := memLp_restrict_closedBall_of_continuous hf_cont R
  let diff : E d → ℂ := F n - f
  have hdiff_mem : MemLp diff 2 μB := hFn_mem.sub hf_mem
  have hdist_le : ∀ x ∈ B, dist (F n x) (f x) ≤ delta := by
    intro x hx
    exact le_of_lt (hn x hx)
  have heLp_le :
      eLpNorm diff 2 μB
        ≤ ENNReal.ofReal delta * volume B ^ (1 / (2 : ℝ)) := by
    have hindicator :=
      eLpNorm_indicator_sub_le_of_dist_bdd
        (μ := volume) (p := (2 : ℝ≥0∞))
        (s := B) (f := F n) (g := f) (c := delta)
        (by simp) measurableSet_closedBall hdelta_pos.le hdist_le
    rw [← eLpNorm_indicator_eq_eLpNorm_restrict
      (p := (2 : ℝ≥0∞)) measurableSet_closedBall]
    simpa [B, μB, diff] using hindicator
  have hvol_lt_top : volume B < ∞ := by
    simpa [B] using
      (measure_closedBall_lt_top
        (μ := (volume : Measure (E d))) (x := (0 : E d)) (r := R))
  have hpow_ne_top : volume B ^ (1 / (2 : ℝ)) ≠ ∞ :=
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hvol_lt_top.ne).ne
  have hright_ne_top :
      ENNReal.ofReal delta * volume B ^ (1 / (2 : ℝ)) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hpow_ne_top
  have hnorm_le : ‖hdiff_mem.toLp diff‖ ≤ delta * scale := by
    calc
      ‖hdiff_mem.toLp diff‖
          = (eLpNorm diff 2 μB).toReal :=
            Lp.norm_toLp diff hdiff_mem
      _ ≤ (ENNReal.ofReal delta * volume B ^ (1 / (2 : ℝ))).toReal :=
            ENNReal.toReal_mono hright_ne_top heLp_le
      _ = delta * scale := by
            simp [scale, ENNReal.toReal_mul,
              ENNReal.toReal_ofReal hdelta_pos.le]
  have hdelta_scale_le : delta * scale ≤ eps / 2 := by
    dsimp [delta]
    calc
      (eps / (2 * (scale + 1))) * scale
          = (eps * scale) / (2 * (scale + 1)) := by ring
      _ ≤ (eps * (scale + 1)) / (2 * (scale + 1)) := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left (by nlinarith) heps.le)
            (le_of_lt hden_pos)
      _ = eps / 2 := by
          field_simp [show scale + 1 ≠ 0 by nlinarith]
  have htoLp_sub :
      hdiff_mem.toLp diff = hFn_mem.toLp (F n) - hf_mem.toLp f := by
    exact MemLp.toLp_sub hFn_mem hf_mem
  have hnorm_lt : ‖hFn_mem.toLp (F n) - hf_mem.toLp f‖ < eps := by
    calc
      ‖hFn_mem.toLp (F n) - hf_mem.toLp f‖
          = ‖hdiff_mem.toLp diff‖ := by rw [← htoLp_sub]
      _ ≤ delta * scale := hnorm_le
      _ ≤ eps / 2 := hdelta_scale_le
      _ < eps := by linarith
  simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using hnorm_lt

theorem continuousInvFourierRep_of_L2_and_locallyUniform {d : ℕ}
    {G : ℕ → E d → ℂ} {s : ℕ → E d → ℂ}
    {H f : E d → ℂ}
    (hH_memL2 : MemLp H 2 volume)
    (h_part : ∀ n, ContinuousInvFourierRep (G n) (s n))
    (h_L2 :
      Tendsto
        (fun n => eLpNorm (fun xi => G n xi - H xi) 2 volume)
        atTop (nhds 0))
    (h_loc : LocallyUniformLimit s f)
    (hf_cont : Continuous f) :
    ContinuousInvFourierRep H f := by
  -- Use continuity of Mathlib's inverse Fourier operator on `Lp`. Restrict the
  -- global `L2` convergence to each closed ball, convert locally uniform
  -- convergence on that ball into local `L2` convergence, use uniqueness of
  -- limits in local `Lp`, then exhaust `E d` by closed balls to obtain the
  -- global a.e. representative equality.
  let Hlp : Lp (α := E d) ℂ 2 volume := hH_memL2.toLp H
  let invH : Lp (α := E d) ℂ 2 volume := 𝓕⁻ Hlp
  let partLp : ℕ → Lp (α := E d) ℂ 2 volume := fun n =>
    (h_part n).P_memL2.toLp (G n)
  let invPart : ℕ → Lp (α := E d) ℂ 2 volume := fun n =>
    𝓕⁻ (partLp n)
  have hpart_tendsto : Tendsto partLp atTop (nhds Hlp) := by
    rw [tendsto_iff_edist_tendsto_0]
    simp only [partLp, Hlp, Lp.edist_toLp_toLp]
    have hsame :
        (fun n => eLpNorm (G n - H) 2 volume) =
          (fun n => eLpNorm (fun xi => G n xi - H xi) 2 volume) := by
      funext n
      congr 1
    rw [hsame]
    exact h_L2
  have hinv_tendsto :
      Tendsto invPart atTop (nhds invH) := by
    simpa [Function.comp_def, invPart, invH] using
      (FourierTransform.continuous_fourierInv.tendsto Hlp).comp hpart_tendsto
  have hball :
      ∀ k : ℕ,
        (invH : E d → ℂ)
          =ᵐ[volume.restrict (Metric.closedBall (0 : E d) (k : ℝ))] f := by
    intro k
    let R : ℝ := (k : ℝ)
    let B : Set (E d) := Metric.closedBall (0 : E d) R
    let μB : Measure (E d) := volume.restrict B
    let restrictCLM :
        Lp (α := E d) ℂ 2 volume →L[ℂ] Lp (α := E d) ℂ 2 μB :=
      LpToLpRestrictCLM (E d) ℂ ℂ volume 2 B
    let f_mem : MemLp f 2 μB :=
      memLp_restrict_closedBall_of_continuous hf_cont R
    let partial_mem : ∀ n, MemLp (s n) 2 μB :=
      fun n =>
        memLp_restrict_closedBall_of_continuous (h_part n).f_cont R
    have hinv_restrict_tendsto :
        Tendsto (fun n : ℕ => restrictCLM (invPart n)) atTop
          (nhds (restrictCLM invH)) := by
      exact restrictCLM.continuous.tendsto invH |>.comp hinv_tendsto
    have hlocal_tendsto :
        Tendsto
          (fun n : ℕ => (partial_mem n).toLp (s n))
          atTop (nhds (f_mem.toLp f)) := by
      simpa [R, B, μB, partial_mem, f_mem] using
        tendsto_Lp_restrict_closedBall_of_locallyUniform
          (F := s) (f := f)
          (fun n => (h_part n).f_cont) hf_cont h_loc R
    have hseq_eq :
        (fun n : ℕ => restrictCLM (invPart n))
          =ᶠ[atTop]
        (fun n : ℕ => (partial_mem n).toLp (s n)) := by
      refine Eventually.of_forall fun n => ?_
      apply Lp.ext
      have hrestrict :
          restrictCLM (invPart n) =ᵐ[μB] invPart n := by
        simpa [restrictCLM, μB, B] using
          (LpToLpRestrictCLM_coeFn
            (X := E d) (F := ℂ) (𝕜 := ℂ) (μ := volume)
            (p := (2 : ℝ≥0∞)) B (invPart n))
      have hinv_ae :
          (invPart n : E d → ℂ) =ᵐ[μB] s n := by
        change ∀ᵐ x ∂μB, (invPart n : E d → ℂ) x = s n x
        simpa [invPart, partLp, μB] using
          ae_restrict_of_ae (ContinuousInvFourierRep.ae_eq_inverse (h_part n))
      have hpartial_toLp :
          (partial_mem n).toLp (s n) =ᵐ[μB] s n :=
        MemLp.coeFn_toLp (partial_mem n)
      exact hrestrict.trans (hinv_ae.trans hpartial_toLp.symm)
    have hinv_as_partial_tendsto :
        Tendsto
          (fun n : ℕ => (partial_mem n).toLp (s n))
          atTop (nhds (restrictCLM invH)) :=
      hinv_restrict_tendsto.congr' hseq_eq
    have hlimit_eq : f_mem.toLp f = restrictCLM invH :=
      tendsto_nhds_unique hlocal_tendsto hinv_as_partial_tendsto
    have hrestrict_invH : restrictCLM invH =ᵐ[μB] invH := by
      simpa [restrictCLM, μB, B] using
        (LpToLpRestrictCLM_coeFn
          (X := E d) (F := ℂ) (𝕜 := ℂ) (μ := volume)
          (p := (2 : ℝ≥0∞)) B invH)
    have hf_toLp : f_mem.toLp f =ᵐ[μB] f := MemLp.coeFn_toLp f_mem
    have htoLp_f_eq_invH : f_mem.toLp f =ᵐ[μB] invH := by
      simpa [hlimit_eq] using hrestrict_invH
    simpa [R, B] using htoLp_f_eq_invH.symm.trans hf_toLp
  have hall :
      (invH : E d → ℂ)
        =ᵐ[volume.restrict
          (⋃ k : ℕ, Metric.closedBall (0 : E d) (k : ℝ))] f := by
    exact
      (ae_eq_restrict_iUnion_iff
        (μ := volume)
        (s := fun k : ℕ => Metric.closedBall (0 : E d) (k : ℝ))
        (f := (invH : E d → ℂ)) (g := f)).2 hball
  have hglobal : (invH : E d → ℂ) =ᵐ[volume] f := by
    simpa [Metric.iUnion_closedBall_nat] using hall
  have hf_memL2 : MemLp f 2 volume :=
    MemLp.ae_eq hglobal (Lp.memLp invH)
  have hinv_eq : invH = hf_memL2.toLp f := by
    have hcongr :=
      MemLp.toLp_congr (Lp.memLp invH) hf_memL2 hglobal
    simpa using hcongr
  refine ⟨hH_memL2, hf_memL2, hf_cont, ?_⟩
  simpa [Hlp, invH] using hinv_eq

theorem continuousInvFourierRep_of_partialFourier_L2_and_locallyUniform {d : ℕ}
    {A : Set (E d)} {alpha : ℝ}
    {g0 G0 : E d → ℂ} {q Q : ℕ → E d → ℂ}
    {H f : E d → ℂ}
    (h0 : WeightedFourierWitness alpha A g0 G0)
    (hq : ∀ n, WeightedFourierWitness alpha A (q n) (Q n))
    (hH_memL2 : MemLp H 2 volume)
    (h_L2 :
      Tendsto
        (fun n =>
          eLpNorm
            (fun xi => partialFourier G0 Q n xi - H xi) 2 volume)
        atTop (nhds 0))
    (h_loc : LocallyUniformLimit (fun n x => partialSum g0 q n x) f)
    (hf_cont : Continuous f) :
    ContinuousInvFourierRep H f := by
  exact
    continuousInvFourierRep_of_L2_and_locallyUniform
      (G := partialFourier G0 Q)
      (s := fun n x => partialSum g0 q n x)
      hH_memL2
      (fun n => (partialFourierWitness h0 hq n).invRep)
      h_L2 h_loc hf_cont

theorem weightedWitness_tsum_of_locallyUniform_limit {d : ℕ}
    {A : Set (E d)} {alpha : ℝ}
    {g0 G0 : E d → ℂ}
    {q Q : ℕ → E d → ℂ}
    {f H : E d → ℂ}
    (hA : AContextHD d A)
    (h0 : WeightedFourierWitness alpha A g0 G0)
    (hq : ∀ n, WeightedFourierWitness alpha A (q n) (Q n))
    (hH_side : WeightedFourierSide alpha A H)
    (h_weighted_sum : weightedSeriesTendsto alpha A G0 Q H)
    (h_L2 :
      Tendsto
        (fun n =>
          eLpNorm
            (fun xi => partialFourier G0 Q n xi - H xi)
            2 volume)
        atTop (nhds 0))
    (h_loc_unif :
      LocallyUniformLimit (fun n x => partialSum g0 q n x) f)
    (hf_cont : Continuous f) :
    WeightedFourierWitness alpha A f H := by
  have _hA_used : AContextHD d A := hA
  have _h_weighted_sum_used : weightedSeriesTendsto alpha A G0 Q H :=
    h_weighted_sum
  exact
    ⟨hH_side,
      continuousInvFourierRep_of_partialFourier_L2_and_locallyUniform
        h0 hq hH_side.memL2 h_L2 h_loc_unif hf_cont⟩

theorem LocallyUniformLimit.eval_of_eventually_eq {d : ℕ}
    {F : ℕ → E d → ℂ} {f : E d → ℂ}
    {x : E d} {c : ℂ}
    (hlim : LocallyUniformLimit F f)
    (hF : ∀ᶠ n in atTop, F n x = c) :
    f x = c := by
  refine eq_of_forall_dist_le ?_
  intro eps heps
  have hconv := hlim ({x} : Set (E d)) isCompact_singleton eps heps
  rcases (hconv.and hF).exists with ⟨n, hnconv, hnF⟩
  have hlt : dist (F n x) (f x) < eps := hnconv x (by simp)
  exact le_of_lt (by simpa [hnF, dist_comm] using hlt)

theorem recursive_limit_value_x0 {d : ℕ}
    {g0 : E d → ℂ} {q : ℕ → E d → ℂ}
    {f : E d → ℂ} {x0 : E d}
    (hlim : LocallyUniformLimit (fun n x => partialSum g0 q n x) f)
    (hval : ∀ᶠ n in atTop, partialSum g0 q n x0 = 1) :
    f x0 = 1 := by
  exact LocallyUniformLimit.eval_of_eventually_eq hlim hval

theorem recursive_limit_value_lambda {d : ℕ}
    {g0 : E d → ℂ} {q : ℕ → E d → ℂ}
    {f : E d → ℂ} {lambda : ℕ → E d} {j : ℕ}
    (hlim : LocallyUniformLimit (fun n x => partialSum g0 q n x) f)
    (hzero : ∀ᶠ n in atTop,
      partialSum g0 q n (lambda j) = 0) :
    f (lambda j) = 0 := by
  exact LocallyUniformLimit.eval_of_eventually_eq hlim hzero

theorem exists_weighted_pw_vanishes_on_uniformlyDiscrete {d : ℕ} (hd_pos : 0 < d)
    {A Lambda : Set (E d)} {alpha : ℝ} {x0 : E d}
    (hA : AContextHD d A)
    (halpha : AlphaLeDimHalf d alpha)
    (hLambda : UniformlyDiscrete Lambda)
    (hx0 : x0 ∉ Lambda) :
    ∃ f P : E d → ℂ,
      WeightedFourierWitness alpha A f P ∧
      Continuous f ∧
      f x0 = 1 ∧
      ∀ lambda ∈ Lambda, f lambda = 0 := by
  classical
  by_cases hLambda_fin : Lambda.Finite
  · exact finite_set_case hd_pos hA halpha hLambda_fin hx0
  · have hLambda_inf : Lambda.Infinite := hLambda_fin
    obtain ⟨lambda, hlambda_inj, hlambda_mem, hlambda_surj, hlambda_escape⟩ :=
      exists_escaping_enumeration hLambda hLambda_inf
    have hx0_lambda : ∀ n, x0 ≠ lambda n := by
      intro n hx
      exact hx0 (by simpa [← hx] using hlambda_mem n)
    obtain
      ⟨g0, G0, q, Q, h0, hq, _hg0_x0, _hq_x0, _hq_prev, hpartial_x0,
        hpartial_lambda, hnorm, hcompact⟩ :=
      recursive_corrections hd_pos hA halpha hlambda_inj hlambda_escape hx0_lambda
    obtain ⟨H, hH_side, _hH_zero, hseries, hL2⟩ :=
      weightedSeriesTendsto_of_geometric_bound hA h0 hq hnorm
    obtain ⟨f, hf_cont, hloc⟩ :=
      locallyUniformLimit_of_geometric_bound
        h0.continuous (fun n => (hq n).continuous) hcompact
    have hW : WeightedFourierWitness alpha A f H :=
      weightedWitness_tsum_of_locallyUniform_limit
        hA h0 hq hH_side hseries hL2 hloc hf_cont
    have hf_x0 : f x0 = 1 :=
      recursive_limit_value_x0 hloc
        (Eventually.of_forall fun n => hpartial_x0 n)
    have hf_zero : ∀ y ∈ Lambda, f y = 0 := by
      intro y hy
      rcases hlambda_surj y hy with ⟨j, hj⟩
      have hevent :
          ∀ᶠ n in atTop, partialSum g0 q n (lambda j) = 0 := by
        filter_upwards [eventually_ge_atTop (j + 1)] with n hn
        exact hpartial_lambda n j (Nat.lt_of_succ_le hn)
      have hzero_lambda : f (lambda j) = 0 :=
        recursive_limit_value_lambda hloc hevent
      simpa [hj] using hzero_lambda
    exact ⟨f, H, hW, hf_cont, hf_x0, hf_zero⟩

theorem higher_dimensional_nonuniqueness {d : ℕ} (hd_pos : 0 < d)
    {A Lambda : Set (E d)} {alpha : ℝ} {x0 : E d}
    (hA_meas : MeasurableSet A)
    (hA_sub : A ⊆ unitCube d)
    (hA_pos : 0 < volume A)
    (hA_lt_one : volume A < 1)
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_le_dim : 2 * alpha ≤ (d : ℝ))
    (hLambda : UniformlyDiscrete Lambda)
    (hx0 : x0 ∉ Lambda) :
    ∃ f : E d → ℂ,
      WeightedPW alpha A f ∧
      Continuous f ∧
      f x0 = 1 ∧
      ∀ lambda ∈ Lambda, f lambda = 0 := by
  have _hA_lt_one_used : volume A < 1 := hA_lt_one
  have hA : AContextHD d A := ⟨hA_meas, hA_sub, hA_pos⟩
  have halpha : AlphaLeDimHalf d alpha := ⟨halpha_nonneg, halpha_le_dim⟩
  obtain ⟨f, P, hW, hf_cont, hf_x0, hf_zero⟩ :=
    exists_weighted_pw_vanishes_on_uniformlyDiscrete
      hd_pos hA halpha hLambda hx0
  exact ⟨f, ⟨P, hW⟩, hf_cont, hf_x0, hf_zero⟩

end SpectralGapsPrelim.HigherDim
