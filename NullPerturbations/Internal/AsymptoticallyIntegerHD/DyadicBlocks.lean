import AsymptoticallyIntegerHD.Definitions
import AsymptoticallyIntegerHD.PerturbedExponentials
import AsymptoticallyIntegerHD.ThinInterpolation
import Mathlib.Analysis.PSeries

/-! # Dyadic vector shells, coordinate pieces, and budgets

This module establishes the dyadic vector shells, coordinate pieces, and
budget estimates used in the construction.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace AsymptoticallyIntegerHD

/-- Dyadic scale `2⁻ʲ`. -/
def dyadicScale (j : Nat) : Real := (2 : Real) ^ (-(j : Int))

private theorem dyadicScale_eq_inv_pow (j : Nat) :
    dyadicScale j = ((2 : Real)⁻¹) ^ j := by
  rw [dyadicScale, zpow_neg, zpow_natCast, inv_pow]

private theorem dyadicScale_pos (j : Nat) : 0 < dyadicScale j := by
  rw [dyadicScale_eq_inv_pow]
  positivity

private theorem dyadicScale_strictAnti : StrictAnti dyadicScale := by
  intro j k hjk
  rw [dyadicScale_eq_inv_pow, dyadicScale_eq_inv_pow]
  exact pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) hjk

private theorem dyadicScale_antitone : Antitone dyadicScale :=
  dyadicScale_strictAnti.antitone

private theorem dyadicScale_tendsto_zero :
    Filter.Tendsto dyadicScale Filter.atTop (nhds 0) := by
  convert tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : Real) ≤ (2 : Real)⁻¹)
    (by norm_num : (2 : Real)⁻¹ < 1) using 1
  funext j
  exact dyadicScale_eq_inv_pow j

private theorem exists_dyadicScale_lt {x : Real} (hx : 0 < x) :
    ∃ j : Nat, dyadicScale j < x := by
  have hEventually : ∀ᶠ j in Filter.atTop, dyadicScale j ∈ Set.Iio x :=
    dyadicScale_tendsto_zero.eventually (Iio_mem_nhds hx)
  exact hEventually.exists

namespace Internal

/-- Half-open nonzero perturbation shell outside `C0`. -/
def dyadicBlockSet {d : Nat} (delta : IntVec d → RealVec d)
    (C0 : Finset (IntVec d)) (j : Nat) : Set (IntVec d) :=
  {n | n ∉ C0 ∧ delta n ≠ 0 ∧ dyadicScale (j + 1) ≤ ‖delta n‖ ∧
    ‖delta n‖ < dyadicScale j}

/-- Null perturbations have finite positive dyadic shells. -/
theorem dyadicBlockSet_finite {d : Nat} {delta : IntVec d → RealVec d}
    (hdelta : TendsToZeroAtIntVecInfinity delta) (C0 : Finset (IntVec d))
    (j : Nat) : (dyadicBlockSet delta C0 j).Finite := by
  obtain ⟨N, hN⟩ := hdelta (dyadicScale (j + 1)) (dyadicScale_pos (j + 1))
  apply (Finset.finite_toSet (indexBall d N)).subset
  intro n hn
  have hlower : dyadicScale (j + 1) ≤ ‖delta n‖ := hn.2.2.1
  have hsize : indexSize n < N := by
    by_contra hnot
    have hsmall := hN n (Nat.le_of_not_gt hnot)
    exact (not_lt_of_ge hlower) hsmall
  exact (mem_indexBall.mpr hsize.le)

end Internal

/-- Finset realization of a dyadic shell. -/
noncomputable def dyadicBlock {d : Nat} (delta : IntVec d → RealVec d)
    (hdelta : TendsToZeroAtIntVecInfinity delta) (C0 : Finset (IntVec d))
    (j : Nat) : Finset (IntVec d) :=
  (Internal.dyadicBlockSet_finite hdelta C0 j).toFinset

/-- Exact membership interface for dyadic blocks. -/
@[simp] theorem mem_dyadicBlock_iff {d : Nat}
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    {C0 : Finset (IntVec d)} {j : Nat} {n : IntVec d} :
    n ∈ dyadicBlock delta hdelta C0 j ↔
      n ∉ C0 ∧ delta n ≠ 0 ∧ dyadicScale (j + 1) ≤ ‖delta n‖ ∧
        ‖delta n‖ < dyadicScale j := by
  simp only [dyadicBlock, Set.Finite.mem_toFinset, Internal.dyadicBlockSet,
    Set.mem_setOf_eq]

namespace Internal

/-- Data returned by the deterministic maximizing-coordinate selector. -/
structure MaxCoordinateResult {d : Nat} (v : RealVec d) where
  coordinate : Fin d
  abs_eq_norm : |v coordinate| = ‖v‖
  least : ∀ i, |v i| = ‖v‖ → coordinate.val ≤ i.val

/-- Existence certificate for the deterministic least maximizing coordinate. -/
theorem maxCoordinateResult_nonempty {d : Nat} (hd : 0 < d) (v : RealVec d)
    (hv : v ≠ 0) : Nonempty (MaxCoordinateResult v) := by
  classical
  have _hvNorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have huniv : (Finset.univ : Finset (Fin d)).Nonempty := by
    exact ⟨⟨0, hd⟩, Finset.mem_univ _⟩
  obtain ⟨i, hi, hsup⟩ :=
    Finset.exists_mem_eq_sup (s := (Finset.univ : Finset (Fin d))) huniv
      (fun r ↦ ‖v r‖₊)
  have hiMax : |v i| = ‖v‖ := by
    change |v i| =
      ((Finset.univ.sup fun r : Fin d ↦ ‖v r‖₊ : NNReal) : Real)
    rw [hsup]
    simp [Real.norm_eq_abs]
  let A : Finset (Fin d) := Finset.univ.filter fun r ↦ |v r| = ‖v‖
  have hA : A.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, hiMax⟩⟩
  let r : Fin d := A.min' hA
  refine ⟨⟨r, ?_, ?_⟩⟩
  · exact (Finset.mem_filter.mp (A.min'_mem hA)).2
  · intro k hk
    exact_mod_cast A.min'_le k (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩)

/-- Least coordinate attaining the finite Pi norm. -/
noncomputable def maxCoordinate {d : Nat} (hd : 0 < d) (v : RealVec d)
    (hv : v ≠ 0) : MaxCoordinateResult v :=
  Classical.choice (maxCoordinateResult_nonempty hd v hv)

end Internal

/-- Coordinate piece selected by the cached maximizing index. -/
noncomputable def coordinateBlock {d : Nat} (delta : IntVec d → RealVec d)
    (hdelta : TendsToZeroAtIntVecInfinity delta) (C0 : Finset (IntVec d))
    (hd : 0 < d) (j : Nat) (r : Fin d) : Finset (IntVec d) := by
  classical
  let B := dyadicBlock delta hdelta C0 j
  exact (B.attach.filter fun n =>
    (Internal.maxCoordinate hd (delta n.1)
      (mem_dyadicBlock_iff.mp n.2).2.1).coordinate = r).map
        ⟨Subtype.val, Subtype.val_injective⟩

/-- Exact membership interface for coordinate pieces. -/
theorem mem_coordinateBlock_iff {d : Nat} {delta : IntVec d → RealVec d}
    {hdelta : TendsToZeroAtIntVecInfinity delta} {C0 : Finset (IntVec d)}
    {hd : 0 < d} {j : Nat} {r : Fin d} {n : IntVec d} :
    n ∈ coordinateBlock delta hdelta C0 hd j r ↔
      ∃ hn : n ∈ dyadicBlock delta hdelta C0 j,
        (Internal.maxCoordinate hd (delta n)
          (mem_dyadicBlock_iff.mp hn).2.1).coordinate = r := by
  classical
  simp only [coordinateBlock, Finset.mem_map, Finset.mem_filter, Finset.mem_attach,
    true_and, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m.2, hm⟩
  · rintro ⟨hn, hcoord⟩
    exact ⟨⟨n, hn⟩, hcoord, rfl⟩

/-- Coordinate partition, level disjointness, and unique shells. -/
theorem coordinateBlocks_partition {d : Nat} (hd : 0 < d)
    {delta : IntVec d → RealVec d} (hdelta : TendsToZeroAtIntVecInfinity delta)
    (C0 : Finset (IntVec d)) :
    (∀ j, Set.Pairwise (Set.univ : Set (Fin d)) fun r s =>
      Disjoint (coordinateBlock delta hdelta C0 hd j r)
        (coordinateBlock delta hdelta C0 hd j s)) ∧
    (∀ j, (Finset.univ.biUnion fun r =>
      coordinateBlock delta hdelta C0 hd j r) =
        dyadicBlock delta hdelta C0 j) ∧
    (∀ j k, j ≠ k → Disjoint (dyadicBlock delta hdelta C0 j)
      (dyadicBlock delta hdelta C0 k)) ∧
    (∀ n, n ∉ C0 → delta n ≠ 0 → ‖delta n‖ < (1 / 8 : Real) →
      ∃! p : Nat × Fin d,
        3 ≤ p.1 ∧ n ∈ coordinateBlock delta hdelta C0 hd p.1 p.2) := by
  classical
  have hcoordinateDisjoint : ∀ j,
      Set.Pairwise (Set.univ : Set (Fin d)) fun r s ↦
        Disjoint (coordinateBlock delta hdelta C0 hd j r)
          (coordinateBlock delta hdelta C0 hd j s) := by
    intro j r _ s _ hrs
    rw [Finset.disjoint_left]
    intro n hnr hns
    obtain ⟨hnrB, hnrCoord⟩ := mem_coordinateBlock_iff.mp hnr
    obtain ⟨hnsB, hnsCoord⟩ := mem_coordinateBlock_iff.mp hns
    have : r = s := by
      rw [← hnrCoord, ← hnsCoord]
    exact hrs this
  have hcoordinateUnion : ∀ j,
      (Finset.univ.biUnion fun r ↦ coordinateBlock delta hdelta C0 hd j r) =
        dyadicBlock delta hdelta C0 j := by
    intro j
    ext n
    constructor
    · intro hn
      obtain ⟨r, -, hnr⟩ := Finset.mem_biUnion.mp hn
      exact (mem_coordinateBlock_iff.mp hnr).choose
    · intro hn
      let r := (Internal.maxCoordinate hd (delta n)
        (mem_dyadicBlock_iff.mp hn).2.1).coordinate
      apply Finset.mem_biUnion.mpr
      exact ⟨r, Finset.mem_univ r, mem_coordinateBlock_iff.mpr ⟨hn, rfl⟩⟩
  have hlevelDisjoint : ∀ j k, j ≠ k →
      Disjoint (dyadicBlock delta hdelta C0 j)
        (dyadicBlock delta hdelta C0 k) := by
    intro j k hjk
    rw [Finset.disjoint_left]
    intro n hnj hnk
    have hj := mem_dyadicBlock_iff.mp hnj
    have hk := mem_dyadicBlock_iff.mp hnk
    rcases lt_or_gt_of_ne hjk with hjlt | hklt
    · have hscale : dyadicScale k ≤ dyadicScale (j + 1) :=
        dyadicScale_antitone (Nat.succ_le_iff.mpr hjlt)
      exact (not_lt_of_ge (hscale.trans hj.2.2.1)) hk.2.2.2
    · have hscale : dyadicScale j ≤ dyadicScale (k + 1) :=
        dyadicScale_antitone (Nat.succ_le_iff.mpr hklt)
      exact (not_lt_of_ge (hscale.trans hk.2.2.1)) hj.2.2.2
  refine ⟨hcoordinateDisjoint, hcoordinateUnion, hlevelDisjoint, ?_⟩
  intro n hnC0 hnzero hsmall
  have hnormPos : 0 < ‖delta n‖ := norm_pos_iff.mpr hnzero
  obtain ⟨m, hm⟩ := exists_dyadicScale_lt hnormPos
  have hexists : ∃ q : Nat, dyadicScale (3 + q + 1) ≤ ‖delta n‖ := by
    refine ⟨m, (dyadicScale_antitone ?_).trans hm.le⟩
    omega
  let q : Nat := Nat.find hexists
  let j : Nat := 3 + q
  have hjLower : dyadicScale (j + 1) ≤ ‖delta n‖ := by
    simpa [j, q, Nat.add_assoc] using Nat.find_spec hexists
  have hscaleThree : dyadicScale 3 = (1 / 8 : Real) := by
    norm_num [dyadicScale, zpow_neg]
  have hjUpper : ‖delta n‖ < dyadicScale j := by
    by_cases hq : q = 0
    · simpa [j, hq, hscaleThree] using hsmall
    · obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero hq
      have htlt : t < Nat.find hexists := by simp [q, ht]
      have hnot := Nat.find_min hexists htlt
      have hnot' : ¬dyadicScale (3 + t + 1) ≤ ‖delta n‖ := hnot
      simpa [j, q, ht, Nat.add_assoc] using lt_of_not_ge hnot'
  have hnBlock : n ∈ dyadicBlock delta hdelta C0 j :=
    mem_dyadicBlock_iff.mpr ⟨hnC0, hnzero, hjLower, hjUpper⟩
  let r : Fin d := (Internal.maxCoordinate hd (delta n) hnzero).coordinate
  have hnCoordinate : n ∈ coordinateBlock delta hdelta C0 hd j r := by
    apply mem_coordinateBlock_iff.mpr
    refine ⟨hnBlock, ?_⟩
    congr
  refine ⟨(j, r), ⟨by simp [j], hnCoordinate⟩, ?_⟩
  intro p hp
  have hpBlock := (mem_coordinateBlock_iff.mp hp.2).choose
  have hjEq : p.1 = j := by
    by_contra hne
    exact (Finset.disjoint_left.mp (hlevelDisjoint p.1 j hne)
      hpBlock) hnBlock
  apply Prod.ext
  · exact hjEq
  · obtain ⟨hpB, hpCoord⟩ := mem_coordinateBlock_iff.mp hp.2
    have hcoord :
        (Internal.maxCoordinate hd (delta n) hnzero).coordinate = p.2 := by
      simpa only using hpCoord
    simpa [r] using hcoord.symm

/-- Finite union of all protected levels through `4*j`. -/
noncomputable def guardFinset {d : Nat} (delta : IntVec d → RealVec d)
    (hdelta : TendsToZeroAtIntVecInfinity delta) (C0 : Finset (IntVec d))
    (j : Nat) : Finset (IntVec d) :=
  (Finset.Icc 3 (4 * j)).biUnion fun k => dyadicBlock delta hdelta C0 k

namespace Internal

/-- Product two-sided lattice weight. -/
def indexWeight {d : Nat} (n : IntVec d) : Real :=
  ∏ i, (1 + ((n i).natAbs : Real)) ^ (-2 : Int)

private def integerWeight (n : Int) : Real :=
  (1 + (n.natAbs : Real)) ^ (-2 : Int)

private theorem integerWeight_summable : Summable integerWeight := by
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · refine ((Real.summable_one_div_nat_add_rpow 1 2).mpr (by norm_num)).congr ?_
    intro n
    simp [integerWeight, zpow_neg, add_comm]
    rfl
  · refine ((Real.summable_one_div_nat_add_rpow 1 2).mpr (by norm_num)).congr ?_
    intro n
    simp [integerWeight, zpow_neg, add_comm]
    rfl

private theorem indexWeight_nonneg {d : Nat} (n : IntVec d) :
    0 ≤ indexWeight n := by
  exact Finset.prod_nonneg fun _ _ ↦ zpow_nonneg (by positivity) _

/-- Product-lattice summability needed by the budget constructor. -/
theorem indexWeight_summable (d : Nat) :
    Summable (fun n : IntVec d => indexWeight n) := by
  induction d with
  | zero => exact Summable.of_finite
  | succ d ih =>
      let e := Fin.succFunEquiv Int d
      let g : (IntVec d × Int) → Real := fun p ↦ indexWeight p.1 * integerWeight p.2
      have hg_nonneg : ∀ p, 0 ≤ g p := by
        intro p
        exact mul_nonneg (indexWeight_nonneg p.1)
          (zpow_nonneg (by positivity) _)
      have hg : Summable g := by
        rw [summable_prod_of_nonneg hg_nonneg]
        constructor
        · intro n
          exact integerWeight_summable.mul_left (indexWeight n)
        · have houter : Summable
              (fun n : IntVec d ↦ indexWeight n * ∑' z : Int, integerWeight z) :=
            ih.mul_right (∑' z : Int, integerWeight z)
          convert houter using 1
          funext n
          simp only [g]
          rw [tsum_mul_left]
      have hcomp : Summable (fun n : IntVec (d + 1) ↦ g (e n)) :=
        hg.comp_injective e.injective
      refine hcomp.congr ?_
      intro n
      simp [g, e, indexWeight, integerWeight, Fin.prod_univ_castSucc,
        Fin.succFunEquiv]
      exact mul_comm _ _

/-- Fixed positive geometric-plus-product denominator. -/
def blockBudgetDenominator (d : Nat) : Real :=
  (∑' j : Nat, if 3 ≤ j then dyadicScale j else 0) +
    ∑' n : IntVec d, indexWeight n

private theorem dyadicLevelTerm_summable :
    Summable (fun j : Nat ↦ if 3 ≤ j then dyadicScale j else 0) := by
  have hscale : Summable dyadicScale := by
    refine (summable_geometric_of_lt_one (by norm_num : (0 : Real) ≤ (2 : Real)⁻¹)
      (by norm_num : (2 : Real)⁻¹ < 1)).congr ?_
    intro j
    exact (dyadicScale_eq_inv_pow j).symm
  exact Summable.of_nonneg_of_le
    (fun j ↦ by
      by_cases h : 3 ≤ j
      · simp [h, (dyadicScale_pos j).le]
      · simp [h])
    (fun j ↦ by
      by_cases h : 3 ≤ j
      · simp [h]
      · simp [h, (dyadicScale_pos j).le]) hscale

/-- The block-budget denominator is positive. -/
theorem blockBudgetDenominator_pos (d : Nat) :
    0 < blockBudgetDenominator d := by
  have htermNonneg : ∀ j : Nat,
      0 ≤ (if 3 ≤ j then dyadicScale j else 0) := by
    intro j
    by_cases h : 3 ≤ j
    · simp [h, (dyadicScale_pos j).le]
    · simp [h]
  have hlevel : 0 < ∑' j : Nat, if 3 ≤ j then dyadicScale j else 0 := by
    have hle := dyadicLevelTerm_summable.sum_le_tsum {3}
      (fun j _ ↦ htermNonneg j)
    simp only [Finset.sum_singleton, if_pos (by omega : 3 ≤ (3 : Nat))] at hle
    exact (dyadicScale_pos 3).trans_le hle
  have hweight : 0 ≤ ∑' n : IntVec d, indexWeight n :=
    tsum_nonneg indexWeight_nonneg
  rw [blockBudgetDenominator]
  linarith

/-- Maximum block weight, zero for an empty shell. -/
noncomputable def blockWeightMax {d : Nat} (delta : IntVec d → RealVec d)
    (hdelta : TendsToZeroAtIntVecInfinity delta) (C0 : Finset (IntVec d))
    (j : Nat) : Real :=
  if h : (dyadicBlock delta hdelta C0 j).Nonempty then
    (dyadicBlock delta hdelta C0 j).sup' h indexWeight
  else 0

private theorem blockWeightMax_nonneg {d : Nat} (delta : IntVec d → RealVec d)
    (hdelta : TendsToZeroAtIntVecInfinity delta) (C0 : Finset (IntVec d))
    (j : Nat) : 0 ≤ blockWeightMax delta hdelta C0 j := by
  classical
  rw [blockWeightMax]
  split
  next h =>
    obtain ⟨n, hn⟩ := h
    exact (indexWeight_nonneg n).trans
      (Finset.le_sup' (f := indexWeight) hn)
  next => exact le_rfl

private theorem indexWeight_le_blockWeightMax {d : Nat}
    (delta : IntVec d → RealVec d)
    (hdelta : TendsToZeroAtIntVecInfinity delta) (C0 : Finset (IntVec d))
    {j : Nat} {n : IntVec d} (hn : n ∈ dyadicBlock delta hdelta C0 j) :
    indexWeight n ≤ blockWeightMax delta hdelta C0 j := by
  classical
  rw [blockWeightMax, dif_pos ⟨n, hn⟩]
  exact Finset.le_sup' (f := indexWeight) hn

/-- Cached representatives and the sole total budget family. -/
structure BlockParameters {d : Nat} (hd : 0 < d)
    (delta : IntVec d → RealVec d) (hdelta : TendsToZeroAtIntVecInfinity delta)
    (data : ModifiedFrequencyData delta) (mu0 : Real) where
  mu0_pos : 0 < mu0
  mu0_lt_one : mu0 < 1
  representative : (j : Nat) →
    Option {n : IntVec d // n ∈ dyadicBlock delta hdelta data.C0 j}
  representative_none_iff : ∀ j,
    representative j = none ↔ ¬(dyadicBlock delta hdelta data.C0 j).Nonempty
  eta : Nat → Real
  eta_eq : ∀ j, eta j = if 3 ≤ j then
    (mu0 / 8) * (dyadicScale j + blockWeightMax delta hdelta data.C0 j) /
      blockBudgetDenominator d else 0
  eta_zero : eta 0 = 0 ∧ eta 1 = 0 ∧ eta 2 = 0
  eta_nonneg : ∀ j, 0 ≤ eta j
  eta_pos : ∀ j, 3 ≤ j → 0 < eta j

/-- Existence certificate for the canonical block parameters. -/
theorem blockParameters_nonempty {d : Nat} (hd : 0 < d)
    (delta : IntVec d → RealVec d) (hdelta : TendsToZeroAtIntVecInfinity delta)
    (data : ModifiedFrequencyData delta) (mu0 : Real) (hmu0 : 0 < mu0)
    (hmu01 : mu0 < 1) : Nonempty (BlockParameters hd delta hdelta data mu0) := by
  classical
  let representative : (j : Nat) →
      Option {n : IntVec d // n ∈ dyadicBlock delta hdelta data.C0 j} := fun j ↦
    if h : (dyadicBlock delta hdelta data.C0 j).Nonempty then
      some ⟨h.choose, h.choose_spec⟩
    else none
  let eta : Nat → Real := fun j ↦ if 3 ≤ j then
    (mu0 / 8) * (dyadicScale j + blockWeightMax delta hdelta data.C0 j) /
      blockBudgetDenominator d else 0
  refine ⟨{
    mu0_pos := hmu0
    mu0_lt_one := hmu01
    representative := representative
    representative_none_iff := ?_
    eta := eta
    eta_eq := ?_
    eta_zero := ?_
    eta_nonneg := ?_
    eta_pos := ?_ }⟩
  · intro j
    simp [representative]
  · intro j
    rfl
  · simp [eta]
  · intro j
    by_cases hj : 3 ≤ j
    · simp only [eta]
      rw [if_pos hj]
      exact div_nonneg
        (mul_nonneg (div_nonneg hmu0.le (by norm_num))
          (add_nonneg (dyadicScale_pos j).le
            (blockWeightMax_nonneg delta hdelta data.C0 j)))
        (blockBudgetDenominator_pos d).le
    · simp [eta, hj]
  · intro j hj
    simp only [eta]
    rw [if_pos hj]
    exact div_pos
      (mul_pos (div_pos hmu0 (by norm_num))
        (add_pos_of_pos_of_nonneg (dyadicScale_pos j)
          (blockWeightMax_nonneg delta hdelta data.C0 j)))
      (blockBudgetDenominator_pos d)

/-- Sole constructor for the canonical block parameters. -/
noncomputable def blockParameters {d : Nat} (hd : 0 < d)
    (delta : IntVec d → RealVec d) (hdelta : TendsToZeroAtIntVecInfinity delta)
    (data : ModifiedFrequencyData delta) (mu0 : Real) (hmu0 : 0 < mu0)
    (hmu01 : mu0 < 1) : BlockParameters hd delta hdelta data mu0 :=
  Classical.choice
    (blockParameters_nonempty hd delta hdelta data mu0 hmu0 hmu01)

/-- Uniform summability and reciprocal-budget constants. -/
structure BudgetConstants {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    {data : ModifiedFrequencyData delta} {mu0 : Real}
    (P : BlockParameters hd delta hdelta data mu0) where
  Ceta : Real
  Ceta_pos : 0 < Ceta
  eta_nonneg : ∀ j, 0 ≤ P.eta j
  eta_pos : ∀ j, 3 ≤ j → 0 < P.eta j
  eta_summable : Summable P.eta
  eta_tsum_le : ∑' j, P.eta j < mu0 / 4
  inv_eta_le_scale : ∀ j, 3 ≤ j → 1 / P.eta j ≤ Ceta * (2 : Real) ^ j
  inv_eta_le_weight : ∀ j n, n ∈ dyadicBlock delta hdelta data.C0 j →
    1 / P.eta j ≤ Ceta * (1 + indexSize n : Real) ^ (2 * d + 2)

/-- Existence certificate for the quantitative budget package. -/
theorem budgetConstants_nonempty {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    {data : ModifiedFrequencyData delta} {mu0 : Real}
    (P : BlockParameters hd delta hdelta data mu0) : Nonempty (BudgetConstants P) := by
  classical
  let A : Set Nat := {j | (dyadicBlock delta hdelta data.C0 j).Nonempty}
  have hdatumExists (e : A) : ∃ n : IntVec d,
      n ∈ dyadicBlock delta hdelta data.C0 e.1 ∧
        blockWeightMax delta hdelta data.C0 e.1 = indexWeight n := by
    have he : (dyadicBlock delta hdelta data.C0 e.1).Nonempty := e.2
    rw [blockWeightMax, dif_pos he]
    obtain ⟨n, hn, heq⟩ :=
      Finset.exists_mem_eq_sup' e.2 indexWeight
    exact ⟨n, hn, heq⟩
  let datum : A → IntVec d := fun e ↦ Classical.choose (hdatumExists e)
  have hdatum_mem (e : A) :
      datum e ∈ dyadicBlock delta hdelta data.C0 e.1 :=
    (Classical.choose_spec (hdatumExists e)).1
  have hdatum_eq (e : A) :
      blockWeightMax delta hdelta data.C0 e.1 = indexWeight (datum e) :=
    (Classical.choose_spec (hdatumExists e)).2
  have hdatum_injective : Function.Injective datum := by
    intro e f hef
    apply Subtype.ext
    by_contra hne
    have hdisjoint := (coordinateBlocks_partition hd hdelta data.C0).2.2.1
      e.1 f.1 hne
    exact (Finset.disjoint_left.mp hdisjoint (hdatum_mem e))
      (hef ▸ hdatum_mem f)
  let maxWeight : Nat → Real := fun j ↦
    blockWeightMax delta hdelta data.C0 j
  have hmax_sub_summable : Summable (fun e : A ↦ maxWeight e.1) := by
    refine ((indexWeight_summable d).comp_injective hdatum_injective).congr ?_
    intro e
    simpa [Function.comp_def, maxWeight] using (hdatum_eq e).symm
  have hmax_indicator : A.indicator maxWeight = maxWeight := by
    funext j
    by_cases hj : (dyadicBlock delta hdelta data.C0 j).Nonempty
    · have hmem : j ∈ A := hj
      rw [Set.indicator_of_mem hmem]
    · have hnotmem : j ∉ A := hj
      rw [Set.indicator_of_notMem hnotmem]
      simp [maxWeight, blockWeightMax, hj]
  have hmax_summable : Summable maxWeight := by
    have h := (summable_subtype_iff_indicator (f := maxWeight) (s := A)).mp
      hmax_sub_summable
    rwa [hmax_indicator] at h
  have hmax_nonneg : ∀ j, 0 ≤ maxWeight j := fun j ↦
    blockWeightMax_nonneg delta hdelta data.C0 j
  have hmax_tsum_eq :
      ∑' j : Nat, maxWeight j = ∑' e : A, maxWeight e.1 := by
    rw [tsum_subtype A maxWeight, hmax_indicator]
  have hmax_tsum_le :
      ∑' j : Nat, maxWeight j ≤ ∑' n : IntVec d, indexWeight n := by
    rw [hmax_tsum_eq]
    exact Summable.tsum_le_tsum_of_inj datum hdatum_injective
      (fun n _ ↦ indexWeight_nonneg n)
      (fun e ↦ (hdatum_eq e).le) hmax_sub_summable (indexWeight_summable d)
  let levelWeight : Nat → Real := fun j ↦
    if 3 ≤ j then dyadicScale j else 0
  have hlevel_nonneg : ∀ j, 0 ≤ levelWeight j := by
    intro j
    by_cases hj : 3 ≤ j
    · simp [levelWeight, hj, (dyadicScale_pos j).le]
    · simp [levelWeight, hj]
  have hlevel_summable : Summable levelWeight := by
    simpa only [levelWeight] using dyadicLevelTerm_summable
  let c : Real := mu0 / 8
  let D : Real := blockBudgetDenominator d
  have hc : 0 < c := div_pos P.mu0_pos (by norm_num)
  have hD : 0 < D := by simpa only [D] using blockBudgetDenominator_pos d
  have heta_formula (j : Nat) (hj : 3 ≤ j) :
      P.eta j = c * (levelWeight j + maxWeight j) / D := by
    rw [P.eta_eq j, if_pos hj]
    simp only [c, D, levelWeight, maxWeight, if_pos hj]
  have heta_nonneg : ∀ j, 0 ≤ P.eta j := P.eta_nonneg
  have heta_pos : ∀ j, 3 ≤ j → 0 < P.eta j := P.eta_pos
  let major : Nat → Real := fun j ↦
    (c / D) * (levelWeight j + maxWeight j)
  have hmajor_summable : Summable major :=
    (hlevel_summable.add hmax_summable).mul_left (c / D)
  have heta_le_major : ∀ j, P.eta j ≤ major j := by
    intro j
    by_cases hj : 3 ≤ j
    · rw [heta_formula j hj]
      simp only [major]
      exact le_of_eq (by ring)
    · rw [P.eta_eq j, if_neg hj]
      exact mul_nonneg (div_nonneg hc.le hD.le)
        (add_nonneg (hlevel_nonneg j) (hmax_nonneg j))
  have heta_summable : Summable P.eta :=
    Summable.of_nonneg_of_le heta_nonneg heta_le_major hmajor_summable
  have hsum_components :
      (∑' j : Nat, levelWeight j) + ∑' j : Nat, maxWeight j ≤ D := by
    change (∑' j : Nat, if 3 ≤ j then dyadicScale j else 0) +
      ∑' j : Nat, maxWeight j ≤ blockBudgetDenominator d
    rw [blockBudgetDenominator]
    simpa [add_comm] using
      (add_le_add_left hmax_tsum_le
        (∑' j : Nat, if 3 ≤ j then dyadicScale j else 0))
  have heta_tsum_bound : ∑' j, P.eta j ≤ c := by
    calc
      ∑' j, P.eta j ≤ ∑' j, major j :=
        heta_summable.tsum_le_tsum heta_le_major hmajor_summable
      _ = (c / D) * ((∑' j, levelWeight j) + ∑' j, maxWeight j) := by
        rw [show (∑' j, major j) = (c / D) *
            ∑' j, (levelWeight j + maxWeight j) by
          simp [major, tsum_mul_left]]
        rw [hlevel_summable.tsum_add hmax_summable]
      _ ≤ (c / D) * D :=
        mul_le_mul_of_nonneg_left hsum_components (div_nonneg hc.le hD.le)
      _ = c := by field_simp
  have heta_tsum_lt : ∑' j, P.eta j < mu0 / 4 := by
    apply heta_tsum_bound.trans_lt
    simp only [c]
    linarith [P.mu0_pos]
  let Ceta : Real := D / c
  have hCeta : 0 < Ceta := div_pos hD hc
  refine ⟨{
    Ceta := Ceta
    Ceta_pos := hCeta
    eta_nonneg := heta_nonneg
    eta_pos := heta_pos
    eta_summable := heta_summable
    eta_tsum_le := heta_tsum_lt
    inv_eta_le_scale := ?_
    inv_eta_le_weight := ?_ }⟩
  · intro j hj
    rw [heta_formula j hj]
    have hscale : 0 < dyadicScale j := dyadicScale_pos j
    have hmax : 0 ≤ maxWeight j := hmax_nonneg j
    have hlevel : levelWeight j = dyadicScale j := by simp [levelWeight, hj]
    rw [hlevel]
    change 1 / (c * (dyadicScale j + maxWeight j) / D) ≤
      (D / c) * (2 : Real) ^ j
    calc
      1 / (c * (dyadicScale j + maxWeight j) / D) ≤
          1 / (c * dyadicScale j / D) := by
        apply one_div_le_one_div_of_le (div_pos (mul_pos hc hscale) hD)
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hmax) hc.le) hD.le
      _ = (D / c) * (2 : Real) ^ j := by
        rw [dyadicScale_eq_inv_pow]
        field_simp [hc.ne', hD.ne']
        rw [← mul_pow]
        norm_num
  · intro j n hn
    by_cases hbelow : ¬3 ≤ j
    · rw [P.eta_eq j, if_neg hbelow]
      simp only [one_div, inv_zero]
      exact mul_nonneg hCeta.le (pow_nonneg (by positivity) _)
    · have hj : 3 ≤ j := Classical.not_not.mp hbelow
      rw [heta_formula j hj]
      have hnweight : 0 < indexWeight n := by
        rw [indexWeight]
        exact Finset.prod_pos fun _ _ ↦ zpow_pos (by positivity) _
      have hmax : indexWeight n ≤ maxWeight j := by
        exact indexWeight_le_blockWeightMax delta hdelta data.C0 hn
      have hlevel : 0 ≤ levelWeight j := hlevel_nonneg j
      have hinvWeight :
          1 / indexWeight n ≤ (1 + indexSize n : Real) ^ (2 * d + 2) := by
        let R : Real := 1 + indexSize n
        have hR : 1 ≤ R := by simp [R]
        have hcoord (i : Fin d) :
            (1 + ((n i).natAbs : Real)) ^ 2 ≤ R ^ 2 := by
          apply pow_le_pow_left₀ (by positivity)
          dsimp [R]
          have hi := indexSize_coordinate_le n i
          exact_mod_cast Nat.add_le_add_left hi 1
        have hprod :
            (∏ i : Fin d, (1 + ((n i).natAbs : Real)) ^ 2) ≤ R ^ (2 * d) := by
          calc
            (∏ i : Fin d, (1 + ((n i).natAbs : Real)) ^ 2) ≤
                ∏ _i : Fin d, R ^ 2 := by
              exact Finset.prod_le_prod (fun _ _ ↦ by positivity)
                (fun i _ ↦ hcoord i)
            _ = R ^ (2 * d) := by simp [pow_mul]
        calc
          1 / indexWeight n =
              ∏ i : Fin d, (1 + ((n i).natAbs : Real)) ^ 2 := by
            simp [indexWeight, zpow_neg]
            rfl
          _ ≤ R ^ (2 * d) := hprod
          _ ≤ R ^ (2 * d + 2) := pow_le_pow_right₀ hR (by omega)
      change 1 / (c * (levelWeight j + maxWeight j) / D) ≤
        (D / c) * (1 + indexSize n : Real) ^ (2 * d + 2)
      calc
        1 / (c * (levelWeight j + maxWeight j) / D) ≤
            1 / (c * indexWeight n / D) := by
          apply one_div_le_one_div_of_le (div_pos (mul_pos hc hnweight) hD)
          apply div_le_div_of_nonneg_right _ hD.le
          apply mul_le_mul_of_nonneg_left _ hc.le
          exact hmax.trans (le_add_of_nonneg_left hlevel)
        _ = (D / c) * (1 / indexWeight n) := by
          field_simp [hc.ne', hD.ne', hnweight.ne']
        _ ≤ (D / c) * (1 + indexSize n : Real) ^ (2 * d + 2) :=
          mul_le_mul_of_nonneg_left hinvWeight (div_nonneg hD.le hc.le)

/-- Sole constructor of the quantitative budget package. -/
noncomputable def budgetConstants {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    {data : ModifiedFrequencyData delta} {mu0 : Real}
    (P : BlockParameters hd delta hdelta data mu0) : BudgetConstants P :=
  Classical.choice (budgetConstants_nonempty P)

/-- Total normalized block-energy sequence. -/
def blockEnergyTerm {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    {data : ModifiedFrequencyData delta} {mu0 : Real}
    (P : BlockParameters hd delta hdelta data mu0)
    (H : RealVec d → Complex) (j : Nat) : Real :=
  if 3 ≤ j then
    (1 / P.eta j) *
      ∑ n ∈ dyadicBlock delta hdelta data.C0 j,
        ‖inverseSample H (frequency delta n)‖ ^ 2
  else 0

end Internal

end AsymptoticallyIntegerHD
