import AsymptoticallyIntegerHD.Definitions
import AsymptoticallyIntegerHD.PerturbedExponentials
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Algebra.Order.Chebyshev

/-!
# Striped periodic carriers

This module constructs striped periodic carriers. Its two small helper
definitions are dimension-generic counterparts of one-dimensional Gram helpers.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Pointwise

namespace AsymptoticallyIntegerHD

namespace Internal

/-- Canonical first coordinate in positive dimension. -/
def firstCoordinate {d : Nat} (hd : 0 < d) : Fin d := ⟨0, hd⟩

/-- Stable helper for the selected first-coordinate cells. -/
def selectedCells (theta : Real) (N : Nat) : Set Real :=
  ⋃ q ∈ Finset.range N,
    Set.Ioo ((q : Real) / (N : Real)) (((q : Real) + theta) / (N : Real))

end Internal

private theorem selectedCells_measurable_subset (theta : Real) (N : Nat)
    (hN : 0 < N) (_htheta0 : 0 < theta) (htheta1 : theta ≤ 1) :
    MeasurableSet (Internal.selectedCells theta N) ∧
      Internal.selectedCells theta N ⊆ Set.Ioo (0 : Real) 1 := by
  have hNR : (0 : Real) < (N : Real) := by exact_mod_cast hN
  constructor
  · simp only [Internal.selectedCells]
    exact MeasurableSet.iUnion fun _ =>
      MeasurableSet.iUnion fun _ => measurableSet_Ioo
  · intro x hx
    simp only [Internal.selectedCells, Set.mem_iUnion] at hx
    rcases hx with ⟨j, hj, hx⟩
    have hjN : j < N := Finset.mem_range.mp hj
    constructor
    · exact lt_of_le_of_lt (div_nonneg (Nat.cast_nonneg _) hNR.le) hx.1
    · refine hx.2.trans_le ?_
      rw [div_le_one hNR]
      exact_mod_cast (show (j : Real) + theta ≤ (N : Real) by
        have hj1 : (j : Real) + 1 ≤ (N : Real) := by
          exact_mod_cast (Nat.succ_le_iff.mpr hjN)
        linarith)

private theorem selectedCells_pairwiseDisjoint (theta : Real) (N : Nat)
    (hN : 0 < N) (htheta1 : theta ≤ 1) :
    Set.Pairwise (↑(Finset.range N) : Set Nat)
      (fun i j => Disjoint
        (Set.Ioo ((i : Real) / (N : Real)) (((i : Real) + theta) / (N : Real)))
        (Set.Ioo ((j : Real) / (N : Real)) (((j : Real) + theta) / (N : Real)))) := by
  have hNR : (0 : Real) < (N : Real) := by exact_mod_cast hN
  have hdis : ∀ {i j : Nat}, i < j →
      Disjoint
        (Set.Ioo ((i : Real) / (N : Real)) (((i : Real) + theta) / (N : Real)))
        (Set.Ioo ((j : Real) / (N : Real)) (((j : Real) + theta) / (N : Real))) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    have hijR : (i : Real) + theta ≤ (j : Real) := by
      have hij1 : (i : Real) + 1 ≤ (j : Real) := by
        exact_mod_cast (Nat.succ_le_iff.mpr hij)
      linarith
    have hend : ((i : Real) + theta) / (N : Real) ≤ (j : Real) / (N : Real) :=
      (div_le_div_iff_of_pos_right hNR).2 hijR
    exact (not_lt_of_ge hend) (hxj.1.trans hxi.2)
  intro i hi j hj hij
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · exact hdis hijlt
  · exact (hdis hjilt).symm

private theorem volume_selectedCells (theta : Real) (N : Nat)
    (hN : 0 < N) (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1) :
    volume (Internal.selectedCells theta N) = ENNReal.ofReal theta := by
  by_cases ht : theta = 0
  · subst theta
    simp [Internal.selectedCells]
  rw [Internal.selectedCells,
    MeasureTheory.measure_biUnion_finset
      (selectedCells_pairwiseDisjoint theta N hN htheta1)
      (fun _ _ => measurableSet_Ioo)]
  simp_rw [Real.volume_Ioo]
  have hcell (j : Nat) :
      (((j : Real) + theta) / (N : Real) - (j : Real) / (N : Real)) =
        theta / (N : Real) := by ring
  simp_rw [hcell]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg N)]
  congr 1
  field_simp

private theorem selectedCells_integral_error (f : Real → Complex) (L theta : Real)
    (N : Nat) (hLip : ∀ x y : Real, ‖f x - f y‖ ≤ L * |x - y|)
    (hN : 0 < N) (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1) :
    ‖(∫ t in Internal.selectedCells theta N, f t) -
        (theta : Complex) * ∫ t in Set.Ioo (0 : Real) 1, f t‖ ≤
      2 * theta * L / (N : Real) := by
  have hNR : (0 : Real) < (N : Real) := by exact_mod_cast hN
  have hL : 0 ≤ L := by
    exact (norm_nonneg (f 0 - f 1)).trans (by simpa using hLip 0 1)
  have hfLip : LipschitzWith ⟨L, hL⟩ f := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (f x) (f y) ≤ L * dist x y
    simpa [dist_eq_norm, Real.norm_eq_abs] using hLip x y
  have hfcont : Continuous f := hfLip.continuous
  let left : Nat → Real := fun j => (j : Real) / (N : Real)
  let selectedRight : Nat → Real := fun j => ((j : Real) + theta) / (N : Real)
  let cellRight : Nat → Real := fun j => ((j : Real) + 1) / (N : Real)
  have hsel_order (j : Nat) : left j ≤ selectedRight j := by
    apply (div_le_div_iff_of_pos_right hNR).2
    linarith
  have hcell_order (j : Nat) : left j ≤ cellRight j := by
    apply (div_le_div_iff_of_pos_right hNR).2
    linarith
  have hsel_int (j : Nat) :
      IntervalIntegrable f volume (left j) (selectedRight j) :=
    hfcont.intervalIntegrable _ _
  have hcell_int (j : Nat) :
      IntervalIntegrable f volume (left j) (cellRight j) :=
    hfcont.intervalIntegrable _ _
  have hperiod :
      (∫ t in Internal.selectedCells theta N, f t) =
        ∑ j ∈ Finset.range N, ∫ t in left j..selectedRight j, f t := by
    rw [Internal.selectedCells,
      MeasureTheory.integral_biUnion_finset (Finset.range N)
        (fun _ _ => measurableSet_Ioo)
        (selectedCells_pairwiseDisjoint theta N hN htheta1)]
    · apply Finset.sum_congr rfl
      intro j hj
      symm
      rw [intervalIntegral.integral_of_le (hsel_order j),
        MeasureTheory.integral_Ioc_eq_integral_Ioo]
    · intro j hj
      exact (intervalIntegrable_iff_integrableOn_Ioo_of_le (hsel_order j)).mp
        (hsel_int j)
  have hfull :
      (∫ t in Set.Ioo (0 : Real) 1, f t) =
        ∑ j ∈ Finset.range N, ∫ t in left j..cellRight j, f t := by
    have hadj := intervalIntegral.sum_integral_adjacent_intervals
      (f := f) (μ := volume) (a := fun j : Nat => (j : Real) / (N : Real))
      (n := N) (fun j hj => hfcont.intervalIntegrable _ _)
    have hadj' :
        (∑ j ∈ Finset.range N, ∫ t in left j..cellRight j, f t) =
          ∫ t in (0 : Real)..1, f t := by
      simpa [left, cellRight, hN.ne'] using hadj
    calc
      (∫ t in Set.Ioo (0 : Real) 1, f t) = ∫ t in (0 : Real)..1, f t := by
        rw [intervalIntegral.integral_of_le (show (0 : Real) ≤ 1 by norm_num),
          MeasureTheory.integral_Ioc_eq_integral_Ioo]
      _ = _ := hadj'.symm
  let remainder : Nat → Real → Complex := fun j t => f t - f (left j)
  have hrem_sel (j : Nat) :
      ‖∫ t in left j..selectedRight j, remainder j t‖ ≤
        (L / (N : Real)) * (theta / (N : Real)) := by
    refine (intervalIntegral.norm_integral_le_of_norm_le_const
      (C := L / (N : Real)) ?_).trans_eq ?_
    · intro x hx
      have hx' : x ∈ Set.Ioc (left j) (selectedRight j) := by
        simpa [Set.uIoc_of_le (hsel_order j)] using hx
      have hdist0 : 0 ≤ x - left j := sub_nonneg.mpr hx'.1.le
      have hdist : |x - left j| ≤ 1 / (N : Real) := by
        rw [abs_of_nonneg hdist0]
        have htheta_div : theta / (N : Real) ≤ 1 / (N : Real) :=
          (div_le_div_iff_of_pos_right hNR).2 htheta1
        have hxright : x - left j ≤ theta / (N : Real) := by
          calc
            x - left j ≤ selectedRight j - left j := sub_le_sub_right hx'.2 _
            _ = theta / (N : Real) := by
              dsimp [left, selectedRight]
              ring
        exact hxright.trans htheta_div
      exact (hLip x (left j)).trans (by
        simpa only [div_eq_mul_inv, one_mul] using
          mul_le_mul_of_nonneg_left hdist hL)
    · have hdiff : selectedRight j - left j = theta / (N : Real) := by
        dsimp [left, selectedRight]
        ring
      rw [hdiff, abs_of_nonneg (div_nonneg htheta0 hNR.le)]
  have hrem_cell (j : Nat) :
      ‖∫ t in left j..cellRight j, remainder j t‖ ≤
        (L / (N : Real)) * (1 / (N : Real)) := by
    refine (intervalIntegral.norm_integral_le_of_norm_le_const
      (C := L / (N : Real)) ?_).trans_eq ?_
    · intro x hx
      have hx' : x ∈ Set.Ioc (left j) (cellRight j) := by
        simpa [Set.uIoc_of_le (hcell_order j)] using hx
      have hdist0 : 0 ≤ x - left j := sub_nonneg.mpr hx'.1.le
      have hdist : |x - left j| ≤ 1 / (N : Real) := by
        rw [abs_of_nonneg hdist0]
        calc
          x - left j ≤ cellRight j - left j := sub_le_sub_right hx'.2 _
          _ = 1 / (N : Real) := by
            dsimp [left, cellRight]
            ring
      exact (hLip x (left j)).trans (by
        simpa only [div_eq_mul_inv, one_mul] using
          mul_le_mul_of_nonneg_left hdist hL)
    · have hdiff : cellRight j - left j = 1 / (N : Real) := by
        dsimp [left, cellRight]
        ring
      rw [hdiff, abs_of_nonneg (div_nonneg zero_le_one hNR.le)]
  have hsel_expand (j : Nat) :
      (∫ t in left j..selectedRight j, f t) =
        (∫ t in left j..selectedRight j, remainder j t) +
          ((theta / (N : Real) : Real) : Complex) * f (left j) := by
    have hg : IntervalIntegrable (remainder j) volume (left j) (selectedRight j) :=
      (hfcont.sub continuous_const).intervalIntegrable _ _
    calc
      (∫ t in left j..selectedRight j, f t) =
          ∫ t in left j..selectedRight j, remainder j t + f (left j) := by
        apply intervalIntegral.integral_congr
        intro x hx
        simp [remainder]
      _ = (∫ t in left j..selectedRight j, remainder j t) +
          ∫ _t in left j..selectedRight j, f (left j) := by
        rw [intervalIntegral.integral_add hg (continuous_const.intervalIntegrable _ _)]
      _ = _ := by
        rw [intervalIntegral.integral_const]
        congr 2
        · dsimp [left, selectedRight]
          ring_nf
          exact (div_eq_mul_inv theta (N : Real)).symm
  have hcell_expand (j : Nat) :
      (∫ t in left j..cellRight j, f t) =
        (∫ t in left j..cellRight j, remainder j t) +
          (((1 / (N : Real) : Real) : Complex) * f (left j)) := by
    have hg : IntervalIntegrable (remainder j) volume (left j) (cellRight j) :=
      (hfcont.sub continuous_const).intervalIntegrable _ _
    calc
      (∫ t in left j..cellRight j, f t) =
          ∫ t in left j..cellRight j, remainder j t + f (left j) := by
        apply intervalIntegral.integral_congr
        intro x hx
        simp [remainder]
      _ = (∫ t in left j..cellRight j, remainder j t) +
          ∫ _t in left j..cellRight j, f (left j) := by
        rw [intervalIntegral.integral_add hg (continuous_const.intervalIntegrable _ _)]
      _ = _ := by
        rw [intervalIntegral.integral_const]
        congr 2
        · dsimp [left, cellRight]
          ring_nf
          exact (one_div (N : Real)).symm
  have hcell_error (j : Nat) :
      ‖(∫ t in left j..selectedRight j, f t) -
          (theta : Complex) * (∫ t in left j..cellRight j, f t)‖ ≤
        2 * theta * L / (N : Real) ^ 2 := by
    have heq :
        (∫ t in left j..selectedRight j, f t) -
            (theta : Complex) * (∫ t in left j..cellRight j, f t) =
          (∫ t in left j..selectedRight j, remainder j t) -
            (theta : Complex) * (∫ t in left j..cellRight j, remainder j t) := by
      rw [hsel_expand, hcell_expand]
      push_cast
      field_simp
      ring
    rw [heq]
    calc
      ‖(∫ t in left j..selectedRight j, remainder j t) -
          (theta : Complex) * (∫ t in left j..cellRight j, remainder j t)‖ ≤
          ‖∫ t in left j..selectedRight j, remainder j t‖ +
            ‖(theta : Complex) * (∫ t in left j..cellRight j, remainder j t)‖ :=
        norm_sub_le _ _
      _ = ‖∫ t in left j..selectedRight j, remainder j t‖ +
            theta * ‖∫ t in left j..cellRight j, remainder j t‖ := by
        rw [norm_mul]
        simp [abs_of_nonneg htheta0]
      _ ≤ (L / (N : Real)) * (theta / (N : Real)) +
            theta * ((L / (N : Real)) * (1 / (N : Real))) := by
        exact add_le_add (hrem_sel j)
          (mul_le_mul_of_nonneg_left (hrem_cell j) htheta0)
      _ = 2 * theta * L / (N : Real) ^ 2 := by
        field_simp
        ring
  rw [hperiod, hfull, Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    ‖∑ j ∈ Finset.range N,
        ((∫ t in left j..selectedRight j, f t) -
          (theta : Complex) * (∫ t in left j..cellRight j, f t))‖ ≤
        ∑ j ∈ Finset.range N,
          ‖(∫ t in left j..selectedRight j, f t) -
            (theta : Complex) * (∫ t in left j..cellRight j, f t)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range N, 2 * theta * L / (N : Real) ^ 2 := by
      gcongr with j hj
      exact hcell_error j
    _ = 2 * theta * L / (N : Real) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp

private theorem unitCube_eq_pi_Ioo (d : Nat) :
    unitCube d = Set.univ.pi (fun _ : Fin d => Set.Ioo (0 : Real) 1) := by
  ext x
  simp [unitCube]

/-- The first `theta` portion of each first-coordinate cell. -/
def stripedCarrier {d : Nat} (hd : 0 < d) (theta : Real) (N : Nat) :
    Set (RealVec d) :=
  unitCube d ∩
    {x | x (Internal.firstCoordinate hd) ∈ Internal.selectedCells theta N}

private theorem stripedCarrier_eq_pi {d : Nat} (hd : 0 < d)
    (theta : Real) (N : Nat) (hN : 0 < N) (htheta0 : 0 ≤ theta)
    (htheta1 : theta ≤ 1) :
    stripedCarrier hd theta N = Set.univ.pi (fun i : Fin d =>
      if i = Internal.firstCoordinate hd then Internal.selectedCells theta N
      else Set.Ioo (0 : Real) 1) := by
  ext x
  simp only [stripedCarrier, unitCube, Set.mem_inter_iff, Set.mem_setOf_eq,
    Set.mem_pi, Set.mem_univ, true_implies]
  constructor
  · rintro ⟨hx, hsel⟩ i
    split_ifs with hi
    · simpa [hi] using hsel
    · exact hx i
  · intro hx
    constructor
    · intro i
      by_cases hi : i = Internal.firstCoordinate hd
      · subst i
        by_cases ht : theta = 0
        · subst theta
          exfalso
          simpa [Internal.selectedCells] using hx (Internal.firstCoordinate hd)
        · exact (selectedCells_measurable_subset theta N hN
            (lt_of_le_of_ne htheta0 (Ne.symm ht)) htheta1).2
              (by simpa using hx (Internal.firstCoordinate hd))
      · simpa [hi] using hx i
    · simpa using hx (Internal.firstCoordinate hd)

/-- Measurability, cube containment, and exact product volume. -/
theorem stripedCarrier_measurable_volume {d : Nat} (hd : 0 < d)
    (theta : Real) (N : Nat) (hN : 0 < N) (htheta0 : 0 ≤ theta)
    (htheta1 : theta ≤ 1) :
    MeasurableSet (stripedCarrier hd theta N) ∧
      stripedCarrier hd theta N ⊆ unitCube d ∧
      volume (stripedCarrier hd theta N) = ENNReal.ofReal theta := by
  rw [stripedCarrier_eq_pi hd theta N hN htheta0 htheta1]
  constructor
  · apply MeasurableSet.univ_pi
    intro i
    split_ifs
    · exact (by
        by_cases ht : theta = 0
        · subst theta
          simp [Internal.selectedCells]
        · exact (selectedCells_measurable_subset theta N hN
            (lt_of_le_of_ne htheta0 (Ne.symm ht)) htheta1).1)
    · exact measurableSet_Ioo
  constructor
  · intro x hx
    rw [unitCube_eq_pi_Ioo]
    intro i hi
    by_cases hi0 : i = Internal.firstCoordinate hd
    · subst i
      by_cases ht : theta = 0
      · subst theta
        exfalso
        simpa [Internal.selectedCells] using hx (Internal.firstCoordinate hd)
      · exact (selectedCells_measurable_subset theta N hN
          (lt_of_le_of_ne htheta0 (Ne.symm ht)) htheta1).2
            (by simpa using hx (Internal.firstCoordinate hd))
    · simpa [hi0] using hx i
  · rw [MeasureTheory.volume_pi_pi]
    calc
      (∏ i, volume (if i = Internal.firstCoordinate hd then
          Internal.selectedCells theta N else Set.Ioo (0 : Real) 1)) =
          ∏ i, if i = Internal.firstCoordinate hd then ENNReal.ofReal theta else 1 := by
        apply Finset.prod_congr rfl
        intro i hi
        split_ifs
        · exact volume_selectedCells theta N hN htheta0 htheta1
        · simp [Real.volume_Ioo]
      _ = ENNReal.ofReal theta := by simp

namespace Internal

private def coordinateCharacter {d : Nat} (r : RealVec d) (i : Fin d)
    (t : Real) : Complex :=
  Complex.exp ((((2 * Real.pi * r i * t : Real)) : Complex) * Complex.I)

private theorem coordinateCharacter_lipschitz {d : Nat} (r : RealVec d)
    (i : Fin d) :
    ∀ x y : Real,
      ‖coordinateCharacter r i x - coordinateCharacter r i y‖ ≤
        (2 * Real.pi * |r i|) * |x - y| := by
  intro x y
  let c : Real := 2 * Real.pi * r i
  have hfactor :
      Complex.exp (((c * x : Real) : Complex) * Complex.I) -
          Complex.exp (((c * y : Real) : Complex) * Complex.I) =
        Complex.exp (((c * y : Real) : Complex) * Complex.I) *
          (Complex.exp (Complex.I * ((c * (x - y) : Real) : Complex)) - 1) := by
    rw [mul_sub]
    simp only [mul_one]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring_nf
  unfold coordinateCharacter
  rw [show (2 * Real.pi * r i : Real) = c by rfl]
  rw [hfactor, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  refine (Real.norm_exp_I_mul_ofReal_sub_one_le).trans_eq ?_
  simp only [Real.norm_eq_abs, abs_mul]
  dsimp [c]
  rw [abs_mul, abs_of_pos (mul_pos (by positivity) Real.pi_pos)]

private theorem fourierChar_eq_prod_coordinateCharacter {d : Nat}
    (r x : RealVec d) :
    fourierChar r x = ∏ i : Fin d, coordinateCharacter r i (x i) := by
  unfold fourierChar
  simp_rw [coordinateCharacter, ← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

private theorem integral_fourierChar_pi {d : Nat} (r : RealVec d)
    (s : Fin d → Set Real) :
    (∫ x in Set.univ.pi s, fourierChar r x) =
      ∏ i : Fin d, ∫ t in s i, coordinateCharacter r i t := by
  rw [MeasureTheory.volume_pi]
  change (∫ x, fourierChar r x ∂
    ((Measure.pi fun _ : Fin d => volume).restrict (Set.univ.pi s))) = _
  have hrestrict :
      (Measure.pi fun _ : Fin d => volume).restrict (Set.univ.pi s) =
        Measure.pi (fun i : Fin d => volume.restrict (s i)) :=
    Measure.restrict_pi_pi (fun _ : Fin d => volume) s
  rw [hrestrict]
  simp_rw [fourierChar_eq_prod_coordinateCharacter]
  exact MeasureTheory.integral_fintype_prod_eq_prod _

/-- Product-Fubini factorization of selected and full cubes. -/
theorem character_integral_striped_factorization {d : Nat} (hd : 0 < d)
    (theta : Real) (N : Nat) (hN : 0 < N) (htheta0 : 0 ≤ theta)
    (htheta1 : theta ≤ 1) (r : RealVec d) :
    (∫ x in stripedCarrier hd theta N, fourierChar r x) =
        (∫ t in selectedCells theta N,
          Complex.exp ((((2 * Real.pi * r (firstCoordinate hd) * t : Real)) :
            Complex) * Complex.I)) *
          ∏ i ∈ (Finset.univ.erase (firstCoordinate hd)),
            ∫ t in Set.Ioo (0 : Real) 1,
              Complex.exp ((((2 * Real.pi * r i * t : Real)) : Complex) *
                Complex.I) ∧
      (∫ x in unitCube d, fourierChar r x) =
        (∫ t in Set.Ioo (0 : Real) 1,
          Complex.exp ((((2 * Real.pi * r (firstCoordinate hd) * t : Real)) :
            Complex) * Complex.I)) *
          ∏ i ∈ (Finset.univ.erase (firstCoordinate hd)),
            ∫ t in Set.Ioo (0 : Real) 1,
              Complex.exp ((((2 * Real.pi * r i * t : Real)) : Complex) *
                Complex.I) := by
  let sStripe : Fin d → Set Real := fun i =>
    if i = firstCoordinate hd then selectedCells theta N else Set.Ioo (0 : Real) 1
  let sCube : Fin d → Set Real := fun _ => Set.Ioo (0 : Real) 1
  constructor
  · rw [stripedCarrier_eq_pi hd theta N hN htheta0 htheta1]
    change (∫ x in Set.univ.pi sStripe, fourierChar r x) = _
    rw [integral_fourierChar_pi r sStripe]
    rw [← Finset.mul_prod_erase Finset.univ
      (fun i => ∫ t in sStripe i, coordinateCharacter r i t)
      (Finset.mem_univ (firstCoordinate hd))]
    have hprod :
        (∏ i ∈ Finset.univ.erase (firstCoordinate hd),
          ∫ t in sStripe i, coordinateCharacter r i t) =
        ∏ i ∈ Finset.univ.erase (firstCoordinate hd),
          ∫ t in Set.Ioo (0 : Real) 1,
            Complex.exp ((((2 * Real.pi * r i * t : Real)) : Complex) *
              Complex.I) := by
      apply Finset.prod_congr rfl
      intro i hi
      have hne : i ≠ firstCoordinate hd := (Finset.mem_erase.mp hi).1
      simp [sStripe, coordinateCharacter, hne]
    rw [hprod]
    simp [sStripe, coordinateCharacter]
  · rw [unitCube_eq_pi_Ioo]
    change (∫ x in Set.univ.pi sCube, fourierChar r x) = _
    rw [integral_fourierChar_pi r sCube]
    rw [← Finset.mul_prod_erase Finset.univ
      (fun i => ∫ t in sCube i, coordinateCharacter r i t)
      (Finset.mem_univ (firstCoordinate hd))]
    simp only [sCube, coordinateCharacter]

end Internal

/-- Quantitative selected-coordinate character error. -/
theorem stripedCarrier_character_integral_error {d : Nat} (hd : 0 < d)
    (theta : Real) (N : Nat) (hN : 0 < N) (htheta0 : 0 ≤ theta)
    (htheta1 : theta ≤ 1) (r : RealVec d) :
    ‖(∫ x in stripedCarrier hd theta N, fourierChar r x) -
        (theta : Complex) * ∫ x in unitCube d, fourierChar r x‖ ≤
      4 * theta * Real.pi * |r (Internal.firstCoordinate hd)| / (N : Real) := by
  rcases Internal.character_integral_striped_factorization
    hd theta N hN htheta0 htheta1 r with ⟨hstripe, hcube⟩
  rw [hstripe, hcube]
  let i0 := Internal.firstCoordinate hd
  let P : Complex :=
    ∏ i ∈ Finset.univ.erase i0,
      ∫ t in Set.Ioo (0 : Real) 1,
        Complex.exp ((((2 * Real.pi * r i * t : Real)) : Complex) * Complex.I)
  have hcoordinate (i : Fin d) :
      ‖∫ t in Set.Ioo (0 : Real) 1, Internal.coordinateCharacter r i t‖ ≤ 1 := by
    refine (MeasureTheory.norm_setIntegral_le_of_norm_le_const
      (μ := volume) (f := Internal.coordinateCharacter r i)
      (C := 1)
      (by simp [Real.volume_Ioo]) ?_).trans_eq ?_
    · intro t ht
      unfold Internal.coordinateCharacter
      rw [Complex.norm_exp]
      norm_num
    · simp [Measure.real, Real.volume_Ioo]
  have hP : ‖P‖ ≤ 1 := by
    dsimp [P]
    rw [norm_prod]
    apply (Finset.prod_le_prod (fun i hi => norm_nonneg _)
      (fun i hi => ?_)).trans_eq (Finset.prod_const_one)
    have hi := hcoordinate i
    simpa [Internal.coordinateCharacter] using hi
  have hfirst := selectedCells_integral_error
    (Internal.coordinateCharacter r i0) (2 * Real.pi * |r i0|) theta N
    (Internal.coordinateCharacter_lipschitz r i0) hN htheta0 htheta1
  change ‖(∫ t in Internal.selectedCells theta N,
      Internal.coordinateCharacter r i0 t) * P -
    (theta : Complex) *
      ((∫ t in Set.Ioo (0 : Real) 1,
        Internal.coordinateCharacter r i0 t) * P)‖ ≤ _
  change _ ≤ 4 * theta * Real.pi * |r i0| / (N : Real)
  rw [← mul_assoc, ← sub_mul, norm_mul]
  calc
    ‖(∫ t in Internal.selectedCells theta N,
        Internal.coordinateCharacter r i0 t) -
      (theta : Complex) *
        ∫ t in Set.Ioo (0 : Real) 1,
          Internal.coordinateCharacter r i0 t‖ * ‖P‖ ≤
        (2 * theta * (2 * Real.pi * |r i0|) / (N : Real)) * 1 := by
      exact mul_le_mul hfirst hP (norm_nonneg _) (by positivity)
    _ = 4 * theta * Real.pi * |r i0| / (N : Real) := by ring

namespace Internal

/-- Gram matrix with orientation `nu i - nu j`. -/
def gramMatrix {d : Nat} (nu : IntVec d → RealVec d) (D : Finset (IntVec d))
    (Omega : Set (RealVec d)) :
    Matrix {n : IntVec d // n ∈ D} {n : IntVec d // n ∈ D} Complex :=
  fun i j => ∫ x in Omega, fourierChar (nu i.1 - nu j.1) x

/-- Dimension-generic conjugate-first quadratic. -/
def gramQuadratic {ι : Type*} [Fintype ι]
    (G : Matrix ι ι Complex) (a : ι → Complex) : Complex :=
  ∑ i, starRingEnd Complex (a i) * (G.mulVec a) i

/-- Gram quadratic equals the finite negative-synthesis energy. -/
theorem gramQuadratic_eq_sqNormOn {d : Nat} (nu : IntVec d → RealVec d)
    (D : Finset (IntVec d)) (Omega : Set (RealVec d))
    (hOmega : Omega = unitCube d ∨
      ∃ (hd : 0 < d) (theta : Real) (N : Nat), 0 < N ∧ 0 ≤ theta ∧
        theta ≤ 1 ∧ Omega = stripedCarrier hd theta N)
    (a : {n : IntVec d // n ∈ D} → Complex) :
    gramQuadratic (gramMatrix nu D Omega) a =
        ((sqNormOn Omega (fun x =>
          ∑ n, a n * starRingEnd Complex (fourierChar (nu n.1) x)) : Real) :
            Complex) ∧
      (gramQuadratic (gramMatrix nu D Omega) a).im = 0 ∧
      (gramQuadratic (gramMatrix nu D Omega) a).re =
        sqNormOn Omega (fun x =>
          ∑ n, a n * starRingEnd Complex (fourierChar (nu n.1) x)) := by
  have hsub : Omega ⊆ unitCube d := by
    rcases hOmega with h | ⟨hd, theta, N, hN, ht0, ht1, rfl⟩
    · subst Omega
      exact Set.Subset.rfl
    · exact (stripedCarrier_measurable_volume hd theta N hN ht0 ht1).2.1
  have hcubeFinite : volume (unitCube d) < ∞ := by
    rw [unitCube_eq_pi_Ioo, Real.volume_pi_Ioo]
    simp
  have hfinite : volume Omega < ∞ := (measure_mono hsub).trans_lt hcubeFinite
  let chi : RealVec d → RealVec d → Complex := fun r x => fourierChar r x
  have hchi (r : RealVec d) : Integrable (chi r) (volume.restrict Omega) := by
    have hcont : Continuous (chi r) := by
      dsimp [chi, fourierChar]
      fun_prop
    refine MeasureTheory.IntegrableOn.of_bound hfinite
      hcont.aestronglyMeasurable 1 ?_
    filter_upwards [] with x
    dsimp [chi, fourierChar]
    rw [Complex.norm_exp]
    norm_num
  have hterm (i j : {n : IntVec d // n ∈ D}) :
      Integrable (fun x => chi (nu i.1 - nu j.1) x * a j)
        (volume.restrict Omega) :=
    (hchi _).mul_const _
  have hrow (i : {n : IntVec d // n ∈ D}) :
      Integrable (fun x => ∑ j, chi (nu i.1 - nu j.1) x * a j)
        (volume.restrict Omega) :=
    MeasureTheory.integrable_finsetSum Finset.univ (fun j _ => hterm i j)
  have houter (i : {n : IntVec d // n ∈ D}) :
      Integrable (fun x => starRingEnd Complex (a i) *
        ∑ j, chi (nu i.1 - nu j.1) x * a j)
        (volume.restrict Omega) :=
    (hrow i).const_mul _
  have heq : gramQuadratic (gramMatrix nu D Omega) a =
      ((sqNormOn Omega (fun x =>
        ∑ n, a n * starRingEnd Complex (fourierChar (nu n.1) x)) : Real) :
          Complex) := by
    calc
      gramQuadratic (gramMatrix nu D Omega) a =
          ∑ i, starRingEnd Complex (a i) *
            ∑ j, (∫ x in Omega, chi (nu i.1 - nu j.1) x) * a j := by
        rfl
      _ = ∑ i, starRingEnd Complex (a i) *
            ∑ j, (∫ x in Omega, chi (nu i.1 - nu j.1) x * a j) := by
        simp_rw [MeasureTheory.integral_mul_const]
      _ = ∑ i, starRingEnd Complex (a i) *
            (∫ x in Omega, ∑ j, chi (nu i.1 - nu j.1) x * a j) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [MeasureTheory.integral_finsetSum Finset.univ (fun j _ => hterm i j)]
      _ = ∑ i, (∫ x in Omega, starRingEnd Complex (a i) *
            ∑ j, chi (nu i.1 - nu j.1) x * a j) := by
        simp_rw [MeasureTheory.integral_const_mul]
      _ = ∫ x in Omega, ∑ i, starRingEnd Complex (a i) *
            ∑ j, chi (nu i.1 - nu j.1) x * a j := by
        rw [MeasureTheory.integral_finsetSum Finset.univ (fun i _ => houter i)]
      _ = ∫ x in Omega, ((‖∑ n, a n *
            starRingEnd Complex (fourierChar (nu n.1) x)‖ ^ 2 : Real) :
              Complex) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [] with x
        rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
        rw [map_sum]
        simp_rw [map_mul]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        have hchar :
            fourierChar (nu i.1) x *
                starRingEnd Complex (fourierChar (nu j.1) x) =
              chi (nu i.1 - nu j.1) x := by
          have hstar :
              starRingEnd Complex (fourierChar (nu j.1) x) =
                Complex.exp
                  ((((-2 * Real.pi : Real) : Complex) * Complex.I) *
                    ((∑ k : Fin d, nu j.1 k * x k : Real) : Complex)) := by
            unfold fourierChar
            rw [← Complex.exp_conj]
            congr 1
            apply Complex.ext <;> simp
          dsimp [chi]
          rw [hstar]
          unfold fourierChar
          rw [← Complex.exp_add]
          congr 1
          push_cast
          simp only [Pi.sub_apply]
          have hsumC :
              (∑ k : Fin d,
                ((nu i.1 k - nu j.1 k : Real) : Complex) * (x k : Complex)) =
                (∑ k : Fin d, (nu i.1 k : Complex) * (x k : Complex)) -
                  ∑ k : Fin d, (nu j.1 k : Complex) * (x k : Complex) := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro k hk
            push_cast
            ring
          rw [hsumC]
          ring
        rw [← hchar]
        rw [starRingEnd_self_apply]
        ring
      _ = ((sqNormOn Omega (fun x =>
          ∑ n, a n * starRingEnd Complex (fourierChar (nu n.1) x)) : Real) :
            Complex) := by
        unfold sqNormOn
        exact integral_ofReal
  refine ⟨heq, ?_, ?_⟩
  · rw [heq]
    simp
  · rw [heq]
    simp

/-- Finite selected-coordinate diameter, zero on the empty product. -/
def selectedFrequencyDiameter {d : Nat} (hd : 0 < d)
    (nu : IntVec d → RealVec d) (D : Finset (IntVec d)) : Real :=
  if h : (D.product D).Nonempty then
    (D.product D).sup' h
      (fun p => |nu p.1 (firstCoordinate hd) - nu p.2 (firstCoordinate hd)|)
  else 0

private theorem selectedFrequencyDiameter_nonneg {d : Nat} (hd : 0 < d)
    (nu : IntVec d → RealVec d) (D : Finset (IntVec d)) :
    0 ≤ selectedFrequencyDiameter hd nu D := by
  unfold selectedFrequencyDiameter
  split_ifs with h
  · rcases h with ⟨p, hp⟩
    exact (abs_nonneg (nu p.1 (firstCoordinate hd) -
      nu p.2 (firstCoordinate hd))).trans
        (Finset.le_sup' (fun q => |nu q.1 (firstCoordinate hd) -
          nu q.2 (firstCoordinate hd)|) hp)
  · exact le_rfl

private theorem abs_selected_sub_le_selectedFrequencyDiameter {d : Nat}
    (hd : 0 < d) (nu : IntVec d → RealVec d) (D : Finset (IntVec d))
    {i j : IntVec d} (hi : i ∈ D) (hj : j ∈ D) :
    |nu i (firstCoordinate hd) - nu j (firstCoordinate hd)| ≤
      selectedFrequencyDiameter hd nu D := by
  unfold selectedFrequencyDiameter
  have hp : (i, j) ∈ D.product D := Finset.mem_product.mpr ⟨hi, hj⟩
  rw [dif_pos ⟨(i, j), hp⟩]
  exact Finset.le_sup'
    (fun p => |nu p.1 (firstCoordinate hd) - nu p.2 (firstCoordinate hd)|) hp

end Internal

/-- Entrywise striped Gram error. -/
theorem stripedCarrier_gram_error {d : Nat} (hd : 0 < d)
    (theta : Real) (N : Nat) (hN : 0 < N) (htheta0 : 0 ≤ theta)
    (htheta1 : theta ≤ 1) (D : Finset (IntVec d))
    (nu : IntVec d → RealVec d) (a : {n : IntVec d // n ∈ D} → Complex) :
    ‖Internal.gramQuadratic
        (Internal.gramMatrix nu D (stripedCarrier hd theta N)) a -
      (theta : Complex) * Internal.gramQuadratic
        (Internal.gramMatrix nu D (unitCube d)) a‖ ≤
      (D.card : Real) *
        (4 * theta * Real.pi * Internal.selectedFrequencyDiameter hd nu D /
          (N : Real)) * ∑ n, ‖a n‖ ^ 2 := by
  let entryError : {n : IntVec d // n ∈ D} →
      {n : IntVec d // n ∈ D} → Complex := fun i j =>
    (∫ x in stripedCarrier hd theta N,
      fourierChar (nu i.1 - nu j.1) x) -
    (theta : Complex) * ∫ x in unitCube d,
      fourierChar (nu i.1 - nu j.1) x
  have hentry (i j : {n : IntVec d // n ∈ D}) :
      ‖entryError i j‖ ≤
        4 * theta * Real.pi * Internal.selectedFrequencyDiameter hd nu D /
          (N : Real) := by
    have hraw := stripedCarrier_character_integral_error hd theta N hN htheta0
      htheta1 (nu i.1 - nu j.1)
    unfold entryError
    calc
      _ ≤ 4 * theta * Real.pi *
          |(nu i.1 - nu j.1) (Internal.firstCoordinate hd)| / (N : Real) := hraw
      _ ≤ 4 * theta * Real.pi * Internal.selectedFrequencyDiameter hd nu D /
          (N : Real) := by
        have hdiam := Internal.abs_selected_sub_le_selectedFrequencyDiameter
          hd nu D i.property j.property
        have hNR : (0 : Real) < (N : Real) := by exact_mod_cast hN
        have hfactor : 0 ≤ 4 * theta * Real.pi / (N : Real) := by positivity
        simp only [Pi.sub_apply]
        calc
          4 * theta * Real.pi *
              |nu i.1 (Internal.firstCoordinate hd) -
                nu j.1 (Internal.firstCoordinate hd)| / (N : Real) =
              (4 * theta * Real.pi / (N : Real)) *
                |nu i.1 (Internal.firstCoordinate hd) -
                  nu j.1 (Internal.firstCoordinate hd)| := by ring
          _ ≤ (4 * theta * Real.pi / (N : Real)) *
              Internal.selectedFrequencyDiameter hd nu D :=
            mul_le_mul_of_nonneg_left hdiam hfactor
          _ = _ := by ring
  have heq :
      Internal.gramQuadratic
          (Internal.gramMatrix nu D (stripedCarrier hd theta N)) a -
        (theta : Complex) * Internal.gramQuadratic
          (Internal.gramMatrix nu D (unitCube d)) a =
      ∑ i, ∑ j, starRingEnd Complex (a i) * entryError i j * a j := by
    unfold Internal.gramQuadratic Internal.gramMatrix entryError
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [heq]
  let C : Real :=
    4 * theta * Real.pi * Internal.selectedFrequencyDiameter hd nu D / (N : Real)
  have hC : 0 ≤ C := by
    dsimp [C]
    have := Internal.selectedFrequencyDiameter_nonneg hd nu D
    positivity
  calc
    ‖∑ i, ∑ j, starRingEnd Complex (a i) * entryError i j * a j‖ ≤
        ∑ i, ∑ j, ‖starRingEnd Complex (a i) * entryError i j * a j‖ := by
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
    _ ≤ ∑ i, ∑ j, C * ‖a i‖ * ‖a j‖ := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      calc
        ‖starRingEnd Complex (a i) * entryError i j * a j‖ =
            ‖a i‖ * ‖entryError i j‖ * ‖a j‖ := by simp
        _ ≤ ‖a i‖ * C * ‖a j‖ := by
          gcongr
          exact hentry i j
        _ = C * ‖a i‖ * ‖a j‖ := by ring
    _ = ∑ i, (C * ‖a i‖) * (∑ j, ‖a j‖) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
    _ = C * (∑ i, ‖a i‖) ^ 2 := by
      rw [← Finset.sum_mul, ← Finset.mul_sum]
      ring
    _ ≤ C * ((Fintype.card {n : IntVec d // n ∈ D} : Real) *
        ∑ i, ‖a i‖ ^ 2) := by
      gcongr
      simpa only [Finset.card_univ] using
        (sq_sum_le_card_mul_sum_sq (s := Finset.univ)
          (f := fun i : {n : IntVec d // n ∈ D} => ‖a i‖))
    _ = (D.card : Real) *
        (4 * theta * Real.pi * Internal.selectedFrequencyDiameter hd nu D /
          (N : Real)) * ∑ i, ‖a i‖ ^ 2 := by
      simp only [C, Fintype.card_coe]
      ring

set_option linter.unusedVariables false in
/-- Existence of an exact-measure coercive striped carrier. -/
theorem exists_coercive_stripedCarrier {d : Nat} (hd : 0 < d)
    {nu : IntVec d → RealVec d} (K : ExponentialBoundsHD nu)
    (D : Finset (IntVec d)) (hD : D.Nonempty) (theta : Real)
    (htheta0 : 0 < theta) (htheta1 : theta ≤ 1) :
    ∃ N : Nat, ∃ hN : 0 < N,
      let Omega := stripedCarrier hd theta N
      MeasurableSet Omega ∧ Omega ⊆ unitCube d ∧
        volume Omega = ENNReal.ofReal theta ∧
        ∀ a : {n : IntVec d // n ∈ D} → Complex,
          (K.lower * theta / 2) * ∑ n, ‖a n‖ ^ 2 ≤
            (Internal.gramQuadratic (Internal.gramMatrix nu D Omega) a).re := by
  have _hD := hD
  let target : Real := K.lower * theta / 2
  have htarget : 0 < target := by
    dsimp [target]
    exact div_pos (mul_pos K.lower_pos htheta0) (by norm_num)
  let A : Real :=
    (D.card : Real) *
      (4 * theta * Real.pi * Internal.selectedFrequencyDiameter hd nu D)
  have hA : 0 ≤ A := by
    dsimp [A]
    have := Internal.selectedFrequencyDiameter_nonneg hd nu D
    positivity
  obtain ⟨N, hchoice⟩ := exists_nat_gt (A / target)
  have hNR : (0 : Real) < (N : Real) :=
    (div_nonneg hA htarget.le).trans_lt hchoice
  have hN : 0 < N := by exact_mod_cast hNR
  have hmesh : A / (N : Real) ≤ target := by
    apply le_of_lt
    rw [div_lt_iff₀ hNR]
    have hm := (div_lt_iff₀ htarget).mp hchoice
    nlinarith
  refine ⟨N, hN, ?_⟩
  dsimp only
  have hgeom := stripedCarrier_measurable_volume hd theta N hN htheta0.le htheta1
  refine ⟨hgeom.1, hgeom.2.1, hgeom.2.2, ?_⟩
  intro a
  let aext : IntVec d → Complex := fun n => if hn : n ∈ D then a ⟨n, hn⟩ else 0
  have hsum :
      (∑ n ∈ D, ‖aext n‖ ^ 2) = ∑ n, ‖a n‖ ^ 2 := by
    rw [← Finset.sum_coe_sort D (fun n => ‖aext n‖ ^ 2)]
    simp [aext]
  have hsynth (x : RealVec d) :
      Internal.perturbedSynthesisRaw D aext nu x =
        ∑ n, a n * starRingEnd Complex (fourierChar (nu n.1) x) := by
    unfold Internal.perturbedSynthesisRaw
    rw [← Finset.sum_coe_sort D (fun n =>
      aext n * starRingEnd Complex (fourierChar (nu n) x))]
    simp [aext]
  have hfull :
      K.lower * (∑ n, ‖a n‖ ^ 2) ≤
        (Internal.gramQuadratic
          (Internal.gramMatrix nu D (unitCube d)) a).re := by
    have hK := K.synthesis_lower D aext
    rw [hsum] at hK
    have hgram := (Internal.gramQuadratic_eq_sqNormOn nu D
      (unitCube d) (Or.inl rfl) a).2.2
    rw [hgram]
    simpa only [sqNormOn, hsynth] using hK
  let S : Real := ∑ n, ‖a n‖ ^ 2
  have hS : 0 ≤ S := by
    dsimp [S]
    positivity
  have herror := stripedCarrier_gram_error hd theta N hN htheta0.le htheta1 D nu a
  have herror' :
      ‖Internal.gramQuadratic
          (Internal.gramMatrix nu D (stripedCarrier hd theta N)) a -
        (theta : Complex) * Internal.gramQuadratic
          (Internal.gramMatrix nu D (unitCube d)) a‖ ≤
        target * S := by
    calc
      _ ≤ (D.card : Real) *
          (4 * theta * Real.pi * Internal.selectedFrequencyDiameter hd nu D /
            (N : Real)) * ∑ n, ‖a n‖ ^ 2 := herror
      _ = (A / (N : Real)) * S := by
        dsimp [A, S]
        ring
      _ ≤ target * S := mul_le_mul_of_nonneg_right hmesh hS
  have hre :
      |(Internal.gramQuadratic
          (Internal.gramMatrix nu D (stripedCarrier hd theta N)) a).re -
        theta * (Internal.gramQuadratic
          (Internal.gramMatrix nu D (unitCube d)) a).re| ≤
        target * S := by
    calc
      _ = |(Internal.gramQuadratic
          (Internal.gramMatrix nu D (stripedCarrier hd theta N)) a -
        (theta : Complex) * Internal.gramQuadratic
          (Internal.gramMatrix nu D (unitCube d)) a).re| := by
        congr 2
        simp
      _ ≤ ‖Internal.gramQuadratic
          (Internal.gramMatrix nu D (stripedCarrier hd theta N)) a -
        (theta : Complex) * Internal.gramQuadratic
          (Internal.gramMatrix nu D (unitCube d)) a‖ :=
        Complex.abs_re_le_norm _
      _ ≤ _ := herror'
  have hfull_theta :
      theta * (K.lower * S) ≤ theta *
        (Internal.gramQuadratic
          (Internal.gramMatrix nu D (unitCube d)) a).re :=
    mul_le_mul_of_nonneg_left (by simpa [S] using hfull) htheta0.le
  have hdiff := neg_le_of_abs_le hre
  dsimp [target, S] at hdiff hfull_theta ⊢
  nlinarith

end AsymptoticallyIntegerHD
