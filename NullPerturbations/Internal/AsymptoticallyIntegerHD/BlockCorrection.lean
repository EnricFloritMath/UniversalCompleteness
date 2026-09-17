import AsymptoticallyIntegerHD.Definitions
import AsymptoticallyIntegerHD.PerturbedExponentials
import AsymptoticallyIntegerHD.PeriodicCarrier
import AsymptoticallyIntegerHD.ThinInterpolation
import AsymptoticallyIntegerHD.DyadicBlocks
import AsymptoticallyIntegerHD.BlockMultipliers
import AsymptoticallyIntegerHD.FrequencyCarriers

/-! # Coordinate and level corrections

Plans and their thin carriers are parameters of the correction constructors,
so no residual-dependent choice is hidden in this module.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Pointwise

namespace AsymptoticallyIntegerHD

namespace Internal

/-- Uniform constants used at every recursive level. -/
structure CorrectionConstants {d : Nat} (hd : 0 < d)
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    (data : ModifiedFrequencyData delta) (K : ExponentialBoundsHD data.nu)
    {mu0 : Real} (P : BlockParameters hd delta hdelta data mu0)
    (budgets : BudgetConstants P)
    (EC : ExceptionalConstants hd delta hdelta data P) where
  shiftCard : Nat
  shiftCard_eq : shiftCard = 2 ^ ((exceptionalFinset data).card + 1)
  shiftCard_pos : 0 < shiftCard
  blockShift_support_card_le : ∀ j r,
    (blockShiftFinset data EC j r).coeff.support.card ≤ shiftCard
  baseCost : Real
  baseCost_eq : baseCost =
    8 * (d : Real) * (shiftCard : Real) / (K.lower * EC.lower ^ 2)
  baseCost_pos : 0 < baseCost
  cost : Real
  cost_eq : cost = 20 * EC.upper ^ 2 * baseCost
  cost_pos : 0 < cost
  future : Real
  future_eq : future =
    16 * (d : Real) * Real.pi ^ 2 * K.upper * budgets.Ceta * cost
  future_pos : 0 < future
  leak : Real
  leak_eq : leak = max 1 future
  one_le_leak : 1 ≤ leak
  future_le_leak_sq : future ≤ leak ^ 2

/-- Existence theorem for the canonical coarse correction constants. -/
theorem correctionConstants_nonempty {d : Nat} (hd : 0 < d)
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    (data : ModifiedFrequencyData delta) (K : ExponentialBoundsHD data.nu)
    {mu0 : Real} (P : BlockParameters hd delta hdelta data mu0)
    (budgets : BudgetConstants P)
    (EC : ExceptionalConstants hd delta hdelta data P) :
    Nonempty (CorrectionConstants hd data K P budgets EC) := by
  let shiftCard : Nat := 2 ^ ((exceptionalFinset data).card + 1)
  let baseCost : Real :=
    8 * (d : Real) * (shiftCard : Real) / (K.lower * EC.lower ^ 2)
  let cost : Real := 20 * EC.upper ^ 2 * baseCost
  let future : Real :=
    16 * (d : Real) * Real.pi ^ 2 * K.upper * budgets.Ceta * cost
  let leak : Real := max 1 future
  have hshift : 0 < shiftCard := by simp [shiftCard]
  have hdR : 0 < (d : Real) := by exact_mod_cast hd
  have hbase : 0 < baseCost := by
    dsimp [baseCost]
    exact div_pos
      (mul_pos (mul_pos (by norm_num) hdR) (by exact_mod_cast hshift))
      (mul_pos K.lower_pos (sq_pos_of_pos EC.lower_pos))
  have hcost : 0 < cost := by
    dsimp [cost]
    exact mul_pos (mul_pos (by norm_num) (sq_pos_of_pos EC.upper_pos)) hbase
  have hfuture : 0 < future := by
    dsimp [future]
    exact mul_pos
      (mul_pos
        (mul_pos
          (mul_pos (mul_pos (by norm_num) hdR) (sq_pos_of_pos Real.pi_pos))
          K.upper_pos)
        budgets.Ceta_pos)
      hcost
  have hone : 1 ≤ leak := le_max_left _ _
  have hfuture_le : future ≤ leak := le_max_right _ _
  refine ⟨{
    shiftCard := shiftCard
    shiftCard_eq := rfl
    shiftCard_pos := hshift
    blockShift_support_card_le := ?_
    baseCost := baseCost
    baseCost_eq := rfl
    baseCost_pos := hbase
    cost := cost
    cost_eq := rfl
    cost_pos := hcost
    future := future
    future_eq := rfl
    future_pos := hfuture
    leak := leak
    leak_eq := rfl
    one_le_leak := hone
    future_le_leak_sq := ?_ }⟩
  · intro j r
    simpa only [shiftCard] using (blockShiftFinset data EC j r).coeff_card_le
  · calc
      future ≤ leak := hfuture_le
      _ ≤ leak ^ 2 := by nlinarith

/-- Canonical coarse realization of the correction constants. -/
noncomputable def correctionConstants {d : Nat} (hd : 0 < d)
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    (data : ModifiedFrequencyData delta) (K : ExponentialBoundsHD data.nu)
    {mu0 : Real} (P : BlockParameters hd delta hdelta data mu0)
    (budgets : BudgetConstants P)
    (EC : ExceptionalConstants hd delta hdelta data P) :
    CorrectionConstants hd data K P budgets EC :=
  Classical.choice (correctionConstants_nonempty hd data K P budgets EC)

/-- One late threshold and its square-tail certificate. -/
structure BlockThreshold {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    {data : ModifiedFrequencyData delta} {K : ExponentialBoundsHD data.nu}
    {mu0 : Real} {P : BlockParameters hd delta hdelta data mu0}
    {budgets : BudgetConstants P}
    {EC : ExceptionalConstants hd delta hdelta data P}
    (CC : CorrectionConstants hd data K P budgets EC) where
  J : Nat
  J_ge : max 3 EC.jSep ≤ J
  squareTail_summable : Summable (fun j : Nat =>
    if J ≤ j then (CC.leak * dyadicScale j) ^ 2 else 0)
  squareTail_tsum_le :
    ∑' j : Nat, (if J ≤ j then (CC.leak * dyadicScale j) ^ 2 else 0) ≤ 1 / 4

private theorem scaled_dyadicScale_sq_summable (c : Real) :
    Summable (fun j : Nat ↦ (c * dyadicScale j) ^ 2) := by
  have hgeom : Summable (fun j : Nat ↦ ((1 / 4 : Real) ^ j)) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hscaled := hgeom.mul_left (c ^ 2)
  refine hscaled.congr ?_
  intro j
  rw [dyadicScale, zpow_neg, zpow_natCast, mul_pow]
  congr 1
  rw [show (1 / 4 : Real) = (2 : Real)⁻¹ ^ 2 by norm_num,
    ← pow_mul, ← inv_pow, mul_comm 2 j, pow_mul]

/-- Existence theorem for a sufficiently late geometric threshold. -/
theorem blockThreshold_nonempty {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    {data : ModifiedFrequencyData delta} {K : ExponentialBoundsHD data.nu}
    {mu0 : Real} {P : BlockParameters hd delta hdelta data mu0}
    {budgets : BudgetConstants P}
    {EC : ExceptionalConstants hd delta hdelta data P}
    (CC : CorrectionConstants hd data K P budgets EC) :
    Nonempty (BlockThreshold CC) := by
  let f : Nat → Real := fun j ↦ (CC.leak * dyadicScale j) ^ 2
  have hsum : Summable f := scaled_dyadicScale_sq_summable CC.leak
  let tailEquiv (N : Nat) : Nat ≃ {m : Nat // N ≤ m} :=
    { toFun := fun k ↦ ⟨k + N, by omega⟩
      invFun := fun m ↦ m.1 - N
      left_inv := by intro k; simp
      right_inv := by
        intro m
        apply Subtype.ext
        exact Nat.sub_add_cancel m.property }
  have htail_eq_shifted (N : Nat) :
      (∑' j, if N ≤ j then f j else 0) = ∑' k, f (k + N) := by
    have hfun : (fun j ↦ if N ≤ j then f j else 0) =
        {j : Nat | N ≤ j}.indicator f := by
      funext j
      by_cases hj : N ≤ j <;> simp [Set.indicator, hj]
    rw [hfun, ← tsum_subtype]
    change (∑' m : {m : Nat // N ≤ m}, f m.1) = ∑' k, f (k + N)
    rw [← (tailEquiv N).tsum_eq (fun m ↦ f m.1)]
    rfl
  let hsmall := (Metric.tendsto_atTop.1 (tendsto_sum_nat_add f))
    (1 / 4 : Real) (by norm_num)
  let N : Nat := Classical.choose hsmall
  have hN := Classical.choose_spec hsmall
  have hshift_nonneg : 0 ≤ ∑' k, f (k + N) :=
    tsum_nonneg fun k ↦ sq_nonneg _
  have hshift_lt : (∑' k, f (k + N)) < (1 / 4 : Real) := by
    have hdist := hN N le_rfl
    simpa [Real.dist_eq, abs_of_nonneg hshift_nonneg] using hdist
  let J : Nat := max (max 3 EC.jSep) N
  have hJ : max 3 EC.jSep ≤ J := le_max_left _ _
  have hNJ : N ≤ J := le_max_right _ _
  have htail_summable (L : Nat) :
      Summable (fun j ↦ if L ≤ j then f j else 0) := by
    have hfun : (fun j ↦ if L ≤ j then f j else 0) =
        {j : Nat | L ≤ j}.indicator f := by
      funext j
      by_cases hj : L ≤ j <;> simp [Set.indicator, hj]
    rw [hfun]
    exact hsum.indicator _
  have htail_le :
      (∑' j, if J ≤ j then f j else 0) ≤
        ∑' j, if N ≤ j then f j else 0 := by
    apply Summable.tsum_le_tsum
    · intro j
      by_cases hJj : J ≤ j
      · have hNj : N ≤ j := hNJ.trans hJj
        simp [hJj, hNj]
      · by_cases hNj : N ≤ j
        · simp [hJj, hNj]
          exact sq_nonneg _
        · simp [hJj, hNj]
    · exact htail_summable J
    · exact htail_summable N
  have htail_quarter :
      (∑' j, if J ≤ j then f j else 0) ≤ (1 / 4 : Real) := by
    calc
      (∑' j, if J ≤ j then f j else 0) ≤
          ∑' j, if N ≤ j then f j else 0 := htail_le
      _ = ∑' k, f (k + N) := htail_eq_shifted N
      _ ≤ (1 / 4 : Real) := hshift_lt.le
  refine ⟨{
    J := J
    J_ge := hJ
    squareTail_summable := ?_
    squareTail_tsum_le := ?_ }⟩
  · simpa only [f] using htail_summable J
  · simpa only [f] using htail_quarter

/-- Choose a sufficiently late geometric threshold. -/
noncomputable def blockThreshold {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    {data : ModifiedFrequencyData delta} {K : ExponentialBoundsHD data.nu}
    {mu0 : Real} {P : BlockParameters hd delta hdelta data mu0}
    {budgets : BudgetConstants P}
    {EC : ExceptionalConstants hd delta hdelta data P}
    (CC : CorrectionConstants hd data K P budgets EC) : BlockThreshold CC :=
  Classical.choice (blockThreshold_nonempty CC)

/-- A residual-independent carrier plan for one coordinate piece. -/
structure BlockPlan {d : Nat} (hd : 0 < d)
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    (data : ModifiedFrequencyData delta) (K : ExponentialBoundsHD data.nu)
    {mu0 : Real} (P : BlockParameters hd delta hdelta data mu0)
    (budgets : BudgetConstants P)
    (EC : ExceptionalConstants hd delta hdelta data P)
    (CC : CorrectionConstants hd data K P budgets EC)
    (threshold : BlockThreshold CC) (j : Nat) (r : Fin d)
    (hactive : (coordinateBlock delta hdelta data.C0 hd j r).Nonempty)
    (hlate : threshold.J ≤ j) where
  guard : Finset (IntVec d)
  guard_eq : guard = guardFinset delta hdelta data.C0 j
  guard_nonempty : guard.Nonempty
  guard_outside : ∀ n ∈ guard, n ∉ data.C0
  shiftData : BlockShiftFinsetData data EC j r
  shiftData_eq : shiftData = blockShiftFinset data EC j r
  blockCoeffs : Finsupp (IntVec d) Complex
  blockCoeffs_eq : blockCoeffs = shiftData.coeff
  theta : Real
  theta_eq : theta = P.eta j / (4 * (d : Real) * (CC.shiftCard : Real))
  theta_pos : 0 < theta
  theta_le_one : theta ≤ 1
  thinCarrier : ThinCarrierHD data K guard theta

/-- Existence theorem for a fixed plan chosen before any residual is known. -/
theorem blockPlan_nonempty {d : Nat} (hd : 0 < d)
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    (data : ModifiedFrequencyData delta) (K : ExponentialBoundsHD data.nu)
    {mu0 : Real} (P : BlockParameters hd delta hdelta data mu0)
    (budgets : BudgetConstants P)
    (EC : ExceptionalConstants hd delta hdelta data P)
    (CC : CorrectionConstants hd data K P budgets EC)
    (threshold : BlockThreshold CC) (j : Nat) (r : Fin d)
    (hactive : (coordinateBlock delta hdelta data.C0 hd j r).Nonempty)
    (hlate : threshold.J ≤ j) :
    Nonempty (BlockPlan hd data K P budgets EC CC threshold j r hactive hlate) := by
  classical
  let guard := guardFinset delta hdelta data.C0 j
  have hthree : 3 ≤ j :=
    (le_max_left 3 EC.jSep).trans (threshold.J_ge.trans hlate)
  have hblock_guard : ∀ n,
      n ∈ coordinateBlock delta hdelta data.C0 hd j r → n ∈ guard := by
    intro n hn
    change n ∈ guardFinset delta hdelta data.C0 j
    rw [guardFinset]
    apply Finset.mem_biUnion.mpr
    refine ⟨j, Finset.mem_Icc.mpr ⟨hthree, ?_⟩,
      (mem_coordinateBlock_iff.mp hn).choose⟩
    omega
  have hguard_nonempty : guard.Nonempty := by
    obtain ⟨n, hn⟩ := hactive
    exact ⟨n, hblock_guard n hn⟩
  have hguard_outside : ∀ n ∈ guard, n ∉ data.C0 := by
    intro n hn
    change n ∈ guardFinset delta hdelta data.C0 j at hn
    rw [guardFinset] at hn
    obtain ⟨k, -, hnk⟩ := Finset.mem_biUnion.mp hn
    exact (mem_dyadicBlock_iff.mp hnk).1
  let shiftData : BlockShiftFinsetData data EC j r := blockShiftFinset data EC j r
  let blockCoeffs : Finsupp (IntVec d) Complex := shiftData.coeff
  let theta : Real :=
    P.eta j / (4 * (d : Real) * (CC.shiftCard : Real))
  have hden_pos : 0 < 4 * (d : Real) * (CC.shiftCard : Real) := by
    have hdR : 0 < (d : Real) := by exact_mod_cast hd
    have hshiftR : 0 < (CC.shiftCard : Real) := by exact_mod_cast CC.shiftCard_pos
    positivity
  have heta_pos : 0 < P.eta j := budgets.eta_pos j hthree
  have htheta_pos : 0 < theta := by
    dsimp [theta]
    exact div_pos heta_pos hden_pos
  have heta_le_tsum : P.eta j ≤ ∑' k, P.eta k :=
    budgets.eta_summable.le_tsum j (fun k _ ↦ budgets.eta_nonneg k)
  have heta_lt_one : P.eta j < 1 := by
    calc
      P.eta j ≤ ∑' k, P.eta k := heta_le_tsum
      _ < mu0 / 4 := budgets.eta_tsum_le
      _ < 1 := by nlinarith [P.mu0_lt_one]
  have hden_ge_one : 1 ≤ 4 * (d : Real) * (CC.shiftCard : Real) := by
    have hdR : 1 ≤ (d : Real) := by exact_mod_cast hd
    have hshiftR : 1 ≤ (CC.shiftCard : Real) := by
      exact_mod_cast CC.shiftCard_pos
    nlinarith
  have htheta_le_one : theta ≤ 1 := by
    dsimp [theta]
    apply (div_le_one hden_pos).mpr
    exact heta_lt_one.le.trans hden_ge_one
  let thinCarrier := exists_thinCarrier_hd hd data K guard hguard_nonempty
    hguard_outside theta htheta_pos htheta_le_one
  refine ⟨{
    guard := guard
    guard_eq := rfl
    guard_nonempty := hguard_nonempty
    guard_outside := hguard_outside
    shiftData := shiftData
    shiftData_eq := rfl
    blockCoeffs := blockCoeffs
    blockCoeffs_eq := rfl
    theta := theta
    theta_eq := rfl
    theta_pos := htheta_pos
    theta_le_one := htheta_le_one
    thinCarrier := thinCarrier }⟩

/-- Construct the fixed plan before any residual is known. -/
noncomputable def blockPlan {d : Nat} (hd : 0 < d)
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    (data : ModifiedFrequencyData delta) (K : ExponentialBoundsHD data.nu)
    {mu0 : Real} (P : BlockParameters hd delta hdelta data mu0)
    (budgets : BudgetConstants P)
    (EC : ExceptionalConstants hd delta hdelta data P)
    (CC : CorrectionConstants hd data K P budgets EC)
    (threshold : BlockThreshold CC) (j : Nat) (r : Fin d)
    (hactive : (coordinateBlock delta hdelta data.C0 hd j r).Nonempty)
    (hlate : threshold.J ≤ j) :
    BlockPlan hd data K P budgets EC CC threshold j r hactive hlate :=
  Classical.choice
    (blockPlan_nonempty hd data K P budgets EC CC threshold j r hactive hlate)

/-- Guard values which cancel the current coordinate residual. -/
def coordinateInterpolationValues {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    {data : ModifiedFrequencyData delta} {K : ExponentialBoundsHD data.nu}
    {mu0 : Real} {P : BlockParameters hd delta hdelta data mu0}
    {budgets : BudgetConstants P}
    {EC : ExceptionalConstants hd delta hdelta data P}
    {CC : CorrectionConstants hd data K P budgets EC}
    {threshold : BlockThreshold CC} {j : Nat} {r : Fin d}
    {hactive : (coordinateBlock delta hdelta data.C0 hd j r).Nonempty}
    {hlate : threshold.J ≤ j}
    (plan : BlockPlan hd data K P budgets EC CC threshold j r hactive hlate)
    (u : {n : IntVec d // n ∈ coordinateBlock delta hdelta data.C0 hd j r} →
      Complex) (n : {n : IntVec d // n ∈ plan.guard}) : Complex :=
  if hn : n.1 ∈ coordinateBlock delta hdelta data.C0 hd j r then
    -u ⟨n.1, hn⟩ / blockMultiplier data j r (frequency delta n.1)
  else 0

/-- Absolute first-coordinate slab containing one coordinate carrier. -/
def coordinateBaseEnvelope {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    {data : ModifiedFrequencyData delta} {K : ExponentialBoundsHD data.nu}
    {mu0 : Real} {P : BlockParameters hd delta hdelta data mu0}
    {budgets : BudgetConstants P}
    {EC : ExceptionalConstants hd delta hdelta data P}
    {CC : CorrectionConstants hd data K P budgets EC}
    {threshold : BlockThreshold CC} {j : Nat} {r : Fin d}
    {hactive : (coordinateBlock delta hdelta data.C0 hd j r).Nonempty}
    {hlate : threshold.J ≤ j}
    (plan : BlockPlan hd data K P budgets EC CC threshold j r hactive hlate)
    (M : IntVec d) : Set (RealVec d) :=
  {x | (M (firstCoordinate hd) : Real) ≤ x (firstCoordinate hd) ∧
    x (firstCoordinate hd) ≤ (M (firstCoordinate hd) : Real) +
      plan.shiftData.baseEnvelopeWidth}

/-- Difference-support enlargement of `coordinateBaseEnvelope`. -/
def coordinateDifferenceEnvelope {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    {data : ModifiedFrequencyData delta} {K : ExponentialBoundsHD data.nu}
    {mu0 : Real} {P : BlockParameters hd delta hdelta data mu0}
    {budgets : BudgetConstants P}
    {EC : ExceptionalConstants hd delta hdelta data P}
    {CC : CorrectionConstants hd data K P budgets EC}
    {threshold : BlockThreshold CC} {j : Nat} {r : Fin d}
    {hactive : (coordinateBlock delta hdelta data.C0 hd j r).Nonempty}
    {hlate : threshold.J ≤ j}
    (plan : BlockPlan hd data K P budgets EC CC threshold j r hactive hlate)
    (M : IntVec d) : Set (RealVec d) :=
  {x | (M (firstCoordinate hd) : Real) ≤ x (firstCoordinate hd) ∧
    x (firstCoordinate hd) ≤ (M (firstCoordinate hd) : Real) +
      plan.shiftData.differenceEnvelopeWidth}

/-- Combined properties for one coordinate correction. -/
structure CoordinateCorrection {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    {data : ModifiedFrequencyData delta} {K : ExponentialBoundsHD data.nu}
    {mu0 : Real} {P : BlockParameters hd delta hdelta data mu0}
    {budgets : BudgetConstants P}
    {EC : ExceptionalConstants hd delta hdelta data P}
    {CC : CorrectionConstants hd data K P budgets EC}
    {threshold : BlockThreshold CC} {j : Nat} {r : Fin d}
    {hactive : (coordinateBlock delta hdelta data.C0 hd j r).Nonempty}
    {hlate : threshold.J ≤ j}
    (plan : BlockPlan hd data K P budgets EC CC threshold j r hactive hlate)
    (M : IntVec d)
    (u : {n : IntVec d // n ∈ coordinateBlock delta hdelta data.C0 hd j r} →
      Complex) where
  h : RealVec d → Complex
  h_eq : h = plan.thinCarrier.interpolate M (coordinateInterpolationValues plan u)
  carrierFn : RealVec d → Complex
  carrierFn_eq : carrierFn = shiftPolynomialCarrier plan.blockCoeffs h
  carrierSet : Set (RealVec d)
  carrierSet_eq : carrierSet =
    shiftPolynomialCarrierSet plan.blockCoeffs M plan.thinCarrier.omega
  carrierSet_measurable : MeasurableSet carrierSet
  carrierFn_stronglyMeasurable : AEStronglyMeasurable carrierFn volume
  carrierFn_integrable : Integrable carrierFn volume
  carrierFn_memLp : MemLp carrierFn (2 : ENNReal) volume
  carrierFn_supported : AESupportedIn carrierFn carrierSet
  carrierSet_contained : carrierSet ⊆ coordinateBaseEnvelope plan M
  current_trace : ∀ n,
    inverseSample carrierFn (frequency delta n.1) = -u n
  guard_trace : ∀ n, n ∈ plan.guard →
    n ∉ coordinateBlock delta hdelta data.C0 hd j r →
      inverseSample carrierFn (frequency delta n) = 0
  exceptional_trace : ∀ n ∈ data.C0,
    inverseSample carrierFn (frequency delta n) = 0
  carrier_volume : volume carrierSet ≤ ENNReal.ofReal (P.eta j / (2 * d))
  carrier_energy : sqNormOn Set.univ carrierFn ≤
    CC.cost / P.eta j * ∑ n, ‖u n‖ ^ 2

/-- Existence theorem for one coordinate correction. -/
theorem coordinateCorrection_nonempty {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    {data : ModifiedFrequencyData delta} {K : ExponentialBoundsHD data.nu}
    {mu0 : Real} {P : BlockParameters hd delta hdelta data mu0}
    {budgets : BudgetConstants P}
    {EC : ExceptionalConstants hd delta hdelta data P}
    {CC : CorrectionConstants hd data K P budgets EC}
    {threshold : BlockThreshold CC} {j : Nat} {r : Fin d}
    {hactive : (coordinateBlock delta hdelta data.C0 hd j r).Nonempty}
    {hlate : threshold.J ≤ j}
    (plan : BlockPlan hd data K P budgets EC CC threshold j r hactive hlate)
    (M : IntVec d)
    (u : {n : IntVec d // n ∈ coordinateBlock delta hdelta data.C0 hd j r} →
      Complex) : Nonempty (CoordinateCorrection plan M u) := by
  classical
  let current := coordinateBlock delta hdelta data.C0 hd j r
  have hsep : EC.jSep ≤ j :=
    (le_max_right 3 EC.jSep).trans (threshold.J_ge.trans hlate)
  have hcurrent_guard : ∀ n ∈ current, n ∈ plan.guard := by
    intro n hn
    rw [plan.guard_eq, guardFinset]
    apply Finset.mem_biUnion.mpr
    have hthree : 3 ≤ j :=
      (le_max_left 3 EC.jSep).trans (threshold.J_ge.trans hlate)
    exact ⟨j, Finset.mem_Icc.mpr ⟨hthree, by omega⟩,
      (mem_coordinateBlock_iff.mp hn).choose⟩
  let v : {n : IntVec d // n ∈ plan.guard} → Complex :=
    coordinateInterpolationValues plan u
  let h : RealVec d → Complex := plan.thinCarrier.interpolate M v
  let G : RealVec d → Complex := shiftPolynomialCarrier plan.blockCoeffs h
  let A : Set (RealVec d) :=
    shiftPolynomialCarrierSet plan.blockCoeffs M plan.thinCarrier.omega
  have hhstrong : StronglyMeasurable h :=
    plan.thinCarrier.interpolate_stronglyMeasurable M v
  have hhmeas : AEStronglyMeasurable h volume := hhstrong.aestronglyMeasurable
  have hhint : Integrable h volume :=
    plan.thinCarrier.interpolate_integrable M v
  have hhLp : MemLp h (2 : ENNReal) volume :=
    plan.thinCarrier.interpolate_memLp M v
  have hhsupp : AESupportedIn h (integerEmbed M +ᵥ plan.thinCarrier.omega) :=
    plan.thinCarrier.interpolate_supported M v
  have hgeo := shiftPolynomialCarrier_support_measure plan.blockCoeffs M
    plan.thinCarrier.omega_measurable plan.thinCarrier.omega_subset hhsupp
  have hanalytic := shiftPolynomialCarrier_analytic_cost plan.blockCoeffs M
    hhmeas hhint hhLp hhsupp
  have hmultiplier (xi : RealVec d) :
      inverseSample G xi = blockMultiplier data j r xi * inverseSample h xi := by
    rw [show G = shiftPolynomialCarrier plan.blockCoeffs h from rfl,
      inverseSample_shiftPolynomialCarrier hhint]
    rw [plan.blockCoeffs_eq, plan.shiftData.evaluation]
  have hcurrent_trace : ∀ n : {n : IntVec d // n ∈ current},
      inverseSample G (frequency delta n.1) = -u n := by
    intro n
    have hlower := (blockMultiplier_bounds hd EC).1 j r n.1 hsep n.property
    have hne : blockMultiplier data j r (frequency delta n.1) ≠ 0 := by
      exact norm_pos_iff.mp (EC.lower_pos.trans_le hlower)
    rw [hmultiplier]
    have hsamp := plan.thinCarrier.interpolate_samples M v
      ⟨n.1, hcurrent_guard n.1 n.property⟩
    change inverseSample h (frequency delta n.1) =
      v ⟨n.1, hcurrent_guard n.1 n.property⟩ at hsamp
    rw [hsamp]
    change blockMultiplier data j r (frequency delta n.1) *
      coordinateInterpolationValues plan u
        ⟨n.1, hcurrent_guard n.1 n.property⟩ = -u n
    rw [coordinateInterpolationValues, dif_pos n.property]
    simp only [div_eq_mul_inv]
    calc
      blockMultiplier data j r (frequency delta n.1) *
          (-u ⟨n.1, n.property⟩ *
            (blockMultiplier data j r (frequency delta n.1))⁻¹) =
          -u ⟨n.1, n.property⟩ *
            (blockMultiplier data j r (frequency delta n.1) *
              (blockMultiplier data j r (frequency delta n.1))⁻¹) := by ring
      _ = -u n := by rw [mul_inv_cancel₀ hne, mul_one]
  have hguard_trace : ∀ n, n ∈ plan.guard → n ∉ current →
      inverseSample G (frequency delta n) = 0 := by
    intro n hn hncurrent
    rw [hmultiplier]
    have hsamp := plan.thinCarrier.interpolate_samples M v ⟨n, hn⟩
    change inverseSample h (frequency delta n) = v ⟨n, hn⟩ at hsamp
    rw [hsamp]
    change blockMultiplier data j r (frequency delta n) *
      coordinateInterpolationValues plan u ⟨n, hn⟩ = 0
    rw [coordinateInterpolationValues, dif_neg hncurrent, mul_zero]
  have hintegral_dyadic_zero (xi : RealVec d) (hxi : IsIntegralVector xi) :
      dyadicMultiplier j r xi = 0 := by
    obtain ⟨m, rfl⟩ := hxi
    rw [dyadicMultiplier, fourierChar]
    have hsumInt : ∃ z : Int,
        (∑ i : Fin d, integerEmbed m i *
          (((dyadicStep j : Real) • basisVector r) i)) = (z : Real) := by
      refine ⟨m r * dyadicStep j, ?_⟩
      simp only [integerEmbed_apply, Pi.smul_apply, smul_eq_mul,
        basisVector_apply]
      rw [Finset.sum_eq_single r]
      · simp
      · intro b _ hbr
        simp [hbr]
      · simp
    obtain ⟨z, hz⟩ := hsumInt
    rw [hz]
    have hzexp : Complex.exp
        (((2 * Real.pi : Real) : Complex) * Complex.I *
          (((z : Int) : Real) : Complex)) = 1 := by
      convert Complex.exp_int_mul_two_pi_mul_I z using 1
      push_cast
      ring_nf
    rw [hzexp, sub_self]
  have hexceptional_trace : ∀ n ∈ data.C0,
      inverseSample G (frequency delta n) = 0 := by
    intro n hn
    rw [hmultiplier]
    have hzero : blockMultiplier data j r (frequency delta n) = 0 := by
      by_cases hni : IsIntegralVector (frequency delta n)
      · rw [blockMultiplier, hintegral_dyadic_zero _ hni, mul_zero]
      · have hnexc : n ∈ exceptionalFinset data := by
          simp [exceptionalFinset, hn, hni]
        rw [blockMultiplier, (exceptionalMultiplier_roots data).1 n hnexc,
          zero_mul]
    rw [hzero, zero_mul]
  have hAcontained : A ⊆ coordinateBaseEnvelope plan M := by
    intro x hx
    simp only [A, shiftPolynomialCarrierSet, Set.mem_iUnion] at hx
    obtain ⟨a, ha, hx⟩ := hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_vadd_set.mp hx
    have hyi := plan.thinCarrier.omega_subset hy (firstCoordinate hd)
    rcases hyi with ⟨hyi0, hyi1⟩
    have ha' : a ∈ plan.shiftData.coeff.support := by
      rwa [← plan.blockCoeffs_eq]
    have ha0 := (plan.shiftData.coordinate_bounds a ha' (firstCoordinate hd)).1
    have hau := plan.shiftData.firstCoordinateUpper_spec a ha'
    have hxyi := congrFun hxy (firstCoordinate hd)
    simp only [vadd_eq_add, Pi.add_apply, integerEmbed_apply] at hxyi
    push_cast at hxyi
    change (M (firstCoordinate hd) : Real) ≤ x (firstCoordinate hd) ∧
      x (firstCoordinate hd) ≤ (M (firstCoordinate hd) : Real) +
        plan.shiftData.baseEnvelopeWidth
    rw [plan.shiftData.baseEnvelopeWidth_eq]
    have ha0R : 0 ≤ (a (firstCoordinate hd) : Real) := by exact_mod_cast ha0
    have hauR : (a (firstCoordinate hd) : Real) ≤
        plan.shiftData.firstCoordinateUpper := by exact_mod_cast hau
    constructor
    · rw [← hxyi]
      linarith
    · rw [← hxyi]
      push_cast
      linarith
  have hAvolume : volume A ≤ ENNReal.ofReal (P.eta j / (2 * d)) := by
    have hcardR : (plan.blockCoeffs.support.card : Real) ≤ CC.shiftCard := by
      have hc : plan.blockCoeffs.support.card ≤ CC.shiftCard := by
        rw [plan.blockCoeffs_eq, plan.shiftData_eq]
        exact CC.blockShift_support_card_le j r
      exact_mod_cast hc
    have hdR : 0 < (d : Real) := by exact_mod_cast hd
    have heta0 : 0 ≤ P.eta j := budgets.eta_nonneg j
    have hprod : (plan.blockCoeffs.support.card : Real) * plan.theta ≤
        P.eta j / (2 * (d : Real)) := by
      rw [plan.theta_eq]
      have hsR : 0 < (CC.shiftCard : Real) := by
        exact_mod_cast CC.shiftCard_pos
      calc
        (plan.blockCoeffs.support.card : Real) *
            (P.eta j / (4 * (d : Real) * (CC.shiftCard : Real))) ≤
            (CC.shiftCard : Real) *
              (P.eta j / (4 * (d : Real) * (CC.shiftCard : Real))) :=
          mul_le_mul_of_nonneg_right hcardR (div_nonneg heta0 (by positivity))
        _ ≤ P.eta j / (2 * (d : Real)) := by
          field_simp [hdR.ne', hsR.ne']
          nlinarith
    calc
      volume A ≤ (plan.blockCoeffs.support.card : ENNReal) *
          volume plan.thinCarrier.omega := hgeo.2.2.1
      _ = ENNReal.ofReal
          ((plan.blockCoeffs.support.card : Real) * plan.theta) := by
        rw [plan.thinCarrier.volume_omega, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      _ ≤ ENNReal.ofReal (P.eta j / (2 * (d : Real))) :=
        ENNReal.ofReal_le_ofReal hprod
  have henergy : sqNormOn Set.univ G ≤
      CC.cost / P.eta j * ∑ n, ‖u n‖ ^ 2 := by
    let extEnergy : IntVec d → Real := fun n =>
      if hn : n ∈ current then (1 / EC.lower ^ 2) * ‖u ⟨n, hn⟩‖ ^ 2 else 0
    have hv_sq_le (n : {n : IntVec d // n ∈ plan.guard}) :
        ‖v n‖ ^ 2 ≤ extEnergy n.1 := by
      by_cases hn : n.1 ∈ current
      · have hlower := (blockMultiplier_bounds hd EC).1 j r n.1 hsep hn
        dsimp only [v, extEnergy]
        rw [coordinateInterpolationValues, dif_pos hn, dif_pos hn,
          norm_div, norm_neg]
        have hnormpos : 0 < ‖blockMultiplier data j r (frequency delta n.1)‖ :=
          EC.lower_pos.trans_le hlower
        have hsquare : EC.lower ^ 2 ≤
            ‖blockMultiplier data j r (frequency delta n.1)‖ ^ 2 :=
          pow_le_pow_left₀ EC.lower_pos.le hlower 2
        rw [div_pow]
        calc
          ‖u ⟨n.1, _⟩‖ ^ 2 /
              ‖blockMultiplier data j r (frequency delta n.1)‖ ^ 2 ≤
              ‖u ⟨n.1, _⟩‖ ^ 2 / EC.lower ^ 2 :=
            div_le_div_of_nonneg_left (sq_nonneg _)
              (sq_pos_of_pos EC.lower_pos) hsquare
          _ = (1 / EC.lower ^ 2) * ‖u ⟨n.1, _⟩‖ ^ 2 := by ring
      · dsimp only [v, extEnergy]
        rw [coordinateInterpolationValues, dif_neg hn, dif_neg hn, norm_zero,
          zero_pow (by norm_num)]
    have hcurrent_subset : current ⊆ plan.guard := fun n hn =>
      hcurrent_guard n hn
    have hext_sum :
        (∑ n : {n : IntVec d // n ∈ plan.guard}, extEnergy n.1) =
          (1 / EC.lower ^ 2) *
            ∑ n : {n : IntVec d // n ∈ current}, ‖u n‖ ^ 2 := by
      calc
        (∑ n : {n : IntVec d // n ∈ plan.guard}, extEnergy n.1) =
            ∑ n ∈ plan.guard, extEnergy n := by
          rw [← plan.guard.sum_attach]
          simp
        _ = ∑ n ∈ current, extEnergy n := by
          symm
          apply Finset.sum_subset hcurrent_subset
          intro n _ hncurrent
          simp [extEnergy, hncurrent]
        _ = ∑ n : {n : IntVec d // n ∈ current}, extEnergy n.1 := by
          rw [← current.sum_attach]
          simp
        _ = (1 / EC.lower ^ 2) *
            ∑ n : {n : IntVec d // n ∈ current}, ‖u n‖ ^ 2 := by
          simp only [extEnergy, Subtype.property, ↓reduceDIte, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro n hn
          congr 3
    have hvsum : (∑ n : {n : IntVec d // n ∈ plan.guard}, ‖v n‖ ^ 2) ≤
        (1 / EC.lower ^ 2) *
          ∑ n : {n : IntVec d // n ∈ current}, ‖u n‖ ^ 2 := by
      calc
        _ ≤ ∑ n : {n : IntVec d // n ∈ plan.guard}, extEnergy n.1 :=
          Finset.sum_le_sum fun n _ => hv_sq_le n
        _ = _ := hext_sum
    have heta_pos : 0 < P.eta j :=
      budgets.eta_pos j
        ((le_max_left 3 EC.jSep).trans (threshold.J_ge.trans hlate))
    have hhcost0 := plan.thinCarrier.interpolate_cost M v
    change sqNormOn Set.univ h ≤ (2 / (K.lower * plan.theta)) *
      ∑ n : {n : IntVec d // n ∈ plan.guard}, ‖v n‖ ^ 2 at hhcost0
    have hhcost : sqNormOn Set.univ h ≤ CC.baseCost / P.eta j *
        ∑ n : {n : IntVec d // n ∈ current}, ‖u n‖ ^ 2 := by
      calc
        sqNormOn Set.univ h ≤ (2 / (K.lower * plan.theta)) *
            ∑ n : {n : IntVec d // n ∈ plan.guard}, ‖v n‖ ^ 2 := hhcost0
        _ ≤ (2 / (K.lower * plan.theta)) *
            ((1 / EC.lower ^ 2) *
              ∑ n : {n : IntVec d // n ∈ current}, ‖u n‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hvsum
            (div_nonneg (by norm_num)
              (mul_nonneg K.lower_pos.le plan.theta_pos.le))
        _ = CC.baseCost / P.eta j *
            ∑ n : {n : IntVec d // n ∈ current}, ‖u n‖ ^ 2 := by
          rw [plan.theta_eq, CC.baseCost_eq]
          have hdR : 0 < (d : Real) := by exact_mod_cast hd
          have hsR : 0 < (CC.shiftCard : Real) := by
            exact_mod_cast CC.shiftCard_pos
          field_simp [K.lower_pos.ne', EC.lower_pos.ne', heta_pos.ne',
            hdR.ne', hsR.ne']
          ring
    have hh_nonneg : 0 ≤ sqNormOn Set.univ h := by
      rw [sqNormOn, setIntegral_univ]
      exact integral_nonneg fun x => sq_nonneg ‖h x‖
    have hcoeff : (plan.blockCoeffs.support.sum fun a =>
        ‖plan.blockCoeffs a‖ ^ 2) ≤ 4 * EC.upper ^ 2 := by
      rw [plan.blockCoeffs_eq]
      exact plan.shiftData.coeff_sq_le
    have hGexact := hanalytic.2.2.2 hgeo.2.2.2
    have hGcost : sqNormOn Set.univ G ≤
        4 * EC.upper ^ 2 * (CC.baseCost / P.eta j *
          ∑ n : {n : IntVec d // n ∈ current}, ‖u n‖ ^ 2) := by
      rw [show G = shiftPolynomialCarrier plan.blockCoeffs h from rfl, hGexact]
      calc
        _ ≤ (4 * EC.upper ^ 2) * sqNormOn Set.univ h :=
          mul_le_mul_of_nonneg_right hcoeff hh_nonneg
        _ ≤ _ := mul_le_mul_of_nonneg_left hhcost (by positivity)
    calc
      sqNormOn Set.univ G ≤ _ := hGcost
      _ ≤ (20 * EC.upper ^ 2) * (CC.baseCost / P.eta j *
          ∑ n : {n : IntVec d // n ∈ current}, ‖u n‖ ^ 2) := by
        have hbase0 : 0 ≤ CC.baseCost / P.eta j *
            ∑ n : {n : IntVec d // n ∈ current}, ‖u n‖ ^ 2 :=
          mul_nonneg (div_nonneg CC.baseCost_pos.le heta_pos.le)
            (Finset.sum_nonneg fun _ _ => sq_nonneg _)
        apply mul_le_mul_of_nonneg_right _ hbase0
        nlinarith [sq_nonneg EC.upper]
      _ = CC.cost / P.eta j *
          ∑ n : {n : IntVec d // n ∈ current}, ‖u n‖ ^ 2 := by
        rw [CC.cost_eq]
        ring
  refine ⟨{
    h := h
    h_eq := rfl
    carrierFn := G
    carrierFn_eq := rfl
    carrierSet := A
    carrierSet_eq := rfl
    carrierSet_measurable := hgeo.1
    carrierFn_stronglyMeasurable := hanalytic.1.aestronglyMeasurable
    carrierFn_integrable := hanalytic.1
    carrierFn_memLp := hanalytic.2.1
    carrierFn_supported := hgeo.2.1
    carrierSet_contained := hAcontained
    current_trace := hcurrent_trace
    guard_trace := hguard_trace
    exceptional_trace := hexceptional_trace
    carrier_volume := hAvolume
    carrier_energy := henergy }⟩

private theorem coordinateCorrection_carrier_energy_sharp {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    {data : ModifiedFrequencyData delta} {K : ExponentialBoundsHD data.nu}
    {mu0 : Real} {P : BlockParameters hd delta hdelta data mu0}
    {budgets : BudgetConstants P}
    {EC : ExceptionalConstants hd delta hdelta data P}
    {CC : CorrectionConstants hd data K P budgets EC}
    {threshold : BlockThreshold CC} {j : Nat} {r : Fin d}
    {hactive : (coordinateBlock delta hdelta data.C0 hd j r).Nonempty}
    {hlate : threshold.J ≤ j}
    {plan : BlockPlan hd data K P budgets EC CC threshold j r hactive hlate}
    {M : IntVec d}
    {u : {n : IntVec d // n ∈ coordinateBlock delta hdelta data.C0 hd j r} →
      Complex} (C : CoordinateCorrection plan M u) :
    sqNormOn Set.univ C.carrierFn ≤
      4 * EC.upper ^ 2 * (CC.baseCost / P.eta j * ∑ n, ‖u n‖ ^ 2) := by
  classical
  let current := coordinateBlock delta hdelta data.C0 hd j r
  let v : {n : IntVec d // n ∈ plan.guard} → Complex :=
    coordinateInterpolationValues plan u
  have hsep : EC.jSep ≤ j :=
    (le_max_right 3 EC.jSep).trans (threshold.J_ge.trans hlate)
  have hcurrent_guard : ∀ n ∈ current, n ∈ plan.guard := by
    intro n hn
    rw [plan.guard_eq, guardFinset]
    apply Finset.mem_biUnion.mpr
    have hthree : 3 ≤ j :=
      (le_max_left 3 EC.jSep).trans (threshold.J_ge.trans hlate)
    exact ⟨j, Finset.mem_Icc.mpr ⟨hthree, by omega⟩,
      (mem_coordinateBlock_iff.mp hn).choose⟩
  let extEnergy : IntVec d → Real := fun n =>
    if hn : n ∈ current then (1 / EC.lower ^ 2) * ‖u ⟨n, hn⟩‖ ^ 2 else 0
  have hv_sq_le (n : {n : IntVec d // n ∈ plan.guard}) :
      ‖v n‖ ^ 2 ≤ extEnergy n.1 := by
    by_cases hn : n.1 ∈ current
    · have hlower := (blockMultiplier_bounds hd EC).1 j r n.1 hsep hn
      dsimp only [v, extEnergy]
      rw [coordinateInterpolationValues, dif_pos hn, dif_pos hn,
        norm_div, norm_neg, div_pow]
      have hsquare : EC.lower ^ 2 ≤
          ‖blockMultiplier data j r (frequency delta n.1)‖ ^ 2 :=
        pow_le_pow_left₀ EC.lower_pos.le hlower 2
      calc
        ‖u ⟨n.1, _⟩‖ ^ 2 /
            ‖blockMultiplier data j r (frequency delta n.1)‖ ^ 2 ≤
            ‖u ⟨n.1, _⟩‖ ^ 2 / EC.lower ^ 2 :=
          div_le_div_of_nonneg_left (sq_nonneg _)
            (sq_pos_of_pos EC.lower_pos) hsquare
        _ = (1 / EC.lower ^ 2) * ‖u ⟨n.1, _⟩‖ ^ 2 := by ring
    · dsimp only [v, extEnergy]
      rw [coordinateInterpolationValues, dif_neg hn, dif_neg hn, norm_zero,
        zero_pow (by norm_num)]
  have hcurrent_subset : current ⊆ plan.guard := fun n hn => hcurrent_guard n hn
  have hext_sum :
      (∑ n : {n : IntVec d // n ∈ plan.guard}, extEnergy n.1) =
        (1 / EC.lower ^ 2) *
          ∑ n : {n : IntVec d // n ∈ current}, ‖u n‖ ^ 2 := by
    calc
      (∑ n : {n : IntVec d // n ∈ plan.guard}, extEnergy n.1) =
          ∑ n ∈ plan.guard, extEnergy n := by
        rw [← plan.guard.sum_attach]
        simp
      _ = ∑ n ∈ current, extEnergy n := by
        symm
        apply Finset.sum_subset hcurrent_subset
        intro n _ hncurrent
        simp [extEnergy, hncurrent]
      _ = ∑ n : {n : IntVec d // n ∈ current}, extEnergy n.1 := by
        rw [← current.sum_attach]
        simp
      _ = (1 / EC.lower ^ 2) *
          ∑ n : {n : IntVec d // n ∈ current}, ‖u n‖ ^ 2 := by
        simp only [extEnergy, Subtype.property, ↓reduceDIte, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        congr 3
  have hvsum : (∑ n : {n : IntVec d // n ∈ plan.guard}, ‖v n‖ ^ 2) ≤
      (1 / EC.lower ^ 2) *
        ∑ n : {n : IntVec d // n ∈ current}, ‖u n‖ ^ 2 := by
    calc
      _ ≤ ∑ n : {n : IntVec d // n ∈ plan.guard}, extEnergy n.1 :=
        Finset.sum_le_sum fun n _ => hv_sq_le n
      _ = _ := hext_sum
  have heta_pos : 0 < P.eta j :=
    budgets.eta_pos j
      ((le_max_left 3 EC.jSep).trans (threshold.J_ge.trans hlate))
  have hhcost0 := plan.thinCarrier.interpolate_cost M v
  have hhcost : sqNormOn Set.univ C.h ≤ CC.baseCost / P.eta j *
      ∑ n : {n : IntVec d // n ∈ current}, ‖u n‖ ^ 2 := by
    rw [C.h_eq]
    change sqNormOn Set.univ (plan.thinCarrier.interpolate M v) ≤ _
    calc
      _ ≤ (2 / (K.lower * plan.theta)) *
          ∑ n : {n : IntVec d // n ∈ plan.guard}, ‖v n‖ ^ 2 := hhcost0
      _ ≤ (2 / (K.lower * plan.theta)) *
          ((1 / EC.lower ^ 2) *
            ∑ n : {n : IntVec d // n ∈ current}, ‖u n‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hvsum
          (div_nonneg (by norm_num)
            (mul_nonneg K.lower_pos.le plan.theta_pos.le))
      _ = CC.baseCost / P.eta j *
          ∑ n : {n : IntVec d // n ∈ current}, ‖u n‖ ^ 2 := by
        rw [plan.theta_eq, CC.baseCost_eq]
        have hdR : 0 < (d : Real) := by exact_mod_cast hd
        have hsR : 0 < (CC.shiftCard : Real) := by
          exact_mod_cast CC.shiftCard_pos
        field_simp [K.lower_pos.ne', EC.lower_pos.ne', heta_pos.ne',
          hdR.ne', hsR.ne']
        ring
  have hhstrong : AEStronglyMeasurable C.h volume := by
    rw [C.h_eq]
    exact (plan.thinCarrier.interpolate_stronglyMeasurable M v).aestronglyMeasurable
  have hhint : Integrable C.h volume := by
    rw [C.h_eq]
    exact plan.thinCarrier.interpolate_integrable M v
  have hhLp : MemLp C.h (2 : ENNReal) volume := by
    rw [C.h_eq]
    exact plan.thinCarrier.interpolate_memLp M v
  have hhsupp : AESupportedIn C.h
      (integerEmbed M +ᵥ plan.thinCarrier.omega) := by
    rw [C.h_eq]
    exact plan.thinCarrier.interpolate_supported M v
  have hgeo := shiftPolynomialCarrier_support_measure plan.blockCoeffs M
    plan.thinCarrier.omega_measurable plan.thinCarrier.omega_subset hhsupp
  have hanalytic := shiftPolynomialCarrier_analytic_cost plan.blockCoeffs M
    hhstrong hhint hhLp hhsupp
  have hh_nonneg : 0 ≤ sqNormOn Set.univ C.h := by
    rw [sqNormOn, setIntegral_univ]
    exact integral_nonneg fun x => sq_nonneg ‖C.h x‖
  have hcoeff : (plan.blockCoeffs.support.sum fun a =>
      ‖plan.blockCoeffs a‖ ^ 2) ≤ 4 * EC.upper ^ 2 := by
    rw [plan.blockCoeffs_eq]
    exact plan.shiftData.coeff_sq_le
  rw [C.carrierFn_eq, hanalytic.2.2.2 hgeo.2.2.2]
  calc
    _ ≤ (4 * EC.upper ^ 2) * sqNormOn Set.univ C.h :=
      mul_le_mul_of_nonneg_right hcoeff hh_nonneg
    _ ≤ _ := mul_le_mul_of_nonneg_left hhcost (by positivity)

private theorem coordinateCorrection_interpolant_energy {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    {data : ModifiedFrequencyData delta} {K : ExponentialBoundsHD data.nu}
    {mu0 : Real} {P : BlockParameters hd delta hdelta data mu0}
    {budgets : BudgetConstants P}
    {EC : ExceptionalConstants hd delta hdelta data P}
    {CC : CorrectionConstants hd data K P budgets EC}
    {threshold : BlockThreshold CC} {j : Nat} {r : Fin d}
    {hactive : (coordinateBlock delta hdelta data.C0 hd j r).Nonempty}
    {hlate : threshold.J ≤ j}
    {plan : BlockPlan hd data K P budgets EC CC threshold j r hactive hlate}
    {M : IntVec d}
    {u : {n : IntVec d // n ∈ coordinateBlock delta hdelta data.C0 hd j r} →
      Complex} (C : CoordinateCorrection plan M u) :
    sqNormOn Set.univ C.h ≤ CC.baseCost / P.eta j * ∑ n, ‖u n‖ ^ 2 := by
  classical
  let current := coordinateBlock delta hdelta data.C0 hd j r
  let v : {n : IntVec d // n ∈ plan.guard} → Complex :=
    coordinateInterpolationValues plan u
  have hsep : EC.jSep ≤ j :=
    (le_max_right 3 EC.jSep).trans (threshold.J_ge.trans hlate)
  have hcurrent_guard : ∀ n ∈ current, n ∈ plan.guard := by
    intro n hn
    rw [plan.guard_eq, guardFinset]
    apply Finset.mem_biUnion.mpr
    have hthree : 3 ≤ j :=
      (le_max_left 3 EC.jSep).trans (threshold.J_ge.trans hlate)
    exact ⟨j, Finset.mem_Icc.mpr ⟨hthree, by omega⟩,
      (mem_coordinateBlock_iff.mp hn).choose⟩
  let extEnergy : IntVec d → Real := fun n =>
    if hn : n ∈ current then (1 / EC.lower ^ 2) * ‖u ⟨n, hn⟩‖ ^ 2 else 0
  have hv_sq_le (n : {n : IntVec d // n ∈ plan.guard}) :
      ‖v n‖ ^ 2 ≤ extEnergy n.1 := by
    by_cases hn : n.1 ∈ current
    · have hlower := (blockMultiplier_bounds hd EC).1 j r n.1 hsep hn
      dsimp only [v, extEnergy]
      rw [coordinateInterpolationValues, dif_pos hn, dif_pos hn,
        norm_div, norm_neg, div_pow]
      have hsquare : EC.lower ^ 2 ≤
          ‖blockMultiplier data j r (frequency delta n.1)‖ ^ 2 :=
        pow_le_pow_left₀ EC.lower_pos.le hlower 2
      calc
        ‖u ⟨n.1, _⟩‖ ^ 2 /
            ‖blockMultiplier data j r (frequency delta n.1)‖ ^ 2 ≤
            ‖u ⟨n.1, _⟩‖ ^ 2 / EC.lower ^ 2 :=
          div_le_div_of_nonneg_left (sq_nonneg _)
            (sq_pos_of_pos EC.lower_pos) hsquare
        _ = (1 / EC.lower ^ 2) * ‖u ⟨n.1, _⟩‖ ^ 2 := by ring
    · dsimp only [v, extEnergy]
      rw [coordinateInterpolationValues, dif_neg hn, dif_neg hn, norm_zero,
        zero_pow (by norm_num)]
  have hcurrent_subset : current ⊆ plan.guard := fun n hn => hcurrent_guard n hn
  have hext_sum :
      (∑ n : {n : IntVec d // n ∈ plan.guard}, extEnergy n.1) =
        (1 / EC.lower ^ 2) *
          ∑ n : {n : IntVec d // n ∈ current}, ‖u n‖ ^ 2 := by
    calc
      (∑ n : {n : IntVec d // n ∈ plan.guard}, extEnergy n.1) =
          ∑ n ∈ plan.guard, extEnergy n := by
        rw [← plan.guard.sum_attach]
        simp
      _ = ∑ n ∈ current, extEnergy n := by
        symm
        apply Finset.sum_subset hcurrent_subset
        intro n _ hncurrent
        simp [extEnergy, hncurrent]
      _ = ∑ n : {n : IntVec d // n ∈ current}, extEnergy n.1 := by
        rw [← current.sum_attach]
        simp
      _ = (1 / EC.lower ^ 2) *
          ∑ n : {n : IntVec d // n ∈ current}, ‖u n‖ ^ 2 := by
        simp only [extEnergy, Subtype.property, ↓reduceDIte, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        congr 3
  have hvsum : (∑ n : {n : IntVec d // n ∈ plan.guard}, ‖v n‖ ^ 2) ≤
      (1 / EC.lower ^ 2) *
        ∑ n : {n : IntVec d // n ∈ current}, ‖u n‖ ^ 2 := by
    calc
      _ ≤ ∑ n : {n : IntVec d // n ∈ plan.guard}, extEnergy n.1 :=
        Finset.sum_le_sum fun n _ => hv_sq_le n
      _ = _ := hext_sum
  have heta_pos : 0 < P.eta j :=
    budgets.eta_pos j
      ((le_max_left 3 EC.jSep).trans (threshold.J_ge.trans hlate))
  have hhcost0 := plan.thinCarrier.interpolate_cost M v
  rw [C.h_eq]
  change sqNormOn Set.univ (plan.thinCarrier.interpolate M v) ≤ _
  calc
    _ ≤ (2 / (K.lower * plan.theta)) *
        ∑ n : {n : IntVec d // n ∈ plan.guard}, ‖v n‖ ^ 2 := hhcost0
    _ ≤ (2 / (K.lower * plan.theta)) *
        ((1 / EC.lower ^ 2) *
          ∑ n : {n : IntVec d // n ∈ current}, ‖u n‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hvsum
        (div_nonneg (by norm_num)
          (mul_nonneg K.lower_pos.le plan.theta_pos.le))
    _ = CC.baseCost / P.eta j *
        ∑ n : {n : IntVec d // n ∈ current}, ‖u n‖ ^ 2 := by
      rw [plan.theta_eq, CC.baseCost_eq]
      have hdR : 0 < (d : Real) := by exact_mod_cast hd
      have hsR : 0 < (CC.shiftCard : Real) := by
        exact_mod_cast CC.shiftCard_pos
      field_simp [K.lower_pos.ne', EC.lower_pos.ne', heta_pos.ne',
        hdR.ne', hsR.ne']
      ring

private theorem coordinateCorrection_combined_energy {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    {data : ModifiedFrequencyData delta} {K : ExponentialBoundsHD data.nu}
    {mu0 : Real} {P : BlockParameters hd delta hdelta data mu0}
    {budgets : BudgetConstants P}
    {EC : ExceptionalConstants hd delta hdelta data P}
    {CC : CorrectionConstants hd data K P budgets EC}
    {threshold : BlockThreshold CC} {j : Nat} {r : Fin d}
    {hactive : (coordinateBlock delta hdelta data.C0 hd j r).Nonempty}
    {hlate : threshold.J ≤ j}
    {plan : BlockPlan hd data K P budgets EC CC threshold j r hactive hlate}
    {M : IntVec d}
    {u : {n : IntVec d // n ∈ coordinateBlock delta hdelta data.C0 hd j r} →
      Complex} (C : CoordinateCorrection plan M u) :
    sqNormOn Set.univ C.carrierFn +
        sqNormOn Set.univ (firstCoordinateDifference hd C.carrierFn) ≤
      CC.cost / P.eta j * ∑ n, ‖u n‖ ^ 2 := by
  have hdiff := firstCoordinateDifference_support_cost hd C.carrierSet_measurable
    C.carrierFn_stronglyMeasurable C.carrierFn_integrable C.carrierFn_memLp
    C.carrierFn_supported
  have hsharp := coordinateCorrection_carrier_energy_sharp C
  have hG0 : 0 ≤ sqNormOn Set.univ C.carrierFn := by
    rw [sqNormOn, setIntegral_univ]
    exact integral_nonneg fun x => sq_nonneg ‖C.carrierFn x‖
  have heta_pos : 0 < P.eta j :=
    budgets.eta_pos j
      ((le_max_left 3 EC.jSep).trans (threshold.J_ge.trans hlate))
  calc
    sqNormOn Set.univ C.carrierFn +
        sqNormOn Set.univ (firstCoordinateDifference hd C.carrierFn) ≤
        5 * sqNormOn Set.univ C.carrierFn := by
      linarith [hdiff.2.2.2.2.2.2]
    _ ≤ 5 * (4 * EC.upper ^ 2 * (CC.baseCost / P.eta j *
        ∑ n, ‖u n‖ ^ 2)) := mul_le_mul_of_nonneg_left hsharp (by norm_num)
    _ = CC.cost / P.eta j * ∑ n, ‖u n‖ ^ 2 := by
      rw [CC.cost_eq]
      ring

/-- Interpolate once, then apply the cached block multiplier. -/
noncomputable def buildCoordinateCorrection {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    {data : ModifiedFrequencyData delta} {K : ExponentialBoundsHD data.nu}
    {mu0 : Real} {P : BlockParameters hd delta hdelta data mu0}
    {budgets : BudgetConstants P}
    {EC : ExceptionalConstants hd delta hdelta data P}
    {CC : CorrectionConstants hd data K P budgets EC}
    {threshold : BlockThreshold CC} {j : Nat} {r : Fin d}
    {hactive : (coordinateBlock delta hdelta data.C0 hd j r).Nonempty}
    {hlate : threshold.J ≤ j}
    (plan : BlockPlan hd data K P budgets EC CC threshold j r hactive hlate)
    (M : IntVec d)
    (u : {n : IntVec d // n ∈ coordinateBlock delta hdelta data.C0 hd j r} →
      Complex) : CoordinateCorrection plan M u :=
  Classical.choice (coordinateCorrection_nonempty plan M u)

/-- Restriction of one level residual to a coordinate piece. -/
def coordinateResidual {d : Nat} {delta : IntVec d → RealVec d}
    {hdelta : TendsToZeroAtIntVecInfinity delta} {C0 : Finset (IntVec d)}
    {hd : 0 < d} {j : Nat}
    (u : {n : IntVec d // n ∈ dyadicBlock delta hdelta C0 j} → Complex)
    (r : Fin d) :
    {n : IntVec d // n ∈ coordinateBlock delta hdelta C0 hd j r} → Complex :=
  fun n => u ⟨n.1, (mem_coordinateBlock_iff.mp n.2).choose⟩

/-- One cached coordinate plan with its activity proof. -/
structure CoordinatePlanPackage {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    {data : ModifiedFrequencyData delta} {K : ExponentialBoundsHD data.nu}
    {mu0 : Real} {P : BlockParameters hd delta hdelta data mu0}
    {budgets : BudgetConstants P}
    {EC : ExceptionalConstants hd delta hdelta data P}
    {CC : CorrectionConstants hd data K P budgets EC}
    (threshold : BlockThreshold CC) (j : Nat) (hlate : threshold.J ≤ j)
    (r : Fin d) where
  active : (coordinateBlock delta hdelta data.C0 hd j r).Nonempty
  plan : BlockPlan hd data K P budgets EC CC threshold j r active hlate

/-- Cached coordinate plans at a single level. -/
abbrev CoordinatePlanFamily {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    {data : ModifiedFrequencyData delta} {K : ExponentialBoundsHD data.nu}
    {mu0 : Real} {P : BlockParameters hd delta hdelta data mu0}
    {budgets : BudgetConstants P}
    {EC : ExceptionalConstants hd delta hdelta data P}
    {CC : CorrectionConstants hd data K P budgets EC}
    (threshold : BlockThreshold CC) (j : Nat) (hlate : threshold.J ≤ j) :=
  (r : Fin d) → Option (CoordinatePlanPackage threshold j hlate r)

/-- Cached plans occur exactly on nonempty coordinate pieces. -/
structure CoordinatePlanCoverage {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    {data : ModifiedFrequencyData delta} {K : ExponentialBoundsHD data.nu}
    {mu0 : Real} {P : BlockParameters hd delta hdelta data mu0}
    {budgets : BudgetConstants P}
    {EC : ExceptionalConstants hd delta hdelta data P}
    {CC : CorrectionConstants hd data K P budgets EC}
    {threshold : BlockThreshold CC} {j : Nat} {hlate : threshold.J ≤ j}
    (plans : CoordinatePlanFamily threshold j hlate) : Prop where
  none_iff : ∀ r, plans r = none ↔
    ¬(coordinateBlock delta hdelta data.C0 hd j r).Nonempty

/-- Empty plans contribute empty base envelopes. -/
def levelBaseEnvelope {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    {data : ModifiedFrequencyData delta} {K : ExponentialBoundsHD data.nu}
    {mu0 : Real} {P : BlockParameters hd delta hdelta data mu0}
    {budgets : BudgetConstants P}
    {EC : ExceptionalConstants hd delta hdelta data P}
    {CC : CorrectionConstants hd data K P budgets EC}
    {threshold : BlockThreshold CC} {j : Nat} {hlate : threshold.J ≤ j}
    (plans : CoordinatePlanFamily threshold j hlate) (origins : Fin d → IntVec d)
    (r : Fin d) : Set (RealVec d) :=
  match plans r with
  | none => ∅
  | some p => coordinateBaseEnvelope p.plan (origins r)

/-- Empty plans contribute empty difference envelopes. -/
def levelDifferenceEnvelope {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    {data : ModifiedFrequencyData delta} {K : ExponentialBoundsHD data.nu}
    {mu0 : Real} {P : BlockParameters hd delta hdelta data mu0}
    {budgets : BudgetConstants P}
    {EC : ExceptionalConstants hd delta hdelta data P}
    {CC : CorrectionConstants hd data K P budgets EC}
    {threshold : BlockThreshold CC} {j : Nat} {hlate : threshold.J ≤ j}
    (plans : CoordinatePlanFamily threshold j hlate) (origins : Fin d → IntVec d)
    (r : Fin d) : Set (RealVec d) :=
  match plans r with
  | none => ∅
  | some p => coordinateDifferenceEnvelope p.plan (origins r)

/-- Certified within-level packing of all cached coordinate envelopes. -/
structure LevelPacking {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    {data : ModifiedFrequencyData delta} {K : ExponentialBoundsHD data.nu}
    {mu0 : Real} {P : BlockParameters hd delta hdelta data mu0}
    {budgets : BudgetConstants P}
    {EC : ExceptionalConstants hd delta hdelta data P}
    {CC : CorrectionConstants hd data K P budgets EC}
    {threshold : BlockThreshold CC} {j : Nat} {hlate : threshold.J ≤ j}
    (plans : CoordinatePlanFamily threshold j hlate)
    (origins : Fin d → IntVec d) : Prop where
  basePairwise : Set.Pairwise (Set.univ : Set (Fin d)) fun r q =>
    Disjoint (levelBaseEnvelope plans origins r) (levelBaseEnvelope plans origins q)
  differencePairwise : Set.Pairwise (Set.univ : Set (Fin d)) fun r q =>
    Disjoint (levelDifferenceEnvelope plans origins r)
      (levelDifferenceEnvelope plans origins q)

/-- A built coordinate correction tied to the exact cached plan. -/
structure CoordinateCorrectionPackage {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    {data : ModifiedFrequencyData delta} {K : ExponentialBoundsHD data.nu}
    {mu0 : Real} {P : BlockParameters hd delta hdelta data mu0}
    {budgets : BudgetConstants P}
    {EC : ExceptionalConstants hd delta hdelta data P}
    {CC : CorrectionConstants hd data K P budgets EC}
    {threshold : BlockThreshold CC} {j : Nat} {hlate : threshold.J ≤ j}
    (plans : CoordinatePlanFamily threshold j hlate)
    (origins : Fin d → IntVec d)
    (u : {n : IntVec d // n ∈ dyadicBlock delta hdelta data.C0 j} → Complex)
    (r : Fin d) where
  cached : CoordinatePlanPackage threshold j hlate r
  cached_eq : plans r = some cached
  correction : CoordinateCorrection cached.plan (origins r)
    (coordinateResidual u r)

/-- Transparent function projection from an optional coordinate package. -/
def coordinatePackageFn {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    {data : ModifiedFrequencyData delta} {K : ExponentialBoundsHD data.nu}
    {mu0 : Real} {P : BlockParameters hd delta hdelta data mu0}
    {budgets : BudgetConstants P}
    {EC : ExceptionalConstants hd delta hdelta data P}
    {CC : CorrectionConstants hd data K P budgets EC}
    {threshold : BlockThreshold CC} {j : Nat} {hlate : threshold.J ≤ j}
    {plans : CoordinatePlanFamily threshold j hlate}
    {origins : Fin d → IntVec d}
    {u : {n : IntVec d // n ∈ dyadicBlock delta hdelta data.C0 j} → Complex}
    {r : Fin d} (package : Option (CoordinateCorrectionPackage plans origins u r)) :
    RealVec d → Complex :=
  match package with
  | none => fun _ => 0
  | some p => p.correction.carrierFn

/-- Transparent support-set projection from an optional coordinate package. -/
def coordinatePackageSet {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    {data : ModifiedFrequencyData delta} {K : ExponentialBoundsHD data.nu}
    {mu0 : Real} {P : BlockParameters hd delta hdelta data mu0}
    {budgets : BudgetConstants P}
    {EC : ExceptionalConstants hd delta hdelta data P}
    {CC : CorrectionConstants hd data K P budgets EC}
    {threshold : BlockThreshold CC} {j : Nat} {hlate : threshold.J ≤ j}
    {plans : CoordinatePlanFamily threshold j hlate}
    {origins : Fin d → IntVec d}
    {u : {n : IntVec d // n ∈ dyadicBlock delta hdelta data.C0 j} → Complex}
    {r : Fin d} (package : Option (CoordinateCorrectionPackage plans origins u r)) :
    Set (RealVec d) :=
  match package with
  | none => ∅
  | some p => p.correction.carrierSet

private theorem norm_sq_finset_sum_of_disjoint_supports
    {ι α : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → α → Complex) (A : ι → Set α)
    (hpair : Set.Pairwise (↑s : Set ι) fun i k => Disjoint (A i) (A k))
    {x : α} (hzero : ∀ i ∈ s, x ∉ A i → f i x = 0) :
    ‖∑ i ∈ s, f i x‖ ^ 2 = ∑ i ∈ s, ‖f i x‖ ^ 2 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      by_cases hxa : x ∈ A a
      · have hz (i : ι) (hi : i ∈ s) : f i x = 0 := by
          apply hzero i (Finset.mem_insert_of_mem hi)
          intro hxi
          have hai : a ≠ i := fun hai => ha (hai ▸ hi)
          exact Set.disjoint_left.mp
            (hpair (Finset.mem_coe.mpr (Finset.mem_insert_self a s))
              (Finset.mem_coe.mpr (Finset.mem_insert_of_mem hi)) hai) hxa hxi
        simp only [Finset.sum_insert ha]
        rw [Finset.sum_eq_zero fun i hi => hz i hi]
        rw [Finset.sum_eq_zero fun i hi => by rw [hz i hi, norm_zero,
          zero_pow (by norm_num)]]
        simp
      · have hfa : f a x = 0 :=
          hzero a (Finset.mem_insert_self a s) hxa
        have hind := ih (by
          intro i hi k hk hik
          exact hpair (Finset.mem_coe.mpr (Finset.mem_insert_of_mem hi))
            (Finset.mem_coe.mpr (Finset.mem_insert_of_mem hk)) hik) (by
          intro i hi
          exact hzero i (Finset.mem_insert_of_mem hi))
        simpa [Finset.sum_insert, ha, hfa] using hind

private theorem sqNormOn_finset_sum_of_disjoint_supports
    {d : Nat} {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → RealVec d → Complex) (A : ι → Set (RealVec d))
    (hpair : Set.Pairwise (↑s : Set ι) fun i k => Disjoint (A i) (A k))
    (hLp : ∀ i ∈ s, MemLp (f i) (2 : ENNReal) volume)
    (hsupp : ∀ i ∈ s, AESupportedIn (f i) (A i)) :
    sqNormOn Set.univ (fun x => ∑ i ∈ s, f i x) =
      ∑ i ∈ s, sqNormOn Set.univ (f i) := by
  have hall : ∀ᵐ x ∂volume, ∀ i ∈ s, x ∉ A i → f i x = 0 :=
    (Filter.eventually_all_finset s).mpr fun i hi => hsupp i hi
  have hpoint : ∀ᵐ x ∂volume,
      ‖∑ i ∈ s, f i x‖ ^ 2 = ∑ i ∈ s, ‖f i x‖ ^ 2 :=
    hall.mono fun x hx => norm_sq_finset_sum_of_disjoint_supports s f A hpair hx
  rw [sqNormOn, setIntegral_univ]
  calc
    (∫ x, ‖∑ i ∈ s, f i x‖ ^ 2) =
        ∫ x, ∑ i ∈ s, ‖f i x‖ ^ 2 := integral_congr_ae hpoint
    _ = ∑ i ∈ s, ∫ x, ‖f i x‖ ^ 2 := by
      rw [integral_finsetSum]
      intro i hi
      exact (hLp i hi).integrable_norm_pow (by norm_num)
    _ = ∑ i ∈ s, sqNormOn Set.univ (f i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [sqNormOn, setIntegral_univ]

/-- Total correction and difference data for one active level. -/
structure LevelCorrectionResult {d : Nat} (hd : 0 < d)
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    (data : ModifiedFrequencyData delta) (K : ExponentialBoundsHD data.nu)
    {mu0 : Real} (P : BlockParameters hd delta hdelta data mu0)
    (budgets : BudgetConstants P)
    (EC : ExceptionalConstants hd delta hdelta data P)
    (CC : CorrectionConstants hd data K P budgets EC)
    (threshold : BlockThreshold CC) (j : Nat) (hlate : threshold.J ≤ j)
    (plans : CoordinatePlanFamily threshold j hlate)
    (origins : Fin d → IntVec d)
    (u : {n : IntVec d // n ∈ dyadicBlock delta hdelta data.C0 j} → Complex)
    (hactive : (dyadicBlock delta hdelta data.C0 j).Nonempty) where
  coordinateCorrection : (r : Fin d) → Option
    (CoordinateCorrectionPackage plans origins u r)
  coordinateCorrection_none_iff : ∀ r,
    coordinateCorrection r = none ↔
      ¬(coordinateBlock delta hdelta data.C0 hd j r).Nonempty
  carrierFn : RealVec d → Complex
  carrierFn_eq : carrierFn = fun x =>
    ∑ r, coordinatePackageFn (coordinateCorrection r) x
  differenceFn : RealVec d → Complex
  carrierSet : Set (RealVec d)
  carrierSet_eq : carrierSet = ⋃ r, coordinatePackageSet (coordinateCorrection r)
  differenceCarrierSet : Set (RealVec d)
  differenceFn_eq : differenceFn = firstCoordinateDifference hd carrierFn
  differenceCarrierSet_eq : differenceCarrierSet =
    (basisVector (firstCoordinate hd) +ᵥ carrierSet) ∪ carrierSet
  carrierSet_measurable : MeasurableSet carrierSet
  differenceCarrierSet_measurable : MeasurableSet differenceCarrierSet
  carrierFn_stronglyMeasurable : AEStronglyMeasurable carrierFn volume
  differenceFn_stronglyMeasurable : AEStronglyMeasurable differenceFn volume
  carrierFn_integrable : Integrable carrierFn volume
  differenceFn_integrable : Integrable differenceFn volume
  carrierFn_memLp : MemLp carrierFn (2 : ENNReal) volume
  differenceFn_memLp : MemLp differenceFn (2 : ENNReal) volume
  carrierFn_supported : AESupportedIn carrierFn carrierSet
  differenceFn_supported : AESupportedIn differenceFn differenceCarrierSet
  current_trace : ∀ n,
    inverseSample carrierFn (frequency delta n.1) = -u n
  guard_trace : ∀ k, 3 ≤ k → k ≤ 4 * j → k ≠ j → ∀ n,
    n ∈ dyadicBlock delta hdelta data.C0 k →
      inverseSample carrierFn (frequency delta n) = 0
  exceptional_trace : ∀ n ∈ data.C0,
    inverseSample carrierFn (frequency delta n) = 0
  carrierSet_contained : carrierSet ⊆ ⋃ r, levelBaseEnvelope plans origins r
  differenceCarrierSet_contained :
    differenceCarrierSet ⊆ ⋃ r, levelDifferenceEnvelope plans origins r
  carrier_volume : volume carrierSet ≤ ENNReal.ofReal (P.eta j / 2)
  differenceCarrier_volume :
    volume differenceCarrierSet ≤ ENNReal.ofReal (P.eta j)
  combined_energy : sqNormOn Set.univ carrierFn + sqNormOn Set.univ differenceFn ≤
    CC.cost / P.eta j * ∑ n, ‖u n‖ ^ 2

/-- Existence theorem for the packed sum of all active coordinate corrections. -/
theorem levelCorrectionResult_nonempty {d : Nat} (hd : 0 < d)
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    (data : ModifiedFrequencyData delta) (K : ExponentialBoundsHD data.nu)
    {mu0 : Real} (P : BlockParameters hd delta hdelta data mu0)
    (budgets : BudgetConstants P)
    (EC : ExceptionalConstants hd delta hdelta data P)
    (CC : CorrectionConstants hd data K P budgets EC)
    (threshold : BlockThreshold CC) (j : Nat) (hlate : threshold.J ≤ j)
    (plans : CoordinatePlanFamily threshold j hlate)
    (coverage : CoordinatePlanCoverage plans)
    (origins : Fin d → IntVec d)
    (packing : LevelPacking plans origins)
    (u : {n : IntVec d // n ∈ dyadicBlock delta hdelta data.C0 j} → Complex)
    (hactive : (dyadicBlock delta hdelta data.C0 j).Nonempty) :
    Nonempty (LevelCorrectionResult hd data K P budgets EC CC threshold j hlate plans
      origins u hactive) := by
  classical
  let packages : (r : Fin d) → Option
      (CoordinateCorrectionPackage plans origins u r) := fun r =>
    match hpr : plans r with
    | none => none
    | some p => some {
        cached := p
        cached_eq := hpr
        correction := buildCoordinateCorrection p.plan (origins r)
          (coordinateResidual u r) }
  let f : Fin d → RealVec d → Complex := fun r =>
    coordinatePackageFn (packages r)
  let Ar : Fin d → Set (RealVec d) := fun r =>
    coordinatePackageSet (packages r)
  let G : RealVec d → Complex := fun x => ∑ r, f r x
  let A : Set (RealVec d) := ⋃ r, Ar r
  let H : RealVec d → Complex := firstCoordinateDifference hd G
  let Adiff : Set (RealVec d) := (basisVector (firstCoordinate hd) +ᵥ A) ∪ A
  have hnone : ∀ r, packages r = none ↔
      ¬(coordinateBlock delta hdelta data.C0 hd j r).Nonempty := by
    intro r
    rw [← coverage.none_iff r]
    unfold packages
    split <;> simp_all
  have hfmeas (r : Fin d) : AEStronglyMeasurable (f r) volume := by
    unfold f
    cases hq : packages r with
    | none =>
        simpa only [coordinatePackageFn, hq] using
          (aestronglyMeasurable_const :
            AEStronglyMeasurable (fun _ : RealVec d => (0 : Complex)) volume)
    | some q =>
        simpa [coordinatePackageFn, hq] using
          q.correction.carrierFn_stronglyMeasurable
  have hfint (r : Fin d) : Integrable (f r) volume := by
    unfold f
    cases hq : packages r with
    | none => simp [coordinatePackageFn]
    | some q => simpa [coordinatePackageFn, hq] using q.correction.carrierFn_integrable
  have hfLp (r : Fin d) : MemLp (f r) (2 : ENNReal) volume := by
    unfold f
    cases hq : packages r with
    | none => simp [coordinatePackageFn]
    | some q => simpa [coordinatePackageFn, hq] using q.correction.carrierFn_memLp
  have hArmeas (r : Fin d) : MeasurableSet (Ar r) := by
    unfold Ar
    cases hq : packages r with
    | none => simp [coordinatePackageSet]
    | some q => simpa [coordinatePackageSet, hq] using q.correction.carrierSet_measurable
  have hfsupp (r : Fin d) : AESupportedIn (f r) (Ar r) := by
    unfold f Ar
    cases hq : packages r with
    | none => simp [coordinatePackageFn, coordinatePackageSet, AESupportedIn]
    | some q => simpa [coordinatePackageFn, coordinatePackageSet, hq] using
        q.correction.carrierFn_supported
  have hAenv (r : Fin d) : Ar r ⊆ levelBaseEnvelope plans origins r := by
    unfold Ar
    cases hq : packages r with
    | none => simp [coordinatePackageSet]
    | some q =>
        simpa [coordinatePackageSet, hq, levelBaseEnvelope, q.cached_eq] using
          q.correction.carrierSet_contained
  have hArpair : Set.Pairwise (Set.univ : Set (Fin d)) fun r q =>
      Disjoint (Ar r) (Ar q) := by
    intro r _ q _ hrq
    exact (packing.basePairwise (Set.mem_univ r) (Set.mem_univ q) hrq).mono
      (hAenv r) (hAenv q)
  have hAmeas : MeasurableSet A := by
    unfold A
    exact MeasurableSet.iUnion hArmeas
  have hGmeas : AEStronglyMeasurable G volume := by
    unfold G
    refine (Finset.aestronglyMeasurable_sum Finset.univ
      fun r _ => hfmeas r).congr ?_
    filter_upwards [] with x
    simp only [Finset.sum_apply]
  have hGint : Integrable G volume := by
    unfold G
    exact integrable_finsetSum Finset.univ fun r _ => hfint r
  have hGLp : MemLp G (2 : ENNReal) volume := by
    unfold G
    exact memLp_finsetSum Finset.univ fun r _ => hfLp r
  have hGsupp : AESupportedIn G A := by
    have hall : ∀ᵐ x ∂volume, ∀ r : Fin d, x ∉ Ar r → f r x = 0 :=
      ae_all_iff.mpr fun r => hfsupp r
    filter_upwards [hall] with x hx
    intro hxA
    unfold G
    apply Finset.sum_eq_zero
    intro r _
    apply hx r
    intro hxr
    apply hxA
    exact Set.mem_iUnion.mpr ⟨r, hxr⟩
  have hchar_meas (xi : RealVec d) :
      AEStronglyMeasurable (fun x => fourierChar xi x) volume := by
    apply Continuous.aestronglyMeasurable
    unfold fourierChar
    fun_prop
  have hchar_bound (xi : RealVec d) :
      ∀ᵐ x ∂volume, ‖fourierChar xi x‖ ≤ (1 : Real) := by
    filter_upwards [] with x
    simp [fourierChar, Complex.norm_exp]
  have hinverse_sum (xi : RealVec d) :
      inverseSample G xi = ∑ r, inverseSample (f r) xi := by
    unfold inverseSample inverseSampleOn G
    simp only [Measure.restrict_univ, Finset.sum_mul]
    rw [integral_finsetSum]
    intro r _
    exact (hfint r).mul_bdd (hchar_meas xi) (hchar_bound xi)
  have hlevel_member_guard (r : Fin d) (q : CoordinateCorrectionPackage plans origins u r)
      {k : Nat} (hk3 : 3 ≤ k) (hkj : k ≤ 4 * j) {n : IntVec d}
      (hn : n ∈ dyadicBlock delta hdelta data.C0 k) : n ∈ q.cached.plan.guard := by
    rw [q.cached.plan.guard_eq, guardFinset]
    exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_Icc.mpr ⟨hk3, hkj⟩, hn⟩
  have hterm_current (n : {n : IntVec d //
      n ∈ dyadicBlock delta hdelta data.C0 j}) (r : Fin d) :
      inverseSample (f r) (frequency delta n.1) =
        if hn : n.1 ∈ coordinateBlock delta hdelta data.C0 hd j r
        then -u n else 0 := by
    cases hq : packages r with
    | none =>
        have hempty : ¬(coordinateBlock delta hdelta data.C0 hd j r).Nonempty :=
          (hnone r).mp hq
        have hnmem : n.1 ∉ coordinateBlock delta hdelta data.C0 hd j r :=
          fun hn => hempty ⟨n.1, hn⟩
        simp [f, coordinatePackageFn, hq, hnmem, inverseSample,
          inverseSampleOn]
    | some q =>
        by_cases hn : n.1 ∈ coordinateBlock delta hdelta data.C0 hd j r
        · have ht := q.correction.current_trace ⟨n.1, hn⟩
          simpa [f, coordinatePackageFn, hq, hn, coordinateResidual] using ht
        · have hguard := hlevel_member_guard r q
            ((le_max_left 3 EC.jSep).trans (threshold.J_ge.trans hlate))
            (by omega) n.property
          have ht := q.correction.guard_trace n.1 hguard hn
          simpa [f, coordinatePackageFn, hq, hn] using ht
  have hcurrent_trace : ∀ n : {n : IntVec d //
      n ∈ dyadicBlock delta hdelta data.C0 j},
      inverseSample G (frequency delta n.1) = -u n := by
    intro n
    rw [hinverse_sum]
    simp_rw [hterm_current n]
    let r0 := (Internal.maxCoordinate hd (delta n.1)
      (mem_dyadicBlock_iff.mp n.property).2.1).coordinate
    have hr0 : n.1 ∈ coordinateBlock delta hdelta data.C0 hd j r0 :=
      mem_coordinateBlock_iff.mpr ⟨n.property, rfl⟩
    rw [Finset.sum_eq_single r0]
    · simp [hr0]
    · intro q _ hqr
      have hnq : n.1 ∉ coordinateBlock delta hdelta data.C0 hd j q := by
        intro hnq
        have hdis := (coordinateBlocks_partition hd hdelta data.C0).1 j
          (Set.mem_univ q) (Set.mem_univ r0) hqr
        exact Finset.disjoint_left.mp hdis hnq hr0
      simp [hnq]
    · simp
  have hguard_trace : ∀ k, 3 ≤ k → k ≤ 4 * j → k ≠ j → ∀ n,
      n ∈ dyadicBlock delta hdelta data.C0 k →
        inverseSample G (frequency delta n) = 0 := by
    intro k hk3 hkj hkjne n hn
    rw [hinverse_sum]
    apply Finset.sum_eq_zero
    intro r _
    cases hq : packages r with
    | none => simp [f, coordinatePackageFn, hq, inverseSample, inverseSampleOn]
    | some q =>
        have hng := hlevel_member_guard r q hk3 hkj hn
        have hncoord : n ∉ coordinateBlock delta hdelta data.C0 hd j r := by
          intro hnr
          have hnj := (mem_coordinateBlock_iff.mp hnr).choose
          have hdis := (coordinateBlocks_partition hd hdelta data.C0).2.2.1 k j hkjne
          exact Finset.disjoint_left.mp hdis hn hnj
        simpa [f, coordinatePackageFn, hq] using
          q.correction.guard_trace n hng hncoord
  have hexceptional_trace : ∀ n ∈ data.C0,
      inverseSample G (frequency delta n) = 0 := by
    intro n hn
    rw [hinverse_sum]
    apply Finset.sum_eq_zero
    intro r _
    cases hq : packages r with
    | none => simp [f, coordinatePackageFn, hq, inverseSample, inverseSampleOn]
    | some q => simpa [f, coordinatePackageFn, hq] using
        q.correction.exceptional_trace n hn
  have hAcontained : A ⊆ ⋃ r, levelBaseEnvelope plans origins r := by
    intro x hx
    obtain ⟨r, hxr⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨r, hAenv r hxr⟩
  have hArvolume (r : Fin d) :
      volume (Ar r) ≤ ENNReal.ofReal (P.eta j / (2 * (d : Real))) := by
    unfold Ar
    cases hq : packages r with
    | none => simp [coordinatePackageSet]
    | some q => simpa [coordinatePackageSet, hq] using q.correction.carrier_volume
  have hAvolume : volume A ≤ ENNReal.ofReal (P.eta j / 2) := by
    have heta0 : 0 ≤ P.eta j := budgets.eta_nonneg j
    have hdR : 0 < (d : Real) := by exact_mod_cast hd
    calc
      volume A ≤ ∑' r : Fin d, volume (Ar r) := by
        unfold A
        exact measure_iUnion_le _
      _ = ∑ r : Fin d, volume (Ar r) := tsum_fintype _
      _ ≤ ∑ r : Fin d, ENNReal.ofReal (P.eta j / (2 * (d : Real))) :=
        Finset.sum_le_sum fun r _ => hArvolume r
      _ = ENNReal.ofReal (P.eta j / 2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg d)]
        congr 1
        field_simp [hdR.ne']
  have hdiff := firstCoordinateDifference_support_cost hd hAmeas hGmeas hGint hGLp hGsupp
  have hAdiffvolume : volume Adiff ≤ ENNReal.ofReal (P.eta j) := by
    calc
      volume Adiff ≤ 2 * volume A := by simpa [Adiff] using hdiff.2.2.2.2.2.1
      _ ≤ 2 * ENNReal.ofReal (P.eta j / 2) := by gcongr
      _ = ENNReal.ofReal (P.eta j) := by
        rw [show (2 : ENNReal) = ENNReal.ofReal 2 by norm_num,
          ← ENNReal.ofReal_mul (by norm_num : (0 : Real) ≤ 2)]
        congr 1
        ring
  let Br : Fin d → Set (RealVec d) := fun r =>
    (basisVector (firstCoordinate hd) +ᵥ Ar r) ∪ Ar r
  have hBmeas (r : Fin d) : MeasurableSet (Br r) :=
    (hArmeas r).const_vadd _ |>.union (hArmeas r)
  have hBenv (r : Fin d) : Br r ⊆ levelDifferenceEnvelope plans origins r := by
    unfold Br Ar
    cases hq : packages r with
    | none => simp [coordinatePackageSet]
    | some q =>
        simp only [coordinatePackageSet, levelDifferenceEnvelope, q.cached_eq]
        intro x hx
        rcases hx with hx | hx
        · obtain ⟨y, hy, hyx⟩ := Set.mem_vadd_set.mp hx
          have hybase := q.correction.carrierSet_contained hy
          rcases hybase with ⟨hy0, hy1⟩
          have hyx0 := congrFun hyx (firstCoordinate hd)
          simp only [vadd_eq_add, Pi.add_apply, basisVector_apply, if_pos] at hyx0
          change (origins r (firstCoordinate hd) : Real) ≤ x (firstCoordinate hd) ∧
            x (firstCoordinate hd) ≤ (origins r (firstCoordinate hd) : Real) +
              q.cached.plan.shiftData.differenceEnvelopeWidth
          rw [q.cached.plan.shiftData.differenceEnvelopeWidth_eq]
          constructor <;> push_cast <;> linarith
        · have hxbase := q.correction.carrierSet_contained hx
          rcases hxbase with ⟨hx0, hx1⟩
          change (origins r (firstCoordinate hd) : Real) ≤ x (firstCoordinate hd) ∧
            x (firstCoordinate hd) ≤ (origins r (firstCoordinate hd) : Real) +
              q.cached.plan.shiftData.differenceEnvelopeWidth
          rw [q.cached.plan.shiftData.differenceEnvelopeWidth_eq]
          constructor <;> push_cast <;> linarith
  have hBrpair : Set.Pairwise (Set.univ : Set (Fin d)) fun r q =>
      Disjoint (Br r) (Br q) := by
    intro r _ q _ hrq
    exact (packing.differencePairwise (Set.mem_univ r) (Set.mem_univ q) hrq).mono
      (hBenv r) (hBenv q)
  have hAdiffcontained : Adiff ⊆ ⋃ r, levelDifferenceEnvelope plans origins r := by
    intro x hx
    rcases hx with hx | hx
    · obtain ⟨y, hyA, hyx⟩ := Set.mem_vadd_set.mp hx
      obtain ⟨r, hyr⟩ := Set.mem_iUnion.mp hyA
      apply Set.mem_iUnion.mpr
      refine ⟨r, hBenv r ?_⟩
      exact Or.inl (Set.mem_vadd_set.mpr ⟨y, hyr, hyx⟩)
    · obtain ⟨r, hxr⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨r, hBenv r (Or.inr hxr)⟩
  have hdiff_component_meas (r : Fin d) :
      AEStronglyMeasurable (firstCoordinateDifference hd (f r)) volume :=
    (firstCoordinateDifference_support_cost hd (hArmeas r) (hfmeas r)
      (hfint r) (hfLp r) (hfsupp r)).2.1
  have hdiff_component_int (r : Fin d) :
      Integrable (firstCoordinateDifference hd (f r)) volume :=
    (firstCoordinateDifference_support_cost hd (hArmeas r) (hfmeas r)
      (hfint r) (hfLp r) (hfsupp r)).2.2.1
  have hdiff_component_Lp (r : Fin d) :
      MemLp (firstCoordinateDifference hd (f r)) (2 : ENNReal) volume :=
    (firstCoordinateDifference_support_cost hd (hArmeas r) (hfmeas r)
      (hfint r) (hfLp r) (hfsupp r)).2.2.2.1
  have hdiff_component_supp (r : Fin d) :
      AESupportedIn (firstCoordinateDifference hd (f r)) (Br r) := by
    simpa [Br] using
      (firstCoordinateDifference_support_cost hd (hArmeas r) (hfmeas r)
        (hfint r) (hfLp r) (hfsupp r)).2.2.2.2.1
  have hHsum : H = fun x => ∑ r, firstCoordinateDifference hd (f r) x := by
    funext x
    simp only [H, G, firstCoordinateDifference, Internal.vectorTranslate]
    rw [Finset.sum_sub_distrib]
  have hGnorm : sqNormOn Set.univ G = ∑ r, sqNormOn Set.univ (f r) := by
    simpa [G] using sqNormOn_finset_sum_of_disjoint_supports Finset.univ f Ar
      (by simpa using hArpair) (fun r _ => hfLp r) (fun r _ => hfsupp r)
  have hHnorm : sqNormOn Set.univ H =
      ∑ r, sqNormOn Set.univ (firstCoordinateDifference hd (f r)) := by
    rw [hHsum]
    simpa using sqNormOn_finset_sum_of_disjoint_supports Finset.univ
      (fun r => firstCoordinateDifference hd (f r)) Br (by simpa using hBrpair)
      (fun r _ => hdiff_component_Lp r) (fun r _ => hdiff_component_supp r)
  have hcoordinate_energy (r : Fin d) :
      sqNormOn Set.univ (f r) +
          sqNormOn Set.univ (firstCoordinateDifference hd (f r)) ≤
        CC.cost / P.eta j *
          ∑ n : {n : IntVec d // n ∈ coordinateBlock delta hdelta data.C0 hd j r},
            ‖coordinateResidual u r n‖ ^ 2 := by
    cases hq : packages r with
    | none =>
        have heta : 0 < P.eta j := budgets.eta_pos j
          ((le_max_left 3 EC.jSep).trans (threshold.J_ge.trans hlate))
        have hnonneg : 0 ≤ CC.cost / P.eta j *
            ∑ n : {n : IntVec d //
              n ∈ coordinateBlock delta hdelta data.C0 hd j r},
              ‖coordinateResidual u r n‖ ^ 2 :=
          mul_nonneg (div_nonneg CC.cost_pos.le heta.le)
            (Finset.sum_nonneg fun _ _ => sq_nonneg _)
        simpa [f, coordinatePackageFn, hq, firstCoordinateDifference,
          Internal.vectorTranslate, sqNormOn] using hnonneg
    | some q =>
        simpa [f, coordinatePackageFn, hq] using
          coordinateCorrection_combined_energy q.correction
  have hpartition_energy :
      (∑ r : Fin d,
        ∑ n : {n : IntVec d // n ∈ coordinateBlock delta hdelta data.C0 hd j r},
          ‖coordinateResidual u r n‖ ^ 2) =
        ∑ n : {n : IntVec d // n ∈ dyadicBlock delta hdelta data.C0 j},
          ‖u n‖ ^ 2 := by
    let e : IntVec d → Real := fun n =>
      if hn : n ∈ dyadicBlock delta hdelta data.C0 j then ‖u ⟨n, hn⟩‖ ^ 2 else 0
    calc
      (∑ r : Fin d,
          ∑ n : {n : IntVec d // n ∈ coordinateBlock delta hdelta data.C0 hd j r},
            ‖coordinateResidual u r n‖ ^ 2) =
          ∑ r : Fin d, ∑ n ∈ coordinateBlock delta hdelta data.C0 hd j r, e n := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [← (coordinateBlock delta hdelta data.C0 hd j r).sum_attach]
        apply Finset.sum_congr rfl
        intro n _hn
        have hnblock : n.1 ∈ dyadicBlock delta hdelta data.C0 j :=
          (mem_coordinateBlock_iff.mp n.property).choose
        change ‖u ⟨n.1, (mem_coordinateBlock_iff.mp n.property).choose⟩‖ ^ 2 = e n.1
        rw [show e n.1 = ‖u ⟨n.1, hnblock⟩‖ ^ 2 by
          simp only [e, dif_pos hnblock]]
      _ = ∑ n ∈ dyadicBlock delta hdelta data.C0 j, e n := by
        rw [← Finset.sum_biUnion]
        · rw [(coordinateBlocks_partition hd hdelta data.C0).2.1 j]
        · intro r _ q _ hrq
          exact (coordinateBlocks_partition hd hdelta data.C0).1 j
            (Set.mem_univ r) (Set.mem_univ q) hrq
      _ = ∑ n : {n : IntVec d // n ∈ dyadicBlock delta hdelta data.C0 j},
          ‖u n‖ ^ 2 := by
        rw [← (dyadicBlock delta hdelta data.C0 j).sum_attach]
        apply Finset.sum_congr rfl
        intro n _hn
        simp only [e, dif_pos n.property]
  have hcombined : sqNormOn Set.univ G + sqNormOn Set.univ H ≤
      CC.cost / P.eta j * ∑ n, ‖u n‖ ^ 2 := by
    rw [hGnorm, hHnorm, ← Finset.sum_add_distrib]
    calc
      _ ≤ ∑ r : Fin d, (CC.cost / P.eta j *
          ∑ n : {n : IntVec d // n ∈ coordinateBlock delta hdelta data.C0 hd j r},
            ‖coordinateResidual u r n‖ ^ 2) :=
        Finset.sum_le_sum fun r _ => hcoordinate_energy r
      _ = CC.cost / P.eta j *
          (∑ r : Fin d,
            ∑ n : {n : IntVec d // n ∈ coordinateBlock delta hdelta data.C0 hd j r},
              ‖coordinateResidual u r n‖ ^ 2) := by rw [Finset.mul_sum]
      _ = _ := by rw [hpartition_energy]
  refine ⟨{
    coordinateCorrection := packages
    coordinateCorrection_none_iff := hnone
    carrierFn := G
    carrierFn_eq := rfl
    differenceFn := H
    carrierSet := A
    carrierSet_eq := rfl
    differenceCarrierSet := Adiff
    differenceFn_eq := rfl
    differenceCarrierSet_eq := rfl
    carrierSet_measurable := hAmeas
    differenceCarrierSet_measurable := by simpa [Adiff] using hdiff.1
    carrierFn_stronglyMeasurable := hGmeas
    differenceFn_stronglyMeasurable := by simpa [H] using hdiff.2.1
    carrierFn_integrable := hGint
    differenceFn_integrable := by simpa [H] using hdiff.2.2.1
    carrierFn_memLp := hGLp
    differenceFn_memLp := by simpa [H] using hdiff.2.2.2.1
    carrierFn_supported := hGsupp
    differenceFn_supported := by simpa [H, Adiff] using hdiff.2.2.2.2.1
    current_trace := hcurrent_trace
    guard_trace := hguard_trace
    exceptional_trace := hexceptional_trace
    carrierSet_contained := hAcontained
    differenceCarrierSet_contained := hAdiffcontained
    carrier_volume := hAvolume
    differenceCarrier_volume := hAdiffvolume
    combined_energy := hcombined }⟩

/-- Sum all active coordinate corrections at one level. -/
noncomputable def buildLevelCorrection {d : Nat} (hd : 0 < d)
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    (data : ModifiedFrequencyData delta) (K : ExponentialBoundsHD data.nu)
    {mu0 : Real} (P : BlockParameters hd delta hdelta data mu0)
    (budgets : BudgetConstants P)
    (EC : ExceptionalConstants hd delta hdelta data P)
    (CC : CorrectionConstants hd data K P budgets EC)
    (threshold : BlockThreshold CC) (j : Nat) (hlate : threshold.J ≤ j)
    (plans : CoordinatePlanFamily threshold j hlate)
    (coverage : CoordinatePlanCoverage plans)
    (origins : Fin d → IntVec d)
    (packing : LevelPacking plans origins)
    (u : {n : IntVec d // n ∈ dyadicBlock delta hdelta data.C0 j} → Complex)
    (hactive : (dyadicBlock delta hdelta data.C0 j).Nonempty) :
    LevelCorrectionResult hd data K P budgets EC CC threshold j hlate plans
      origins u hactive :=
  Classical.choice
    (levelCorrectionResult_nonempty hd data K P budgets EC CC threshold j hlate plans
      coverage origins packing u hactive)

/-- Summable normalized leakage into all future blocks. -/
theorem levelCorrection_futureLeakage {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    {data : ModifiedFrequencyData delta} {K : ExponentialBoundsHD data.nu}
    {mu0 : Real} {P : BlockParameters hd delta hdelta data mu0}
    {budgets : BudgetConstants P}
    {EC : ExceptionalConstants hd delta hdelta data P}
    {CC : CorrectionConstants hd data K P budgets EC}
    {threshold : BlockThreshold CC} {j : Nat} {hlate : threshold.J ≤ j}
    {plans : CoordinatePlanFamily threshold j hlate}
    {origins : Fin d → IntVec d}
    {u : {n : IntVec d // n ∈ dyadicBlock delta hdelta data.C0 j} → Complex}
    {hactive : (dyadicBlock delta hdelta data.C0 j).Nonempty}
    (correction : LevelCorrectionResult hd data K P budgets EC CC threshold j
      hlate plans origins u hactive) :
    Summable (fun k : Nat => if 4 * j < k then
      blockEnergyTerm P correction.carrierFn k else 0) ∧
    (∑' k : Nat, if 4 * j < k then
      blockEnergyTerm P correction.carrierFn k else 0) ≤
      (CC.leak * dyadicScale j) ^ 2 *
        ((1 / P.eta j) * ∑ n, ‖u n‖ ^ 2) := by
  classical
  let packages := correction.coordinateCorrection
  let f : Fin d → RealVec d → Complex := fun r =>
    coordinatePackageFn (packages r)
  let base : Fin d → RealVec d → Complex := fun r =>
    match packages r with
    | none => fun _ => 0
    | some q => q.correction.h
  let R : Fin d → RealVec d → Complex := fun r =>
    recenterAtIntegerVector (origins r) (base r)
  let sampleSq : Fin d → IntVec d → Real := fun r n =>
    ‖inverseSampleOn (unitCube d) (R r) (data.nu n)‖ ^ 2
  let totalSample : IntVec d → Real := fun n => ∑ r, sampleSq r n
  let shellSample : Nat → Real := fun k =>
    ∑ n ∈ dyadicBlock delta hdelta data.C0 k, totalSample n
  have hbase_meas (r : Fin d) : AEStronglyMeasurable (base r) volume := by
    unfold base packages
    cases hq : correction.coordinateCorrection r with
    | none =>
        simpa only [hq] using
          (aestronglyMeasurable_const :
            AEStronglyMeasurable (fun _ : RealVec d => (0 : Complex)) volume)
    | some q => simpa [hq] using (by
        rw [q.correction.h_eq]
        exact (q.cached.plan.thinCarrier.interpolate_stronglyMeasurable
          (origins r) (coordinateInterpolationValues q.cached.plan
            (coordinateResidual u r))).aestronglyMeasurable)
  have hbase_int (r : Fin d) : Integrable (base r) volume := by
    unfold base packages
    cases hq : correction.coordinateCorrection r with
    | none => simp
    | some q => simpa [hq] using (by
        rw [q.correction.h_eq]
        exact q.cached.plan.thinCarrier.interpolate_integrable
          (origins r) (coordinateInterpolationValues q.cached.plan
            (coordinateResidual u r)))
  have hbase_Lp (r : Fin d) : MemLp (base r) (2 : ENNReal) volume := by
    unfold base packages
    cases hq : correction.coordinateCorrection r with
    | none => simp
    | some q => simpa [hq] using (by
        rw [q.correction.h_eq]
        exact q.cached.plan.thinCarrier.interpolate_memLp
          (origins r) (coordinateInterpolationValues q.cached.plan
            (coordinateResidual u r)))
  have hRdata (r : Fin d) :
      AEStronglyMeasurable (R r) (volume.restrict (unitCube d)) ∧
      MemLp (R r) (2 : ENNReal) (volume.restrict (unitCube d)) ∧
      (∀ xi, inverseSample (base r) xi =
        fourierChar xi (integerEmbed (origins r)) *
          inverseSampleOn (unitCube d) (R r) xi) ∧
      sqNormOn (unitCube d) (R r) = sqNormOn Set.univ (base r) := by
    unfold base packages
    cases hq : correction.coordinateCorrection r with
    | none =>
        have hzeroMeas : AEStronglyMeasurable
            (fun _ : RealVec d => (0 : Complex)) volume :=
          aestronglyMeasurable_const
        have hzeroLp : MemLp (fun _ : RealVec d => (0 : Complex))
            (2 : ENNReal) volume := MemLp.zero'
        have hzeroSupp : AESupportedIn (fun _ : RealVec d => (0 : Complex))
            (integerEmbed (origins r) +ᵥ unitCube d) := by
          filter_upwards [] with x
          intro _hx
          rfl
        simpa [hq, R, base, packages] using
          (recenter_analysis_data (M := origins r) (F := fun _ : RealVec d => 0)
            (omega := unitCube d) (fun _ hx => hx) hzeroMeas hzeroLp hzeroSupp)
    | some q =>
        have hmeas : AEStronglyMeasurable q.correction.h volume := by
          rw [q.correction.h_eq]
          exact (q.cached.plan.thinCarrier.interpolate_stronglyMeasurable
            (origins r) (coordinateInterpolationValues q.cached.plan
              (coordinateResidual u r))).aestronglyMeasurable
        have hLp : MemLp q.correction.h (2 : ENNReal) volume := by
          rw [q.correction.h_eq]
          exact q.cached.plan.thinCarrier.interpolate_memLp
            (origins r) (coordinateInterpolationValues q.cached.plan
              (coordinateResidual u r))
        have hsupp : AESupportedIn q.correction.h
            (integerEmbed (origins r) +ᵥ q.cached.plan.thinCarrier.omega) := by
          rw [q.correction.h_eq]
          exact q.cached.plan.thinCarrier.interpolate_supported
            (origins r) (coordinateInterpolationValues q.cached.plan
              (coordinateResidual u r))
        simpa [hq, R, base, packages] using
          (recenter_analysis_data q.cached.plan.thinCarrier.omega_subset
            hmeas hLp hsupp)
  have hanalysis (r : Fin d) :=
    K.analysis_summable (R r) (hRdata r).1 (hRdata r).2.1
  have hsample_summable (r : Fin d) : Summable (sampleSq r) := by
    simpa [sampleSq] using (hanalysis r).1
  have hsample_tsum (r : Fin d) : ∑' n, sampleSq r n ≤
      K.upper * sqNormOn Set.univ (base r) := by
    calc
      ∑' n, sampleSq r n ≤ K.upper * sqNormOn (unitCube d) (R r) := by
        simpa [sampleSq] using (hanalysis r).2
      _ = K.upper * sqNormOn Set.univ (base r) := by rw [(hRdata r).2.2.2]
  have htotal_summable : Summable totalSample := by
    exact summable_sum (s := Finset.univ) fun r _ => hsample_summable r
  have htotal_tsum : ∑' n, totalSample n ≤
      ∑ r, K.upper * sqNormOn Set.univ (base r) := by
    rw [show (∑' n, totalSample n) = ∑ r, ∑' n, sampleSq r n by
      simpa [totalSample] using
        (Summable.tsum_finsetSum (s := Finset.univ)
          (fun r _ => hsample_summable r))]
    exact Finset.sum_le_sum fun r _ => hsample_tsum r
  have hsample_recenter (r : Fin d) (n : IntVec d) (hn : n ∉ data.C0) :
      ‖inverseSample (base r) (frequency delta n)‖ ^ 2 = sampleSq r n := by
    have hs := (hRdata r).2.2.1 (frequency delta n)
    rw [hs, norm_mul]
    have hchar : ‖fourierChar (frequency delta n) (integerEmbed (origins r))‖ = 1 := by
      simp [fourierChar, Complex.norm_exp]
    rw [hchar, one_mul]
    dsimp [sampleSq]
    rw [data.nu_outside n hn]
  have hcomponent_sample (r : Fin d) (n : IntVec d) :
      inverseSample (f r) (frequency delta n) =
        blockMultiplier data j r (frequency delta n) *
          inverseSample (base r) (frequency delta n) := by
    unfold f base packages
    cases hq : correction.coordinateCorrection r with
    | none => simp [coordinatePackageFn, inverseSample, inverseSampleOn]
    | some q =>
        simp only [coordinatePackageFn]
        rw [q.correction.carrierFn_eq,
          inverseSample_shiftPolynomialCarrier (by
            rw [q.correction.h_eq]
            exact q.cached.plan.thinCarrier.interpolate_integrable
              (origins r) (coordinateInterpolationValues q.cached.plan
                (coordinateResidual u r)))]
        rw [q.cached.plan.blockCoeffs_eq, q.cached.plan.shiftData.evaluation]
  have hfint (r : Fin d) : Integrable (f r) volume := by
    unfold f packages
    cases hq : correction.coordinateCorrection r with
    | none => simp [coordinatePackageFn]
    | some q => simpa [hq, coordinatePackageFn] using q.correction.carrierFn_integrable
  have hchar_meas (xi : RealVec d) :
      AEStronglyMeasurable (fun x => fourierChar xi x) volume := by
    apply Continuous.aestronglyMeasurable
    unfold fourierChar
    fun_prop
  have hchar_bound (xi : RealVec d) :
      ∀ᵐ x ∂volume, ‖fourierChar xi x‖ ≤ (1 : Real) := by
    filter_upwards [] with x
    simp [fourierChar, Complex.norm_exp]
  have hinverse_sum (xi : RealVec d) :
      inverseSample correction.carrierFn xi = ∑ r, inverseSample (f r) xi := by
    rw [correction.carrierFn_eq]
    change inverseSample (fun x => ∑ r, f r x) xi = _
    unfold inverseSample inverseSampleOn
    simp only [Measure.restrict_univ, Finset.sum_mul]
    rw [integral_finsetSum]
    intro r _
    exact (hfint r).mul_bdd (hchar_meas xi) (hchar_bound xi)
  have hcomponent_bound {k : Nat} (hjk : j ≤ k) (n : IntVec d)
      (hn : n ∈ dyadicBlock delta hdelta data.C0 k) (r : Fin d) :
      ‖inverseSample (f r) (frequency delta n)‖ ^ 2 ≤
        (4 * Real.pi * EC.upper *
          (2 : Real) ^ ((j : Int) - (k : Int))) ^ 2 * sampleSq r n := by
    have hsep_k : EC.jSep ≤ k :=
      (le_max_right 3 EC.jSep).trans (threshold.J_ge.trans hlate) |>.trans hjk
    have hexc := (EC.multiplier_bounds k n hsep_k hn).2
    have hdy := (blockMultiplier_bounds hd EC).2.2 j k r n hn hjk
    rw [hcomponent_sample, norm_mul, mul_pow, hsample_recenter r n
      (mem_dyadicBlock_iff.mp hn).1]
    have hblock : ‖blockMultiplier data j r (frequency delta n)‖ ≤
        4 * Real.pi * EC.upper * (2 : Real) ^ ((j : Int) - (k : Int)) := by
      rw [blockMultiplier, norm_mul]
      calc
        _ ≤ EC.upper * (4 * Real.pi * (2 : Real) ^ ((j : Int) - (k : Int))) :=
          mul_le_mul hexc hdy (norm_nonneg _) EC.upper_pos.le
        _ = _ := by ring
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) hblock 2) (sq_nonneg _)
  have hcarrier_sample_bound {k : Nat} (hjk : j ≤ k) (n : IntVec d)
      (hn : n ∈ dyadicBlock delta hdelta data.C0 k) :
      ‖inverseSample correction.carrierFn (frequency delta n)‖ ^ 2 ≤
        (d : Real) *
          (4 * Real.pi * EC.upper *
            (2 : Real) ^ ((j : Int) - (k : Int))) ^ 2 * totalSample n := by
    rw [hinverse_sum]
    have htri := norm_sum_le Finset.univ
      (fun r => inverseSample (f r) (frequency delta n))
    have hsqtri := pow_le_pow_left₀ (norm_nonneg _) htri 2
    have hcauchy := sq_sum_le_card_mul_sum_sq
      (s := Finset.univ) (f := fun r : Fin d =>
        ‖inverseSample (f r) (frequency delta n)‖)
    calc
      _ ≤ (∑ r : Fin d, ‖inverseSample (f r) (frequency delta n)‖) ^ 2 := hsqtri
      _ ≤ (d : Real) *
          ∑ r : Fin d, ‖inverseSample (f r) (frequency delta n)‖ ^ 2 := by
        simpa using hcauchy
      _ ≤ (d : Real) * ∑ r : Fin d,
          ((4 * Real.pi * EC.upper *
            (2 : Real) ^ ((j : Int) - (k : Int))) ^ 2 * sampleSq r n) :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun r _ => hcomponent_bound hjk n hn r)
          (by exact_mod_cast Nat.zero_le d)
      _ = _ := by
        simp only [totalSample, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _hr
        ring
  have hpow {k : Nat} (hfar : 4 * j < k) :
      (2 : Real) ^ k * ((2 : Real) ^ ((j : Int) - (k : Int))) ^ 2 ≤
        dyadicScale j ^ 2 := by
    have hexp : (2 * (j : Int) - (k : Int)) ≤ -(2 * (j : Int)) := by omega
    have hmono := zpow_le_zpow_right₀ (a := (2 : Real)) (by norm_num) hexp
    rw [dyadicScale]
    norm_num [← zpow_natCast, ← zpow_add₀, ← zpow_mul] at hmono ⊢
    have hleft : (k : Int) + ((j : Int) - (k : Int)) * 2 =
        2 * (j : Int) - (k : Int) := by ring
    have hright : (j : Int) * 2 = 2 * (j : Int) := by ring
    rw [hleft, hright]
    exact hmono
  let futureCoeff : Real :=
    16 * (d : Real) * Real.pi ^ 2 * EC.upper ^ 2 * budgets.Ceta
  let futureMajorant : Nat → Real := fun k =>
    futureCoeff * dyadicScale j ^ 2 * shellSample k
  have hfutureCoeff_nonneg : 0 ≤ futureCoeff := by
    have hd0 : 0 ≤ (d : Real) := by exact_mod_cast Nat.zero_le d
    dsimp [futureCoeff]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) hd0)
          (sq_nonneg Real.pi))
        (sq_nonneg EC.upper))
      budgets.Ceta_pos.le
  have hshellIndex_injective : Function.Injective
      (fun z : Σ k : Nat, {n : IntVec d //
        n ∈ dyadicBlock delta hdelta data.C0 k} => z.2.1) := by
    intro a b hab
    rcases a with ⟨k, n⟩
    rcases b with ⟨l, m⟩
    change n.1 = m.1 at hab
    have hkl : k = l := by
      by_contra hne
      have hdis := (coordinateBlocks_partition hd hdelta data.C0).2.2.1 k l hne
      exact Finset.disjoint_left.mp hdis n.property (hab ▸ m.property)
    subst l
    cases n with
    | mk nv hn =>
      cases m with
      | mk mv hm =>
        simp only at hab
        subst mv
        rfl
  have hsigma : Summable (fun z : Σ k : Nat,
      {n : IntVec d // n ∈ dyadicBlock delta hdelta data.C0 k} =>
      totalSample z.2.1) := by
    change Summable (totalSample ∘ fun z : Σ k : Nat,
      {n : IntVec d // n ∈ dyadicBlock delta hdelta data.C0 k} => z.2.1)
    exact htotal_summable.comp_injective hshellIndex_injective
  have hinner (k : Nat) :
      (∑' n : {n : IntVec d // n ∈ dyadicBlock delta hdelta data.C0 k},
        totalSample n.1) = shellSample k := by
    rw [tsum_fintype]
    change (∑ n : {n : IntVec d // n ∈ dyadicBlock delta hdelta data.C0 k},
      totalSample n.1) = _
    rw [show (∑ n : {n : IntVec d // n ∈ dyadicBlock delta hdelta data.C0 k},
        totalSample n.1) =
        ∑ n ∈ dyadicBlock delta hdelta data.C0 k, totalSample n by
      rw [← (dyadicBlock delta hdelta data.C0 k).sum_attach]
      simp]
  have hshell_summable : Summable shellSample := by
    have hs := hsigma.sigma
    apply hs.congr
    intro k
    exact hinner k
  have hshell_tsum_le : ∑' k, shellSample k ≤ ∑' n, totalSample n := by
    have hgroup : HasSum shellSample
        (∑' z : Σ k : Nat, {n : IntVec d //
          n ∈ dyadicBlock delta hdelta data.C0 k}, totalSample z.2.1) := by
      apply hsigma.hasSum.sigma
      intro k
      have hf : Summable (fun n : {n : IntVec d //
          n ∈ dyadicBlock delta hdelta data.C0 k} => totalSample n.1) :=
        Summable.of_finite
      have hfh := hf.hasSum
      rw [hinner k] at hfh
      exact hfh
    rw [hgroup.tsum_eq]
    exact hsigma.tsum_le_tsum_of_inj
      (fun z : Σ k : Nat, {n : IntVec d //
        n ∈ dyadicBlock delta hdelta data.C0 k} => z.2.1)
      hshellIndex_injective (fun n _ => by
        dsimp [totalSample, sampleSq]
        positivity) (fun z => le_rfl) htotal_summable
  have hfuture_le (k : Nat) :
      (if 4 * j < k then blockEnergyTerm P correction.carrierFn k else 0) ≤
        futureMajorant k := by
    by_cases hfar : 4 * j < k
    · rw [if_pos hfar]
      have hjk : j ≤ k := by omega
      have hk3 : 3 ≤ k := by
        have hj3 : 3 ≤ j :=
          (le_max_left 3 EC.jSep).trans (threshold.J_ge.trans hlate)
        omega
      rw [blockEnergyTerm, if_pos hk3]
      have hinveta := budgets.inv_eta_le_scale k hk3
      have hshell0 : 0 ≤ shellSample k := by
        dsimp [shellSample, totalSample, sampleSq]
        positivity
      calc
        (1 / P.eta k) *
            ∑ n ∈ dyadicBlock delta hdelta data.C0 k,
              ‖inverseSample correction.carrierFn (frequency delta n)‖ ^ 2 ≤
            (1 / P.eta k) *
              ∑ n ∈ dyadicBlock delta hdelta data.C0 k,
                ((d : Real) *
                  (4 * Real.pi * EC.upper *
                    (2 : Real) ^ ((j : Int) - (k : Int))) ^ 2 *
                    totalSample n) :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun n hn => hcarrier_sample_bound hjk n hn)
            (one_div_nonneg.mpr (budgets.eta_nonneg k))
        _ = (1 / P.eta k) * ((d : Real) *
            (4 * Real.pi * EC.upper *
              (2 : Real) ^ ((j : Int) - (k : Int))) ^ 2) * shellSample k := by
          simp only [shellSample, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro n _hn
          ring
        _ ≤ (budgets.Ceta * (2 : Real) ^ k) * ((d : Real) *
            (4 * Real.pi * EC.upper *
              (2 : Real) ^ ((j : Int) - (k : Int))) ^ 2) * shellSample k := by
          gcongr
        _ ≤ futureCoeff * dyadicScale j ^ 2 * shellSample k := by
          apply mul_le_mul_of_nonneg_right _ hshell0
          have hp := hpow hfar
          calc
            (budgets.Ceta * (2 : Real) ^ k) * ((d : Real) *
                (4 * Real.pi * EC.upper *
                  (2 : Real) ^ ((j : Int) - (k : Int))) ^ 2) =
                futureCoeff * ((2 : Real) ^ k *
                  ((2 : Real) ^ ((j : Int) - (k : Int))) ^ 2) := by
              dsimp [futureCoeff]
              ring
            _ ≤ futureCoeff * dyadicScale j ^ 2 :=
              mul_le_mul_of_nonneg_left hp hfutureCoeff_nonneg
    · rw [if_neg hfar]
      dsimp [futureMajorant]
      exact mul_nonneg
        (mul_nonneg hfutureCoeff_nonneg (sq_nonneg _))
        (by
          dsimp [shellSample, totalSample, sampleSq]
          exact Finset.sum_nonneg fun _ _ =>
            Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hfuture_nonneg (k : Nat) : 0 ≤
      (if 4 * j < k then blockEnergyTerm P correction.carrierFn k else 0) := by
    split_ifs with hk
    · rw [blockEnergyTerm]
      split_ifs with hk3
      · exact mul_nonneg
          (div_nonneg zero_le_one (P.eta_pos k hk3).le)
          (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      · rfl
    · rfl
  have hmajorant_summable : Summable futureMajorant :=
    hshell_summable.mul_left (futureCoeff * dyadicScale j ^ 2)
  have hfuture_summable : Summable (fun k : Nat => if 4 * j < k then
      blockEnergyTerm P correction.carrierFn k else 0) :=
    Summable.of_nonneg_of_le hfuture_nonneg hfuture_le hmajorant_summable
  have hbase_sum : ∑ r, sqNormOn Set.univ (base r) ≤
      CC.baseCost / P.eta j * ∑ n, ‖u n‖ ^ 2 := by
    have hcoord (r : Fin d) : sqNormOn Set.univ (base r) ≤
        CC.baseCost / P.eta j *
          ∑ n : {n : IntVec d // n ∈ coordinateBlock delta hdelta data.C0 hd j r},
            ‖coordinateResidual u r n‖ ^ 2 := by
      unfold base packages
      cases hq : correction.coordinateCorrection r with
      | none =>
          have heta : 0 < P.eta j := budgets.eta_pos j
            ((le_max_left 3 EC.jSep).trans (threshold.J_ge.trans hlate))
          have hnonneg : 0 ≤ CC.baseCost / P.eta j *
              ∑ n : {n : IntVec d //
                n ∈ coordinateBlock delta hdelta data.C0 hd j r},
                ‖coordinateResidual u r n‖ ^ 2 :=
            mul_nonneg (div_nonneg CC.baseCost_pos.le heta.le)
              (Finset.sum_nonneg fun _ _ => sq_nonneg _)
          simpa [hq, sqNormOn] using hnonneg
      | some q => simpa [hq] using
          coordinateCorrection_interpolant_energy q.correction
    have hpartition :
        (∑ r : Fin d,
          ∑ n : {n : IntVec d // n ∈ coordinateBlock delta hdelta data.C0 hd j r},
            ‖coordinateResidual u r n‖ ^ 2) = ∑ n, ‖u n‖ ^ 2 := by
      let e : IntVec d → Real := fun n =>
        if hn : n ∈ dyadicBlock delta hdelta data.C0 j then ‖u ⟨n, hn⟩‖ ^ 2 else 0
      calc
        _ = ∑ r : Fin d, ∑ n ∈ coordinateBlock delta hdelta data.C0 hd j r, e n := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [← (coordinateBlock delta hdelta data.C0 hd j r).sum_attach]
          apply Finset.sum_congr rfl
          intro n _hn
          have hnblock : n.1 ∈ dyadicBlock delta hdelta data.C0 j :=
            (mem_coordinateBlock_iff.mp n.property).choose
          change ‖u ⟨n.1, (mem_coordinateBlock_iff.mp n.property).choose⟩‖ ^ 2 = e n.1
          rw [show e n.1 = ‖u ⟨n.1, hnblock⟩‖ ^ 2 by
            simp only [e, dif_pos hnblock]]
        _ = ∑ n ∈ dyadicBlock delta hdelta data.C0 j, e n := by
          rw [← Finset.sum_biUnion]
          · rw [(coordinateBlocks_partition hd hdelta data.C0).2.1 j]
          · intro r _ q _ hrq
            exact (coordinateBlocks_partition hd hdelta data.C0).1 j
              (Set.mem_univ r) (Set.mem_univ q) hrq
        _ = ∑ n, ‖u n‖ ^ 2 := by
          rw [← (dyadicBlock delta hdelta data.C0 j).sum_attach]
          apply Finset.sum_congr rfl
          intro n _hn
          simp only [e, dif_pos n.property]
    calc
      _ ≤ ∑ r : Fin d, (CC.baseCost / P.eta j *
          ∑ n : {n : IntVec d // n ∈ coordinateBlock delta hdelta data.C0 hd j r},
            ‖coordinateResidual u r n‖ ^ 2) :=
        Finset.sum_le_sum fun r _ => hcoord r
      _ = CC.baseCost / P.eta j *
          (∑ r : Fin d,
            ∑ n : {n : IntVec d // n ∈ coordinateBlock delta hdelta data.C0 hd j r},
              ‖coordinateResidual u r n‖ ^ 2) := by rw [Finset.mul_sum]
      _ = _ := by rw [hpartition]
  have heta_pos : 0 < P.eta j := budgets.eta_pos j
    ((le_max_left 3 EC.jSep).trans (threshold.J_ge.trans hlate))
  have hfuture_tsum : (∑' k : Nat, if 4 * j < k then
      blockEnergyTerm P correction.carrierFn k else 0) ≤
      (CC.leak * dyadicScale j) ^ 2 *
        ((1 / P.eta j) * ∑ n, ‖u n‖ ^ 2) := by
    have hcoeff0 : 0 ≤ futureCoeff * dyadicScale j ^ 2 := by
      exact mul_nonneg hfutureCoeff_nonneg (sq_nonneg _)
    calc
      _ ≤ ∑' k, futureMajorant k :=
        Summable.tsum_le_tsum hfuture_le hfuture_summable hmajorant_summable
      _ = (futureCoeff * dyadicScale j ^ 2) * ∑' k, shellSample k := by
        rw [tsum_mul_left]
      _ ≤ (futureCoeff * dyadicScale j ^ 2) * ∑' n, totalSample n :=
        mul_le_mul_of_nonneg_left hshell_tsum_le hcoeff0
      _ ≤ (futureCoeff * dyadicScale j ^ 2) *
          (∑ r, K.upper * sqNormOn Set.univ (base r)) :=
        mul_le_mul_of_nonneg_left htotal_tsum hcoeff0
      _ = (futureCoeff * dyadicScale j ^ 2) *
          (K.upper * ∑ r, sqNormOn Set.univ (base r)) := by
        congr 1
        rw [Finset.mul_sum]
      _ ≤ (futureCoeff * dyadicScale j ^ 2) *
          (K.upper * (CC.baseCost / P.eta j * ∑ n, ‖u n‖ ^ 2)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hbase_sum K.upper_pos.le) hcoeff0
      _ ≤ CC.future * dyadicScale j ^ 2 *
          ((1 / P.eta j) * ∑ n, ‖u n‖ ^ 2) := by
        have hrest : 0 ≤ dyadicScale j ^ 2 *
            ((1 / P.eta j) * ∑ n, ‖u n‖ ^ 2) := by
          exact mul_nonneg (sq_nonneg _)
            (mul_nonneg (one_div_nonneg.mpr heta_pos.le)
              (Finset.sum_nonneg fun _ _ => sq_nonneg _))
        have hconst0 : 0 ≤ futureCoeff * K.upper * CC.baseCost := by
          exact mul_nonneg
            (mul_nonneg hfutureCoeff_nonneg K.upper_pos.le)
            CC.baseCost_pos.le
        have hconst_eq : CC.future =
            20 * (futureCoeff * K.upper * CC.baseCost) := by
          rw [CC.future_eq, CC.cost_eq]
          dsimp [futureCoeff]
          ring
        have hconst : futureCoeff * K.upper * CC.baseCost ≤ CC.future := by
          rw [hconst_eq]
          nlinarith
        calc
          (futureCoeff * dyadicScale j ^ 2) *
              (K.upper * (CC.baseCost / P.eta j * ∑ n, ‖u n‖ ^ 2)) =
              (futureCoeff * K.upper * CC.baseCost) *
                (dyadicScale j ^ 2 *
                  ((1 / P.eta j) * ∑ n, ‖u n‖ ^ 2)) := by ring
          _ ≤ CC.future * (dyadicScale j ^ 2 *
                ((1 / P.eta j) * ∑ n, ‖u n‖ ^ 2)) :=
            mul_le_mul_of_nonneg_right hconst hrest
          _ = CC.future * dyadicScale j ^ 2 *
                ((1 / P.eta j) * ∑ n, ‖u n‖ ^ 2) := by ring
      _ ≤ CC.leak ^ 2 * dyadicScale j ^ 2 *
          ((1 / P.eta j) * ∑ n, ‖u n‖ ^ 2) := by
        gcongr
        exact CC.future_le_leak_sq
      _ = (CC.leak * dyadicScale j) ^ 2 *
          ((1 / P.eta j) * ∑ n, ‖u n‖ ^ 2) := by ring
  exact ⟨hfuture_summable, hfuture_tsum⟩

end Internal

end AsymptoticallyIntegerHD
