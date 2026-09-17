import AsymptoticallyIntegerHD.ThinInterpolation
import AsymptoticallyIntegerHD.DyadicBlocks
import AsymptoticallyIntegerHD.BlockMultipliers
import AsymptoticallyIntegerHD.FrequencyCarriers
import AsymptoticallyIntegerHD.BlockCorrection
import AsymptoticallyIntegerHD.Seed
import AsymptoticallyIntegerHD.ForwardRecursion

/-! # Cached plans, origins, and correction recursion

The context owns all non-residual choices, while finite stages own the
recursive construction.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Pointwise

namespace AsymptoticallyIntegerHD

namespace Internal

/-- A cached plan and its proof-irrelevant activity data. -/
structure PlannedCoordinateBlock {d : Nat} (hd : 0 < d)
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    (data : ModifiedFrequencyData delta) (K : ExponentialBoundsHD data.nu)
    {mu0 : Real} (P : BlockParameters hd delta hdelta data mu0)
    (budgets : BudgetConstants P)
    (EC : ExceptionalConstants hd delta hdelta data P)
    (CC : CorrectionConstants hd data K P budgets EC)
    (threshold : BlockThreshold CC) (j : Nat) (r : Fin d) where
  active : (coordinateBlock delta hdelta data.C0 hd j r).Nonempty
  late : threshold.J ≤ j
  plan : BlockPlan hd data K P budgets EC CC threshold j r active late

/-- Every choice fixed before the residual recursion. -/
structure ConstructionContext (d : Nat) (hd : 0 < d)
    (delta : IntVec d → RealVec d) (hdelta : TendsToZeroAtIntVecInfinity delta)
    (mu0 : Real) (hmu0 : 0 < mu0) (hmu01 : mu0 < 1) where
  data : ModifiedFrequencyData delta
  K : ExponentialBoundsHD data.nu
  blocks : BlockParameters hd delta hdelta data mu0
  budgets : BudgetConstants blocks
  exceptionalConstants : ExceptionalConstants hd delta hdelta data blocks
  correctionConstants :
    CorrectionConstants hd data K blocks budgets exceptionalConstants
  threshold : BlockThreshold correctionConstants
  plan : (s : Nat) → (r : Fin d) → Option
    (PlannedCoordinateBlock hd data K blocks budgets exceptionalConstants
      correctionConstants threshold (threshold.J + s) r)
  plan_none_iff : ∀ s r, plan s r = none ↔
    ¬(coordinateBlock delta hdelta data.C0 hd (threshold.J + s) r).Nonempty
  plan_canonical : ∀ s r p, plan s r = some p →
    p.plan = blockPlan hd data K blocks budgets exceptionalConstants
      correctionConstants threshold (threshold.J + s) r p.active p.late
  seed : SeedData hd blocks threshold
  seedWitness : SeedWitnessData hd seed

/-- Existence certificate for the globally coherent collection of choices. -/
theorem constructionContext_nonempty (d : Nat) (hd : 0 < d)
    (delta : IntVec d → RealVec d) (hdelta : TendsToZeroAtIntVecInfinity delta)
    (mu0 : Real) (hmu0 : 0 < mu0) (hmu01 : mu0 < 1) :
    Nonempty (ConstructionContext d hd delta hdelta mu0 hmu0 hmu01) := by
  classical
  let data := modifiedFrequencyData hd delta hdelta
  let K := modifiedExponentialBounds hd data
  let blocks := blockParameters hd delta hdelta data mu0 hmu0 hmu01
  let budgets := budgetConstants blocks
  let exceptionalConstants := exceptionalConstants hd delta hdelta data blocks
  let correctionConstants := correctionConstants hd data K blocks budgets
    exceptionalConstants
  let threshold := blockThreshold correctionConstants
  let plan : (s : Nat) → (r : Fin d) → Option
      (PlannedCoordinateBlock hd data K blocks budgets exceptionalConstants
        correctionConstants threshold (threshold.J + s) r) := fun s r ↦
    if hactive : (coordinateBlock delta hdelta data.C0 hd
        (threshold.J + s) r).Nonempty then
      some
        { active := hactive
          late := by omega
          plan := blockPlan hd data K blocks budgets exceptionalConstants
            correctionConstants threshold (threshold.J + s) r hactive (by omega) }
    else none
  let seed := seedData hd blocks threshold
  let seedWitness := seedWitnessData hd seed
  refine ⟨
    { data := data
      K := K
      blocks := blocks
      budgets := budgets
      exceptionalConstants := exceptionalConstants
      correctionConstants := correctionConstants
      threshold := threshold
      plan := plan
      plan_none_iff := ?_
      plan_canonical := ?_
      seed := seed
      seedWitness := seedWitness }⟩
  · intro s r
    dsimp [plan]
    split_ifs with hactive <;> simp [hactive]
  · intro s r p hp
    dsimp [plan] at hp
    split at hp
    next hactive =>
      have hpeq : p =
          { active := hactive
            late := by omega
            plan := blockPlan hd data K blocks budgets exceptionalConstants
              correctionConstants threshold (threshold.J + s) r hactive
                (by omega) } := Option.some.inj hp.symm
      subst p
      rfl
    next hinactive => simp at hp

/-- Sole global noncomputable construction point. -/
noncomputable def constructionContext (d : Nat) (hd : 0 < d)
    (delta : IntVec d → RealVec d) (hdelta : TendsToZeroAtIntVecInfinity delta)
    (mu0 : Real) (hmu0 : 0 < mu0) (hmu01 : mu0 < 1) :
    ConstructionContext d hd delta hdelta mu0 hmu0 hmu01 :=
  Classical.choice
    (constructionContext_nonempty d hd delta hdelta mu0 hmu0 hmu01)

/-- Pre-residual base envelope of a slot. -/
def baseEnvelope {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    {mu0 : Real} {hmu0 : 0 < mu0} {hmu01 : mu0 < 1}
    (ctx : ConstructionContext d hd delta hdelta mu0 hmu0 hmu01)
    (s : Nat) (r : Fin d) (M : IntVec d) : Set (RealVec d) :=
  match ctx.plan s r with
  | none => ∅
  | some p => coordinateBaseEnvelope p.plan M

/-- Pre-residual difference envelope of a slot. -/
def differenceEnvelope {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    {mu0 : Real} {hmu0 : 0 < mu0} {hmu01 : mu0 < 1}
    (ctx : ConstructionContext d hd delta hdelta mu0 hmu0 hmu01)
    (s : Nat) (r : Fin d) (M : IntVec d) : Set (RealVec d) :=
  match ctx.plan s r with
  | none => ∅
  | some p => coordinateDifferenceEnvelope p.plan M

/-- Width, including a strict gap, reserved for one lexicographic slot. -/
def slotSpan {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    {mu0 : Real} {hmu0 : 0 < mu0} {hmu01 : mu0 < 1}
    (ctx : ConstructionContext d hd delta hdelta mu0 hmu0 hmu01)
    (s : Nat) (r : Fin d) : Nat :=
  match ctx.plan s r with
  | none => 1
  | some p => p.plan.shiftData.differenceEnvelopeWidth + 1

/-- Total span of all slots preceding `(s,r)` in level-first order. -/
def precedingSpan {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    {mu0 : Real} {hmu0 : 0 < mu0} {hmu01 : mu0 < 1}
    (ctx : ConstructionContext d hd delta hdelta mu0 hmu0 hmu01)
    (s : Nat) (r : Fin d) : Nat :=
  (Finset.range s).sum (fun t => ∑ q : Fin d, slotSpan ctx t q) +
    (Finset.univ.filter fun q : Fin d => q.val < r.val).sum
      (fun q => slotSpan ctx s q)

/-- Lexicographically packed integer-vector origins. -/
noncomputable def carrierOrigin {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    {mu0 : Real} {hmu0 : 0 < mu0} {hmu01 : mu0 < 1}
    (ctx : ConstructionContext d hd delta hdelta mu0 hmu0 hmu01)
    (s : Nat) (r : Fin d) : IntVec d :=
  fun i => if i = firstCoordinate hd then
    ((2 + precedingSpan ctx s r : Nat) : Int) else 0

/-- Pairwise packing and seed avoidance, chosen pre-recursion. -/
theorem carrierOrigin_envelopes {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    {mu0 : Real} {hmu0 : 0 < mu0} {hmu01 : mu0 < 1}
    (ctx : ConstructionContext d hd delta hdelta mu0 hmu0 hmu01) :
    Set.Pairwise (Set.univ : Set (Nat × Fin d)) (fun a b =>
      Disjoint (baseEnvelope ctx a.1 a.2 (carrierOrigin ctx a.1 a.2))
        (baseEnvelope ctx b.1 b.2 (carrierOrigin ctx b.1 b.2))) ∧
    Set.Pairwise (Set.univ : Set (Nat × Fin d)) (fun a b =>
      Disjoint (differenceEnvelope ctx a.1 a.2 (carrierOrigin ctx a.1 a.2))
        (differenceEnvelope ctx b.1 b.2 (carrierOrigin ctx b.1 b.2))) ∧
    (∀ s r, Disjoint
      (baseEnvelope ctx s r (carrierOrigin ctx s r)) ctx.seed.A0) ∧
    (∀ s r, Disjoint
      (differenceEnvelope ctx s r (carrierOrigin ctx s r)) ctx.seedWitness.S0) := by
  classical
  have hcoordStep (s : Nat) {r q : Fin d} (hrq : r.val < q.val) :
      (Finset.univ.filter fun i : Fin d ↦ i.val < r.val).sum
          (fun i ↦ slotSpan ctx s i) + slotSpan ctx s r ≤
        (Finset.univ.filter fun i : Fin d ↦ i.val < q.val).sum
          (fun i ↦ slotSpan ctx s i) := by
    let A := Finset.univ.filter fun i : Fin d ↦ i.val < r.val
    let B := Finset.univ.filter fun i : Fin d ↦ i.val < q.val
    have hrA : r ∉ A := by simp [A]
    have hsub : insert r A ⊆ B := by
      intro i hi
      have hi' : i = r ∨ i.val < r.val := by simpa [A] using hi
      rcases hi' with rfl | hi
      · simpa [B] using hrq
      · simp [B]
        omega
    calc
      A.sum (fun i ↦ slotSpan ctx s i) + slotSpan ctx s r =
          (insert r A).sum (fun i ↦ slotSpan ctx s i) := by
        rw [Finset.sum_insert hrA]
        omega
      _ ≤ B.sum (fun i ↦ slotSpan ctx s i) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun i hi hnot ↦ Nat.zero_le _)
  have hcoordAll (s : Nat) (r : Fin d) :
      (Finset.univ.filter fun i : Fin d ↦ i.val < r.val).sum
          (fun i ↦ slotSpan ctx s i) + slotSpan ctx s r ≤
        ∑ i : Fin d, slotSpan ctx s i := by
    let A := Finset.univ.filter fun i : Fin d ↦ i.val < r.val
    have hrA : r ∉ A := by simp [A]
    have hsub : insert r A ⊆ (Finset.univ : Finset (Fin d)) := by simp
    calc
      A.sum (fun i ↦ slotSpan ctx s i) + slotSpan ctx s r =
          (insert r A).sum (fun i ↦ slotSpan ctx s i) := by
        rw [Finset.sum_insert hrA]
        omega
      _ ≤ ∑ i : Fin d, slotSpan ctx s i :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun i hi hnot ↦ Nat.zero_le _)
  have hpreceding {a b : Nat × Fin d}
      (hab : a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2.val < b.2.val)) :
      precedingSpan ctx a.1 a.2 + slotSpan ctx a.1 a.2 ≤
        precedingSpan ctx b.1 b.2 := by
    rcases a with ⟨sa, ra⟩
    rcases b with ⟨sb, rb⟩
    simp only at hab ⊢
    rcases hab with hab | ⟨hs, hr⟩
    · have hlevels :
          (Finset.range (sa + 1)).sum
              (fun t ↦ ∑ i : Fin d, slotSpan ctx t i) ≤
            (Finset.range sb).sum
              (fun t ↦ ∑ i : Fin d, slotSpan ctx t i) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono (Nat.succ_le_iff.mpr hab))
          (fun i hi hnot ↦ Nat.zero_le _)
      rw [Finset.sum_range_succ] at hlevels
      have hc := hcoordAll sa ra
      unfold precedingSpan
      omega
    · subst sb
      have hc := hcoordStep sa hr
      unfold precedingSpan
      omega
  have hlex {a b : Nat × Fin d} (hab : a ≠ b) :
      (a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2.val < b.2.val)) ∨
      (b.1 < a.1 ∨ (b.1 = a.1 ∧ b.2.val < a.2.val)) := by
    by_cases hs : a.1 = b.1
    · have hrv : a.2.val ≠ b.2.val := by
        intro hv
        apply hab
        apply Prod.ext hs
        exact Fin.ext hv
      rcases lt_or_gt_of_ne hrv with h | h
      · exact Or.inl (Or.inr ⟨hs, h⟩)
      · exact Or.inr (Or.inr ⟨hs.symm, h⟩)
    · rcases lt_or_gt_of_ne hs with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl h)
  have hslabDisjoint {a b : Nat × Fin d} (hab : a ≠ b)
      {wa wb : Nat} (hwa : wa < slotSpan ctx a.1 a.2)
      (hwb : wb < slotSpan ctx b.1 b.2) :
      Disjoint
        {x : RealVec d |
          (carrierOrigin ctx a.1 a.2 (firstCoordinate hd) : Real) ≤
            x (firstCoordinate hd) ∧
          x (firstCoordinate hd) ≤
            (carrierOrigin ctx a.1 a.2 (firstCoordinate hd) : Real) + wa}
        {x : RealVec d |
          (carrierOrigin ctx b.1 b.2 (firstCoordinate hd) : Real) ≤
            x (firstCoordinate hd) ∧
          x (firstCoordinate hd) ≤
            (carrierOrigin ctx b.1 b.2 (firstCoordinate hd) : Real) + wb} := by
    rw [Set.disjoint_left]
    intro x hxa hxb
    rcases hlex hab with hbefore | hafter
    · have hp := hpreceding hbefore
      have hsepI : carrierOrigin ctx a.1 a.2 (firstCoordinate hd) + (wa : Int) <
          carrierOrigin ctx b.1 b.2 (firstCoordinate hd) := by
        simp only [carrierOrigin, if_pos]
        omega
      have hsepR :
          (carrierOrigin ctx a.1 a.2 (firstCoordinate hd) : Real) + wa <
            (carrierOrigin ctx b.1 b.2 (firstCoordinate hd) : Real) := by
        exact_mod_cast hsepI
      linarith [hxa.2, hxb.1]
    · have hp := hpreceding hafter
      have hsepI : carrierOrigin ctx b.1 b.2 (firstCoordinate hd) + (wb : Int) <
          carrierOrigin ctx a.1 a.2 (firstCoordinate hd) := by
        simp only [carrierOrigin, if_pos]
        omega
      have hsepR :
          (carrierOrigin ctx b.1 b.2 (firstCoordinate hd) : Real) + wb <
            (carrierOrigin ctx a.1 a.2 (firstCoordinate hd) : Real) := by
        exact_mod_cast hsepI
      linarith [hxb.2, hxa.1]
  have hbase : Set.Pairwise (Set.univ : Set (Nat × Fin d)) (fun a b ↦
      Disjoint (baseEnvelope ctx a.1 a.2 (carrierOrigin ctx a.1 a.2))
        (baseEnvelope ctx b.1 b.2 (carrierOrigin ctx b.1 b.2))) := by
    intro a ha b hb hab
    cases hpa : ctx.plan a.1 a.2 with
    | none => simp [baseEnvelope, hpa]
    | some pa =>
      cases hpb : ctx.plan b.1 b.2 with
      | none => simp [baseEnvelope, hpb]
      | some pb =>
        have hwa : pa.plan.shiftData.baseEnvelopeWidth <
            slotSpan ctx a.1 a.2 := by
          simp [slotSpan, hpa, pa.plan.shiftData.differenceEnvelopeWidth_eq]
        have hwb : pb.plan.shiftData.baseEnvelopeWidth <
            slotSpan ctx b.1 b.2 := by
          simp [slotSpan, hpb, pb.plan.shiftData.differenceEnvelopeWidth_eq]
        simpa [baseEnvelope, hpa, hpb, coordinateBaseEnvelope] using
          (hslabDisjoint hab hwa hwb)
  have hdifference : Set.Pairwise (Set.univ : Set (Nat × Fin d)) (fun a b ↦
      Disjoint (differenceEnvelope ctx a.1 a.2 (carrierOrigin ctx a.1 a.2))
        (differenceEnvelope ctx b.1 b.2 (carrierOrigin ctx b.1 b.2))) := by
    intro a ha b hb hab
    cases hpa : ctx.plan a.1 a.2 with
    | none => simp [differenceEnvelope, hpa]
    | some pa =>
      cases hpb : ctx.plan b.1 b.2 with
      | none => simp [differenceEnvelope, hpb]
      | some pb =>
        have hwa : pa.plan.shiftData.differenceEnvelopeWidth <
            slotSpan ctx a.1 a.2 := by simp [slotSpan, hpa]
        have hwb : pb.plan.shiftData.differenceEnvelopeWidth <
            slotSpan ctx b.1 b.2 := by simp [slotSpan, hpb]
        simpa [differenceEnvelope, hpa, hpb, coordinateDifferenceEnvelope] using
          (hslabDisjoint hab hwa hwb)
  refine ⟨hbase, hdifference, ?_, ?_⟩
  · intro s r
    cases hp : ctx.plan s r with
    | none => simp [baseEnvelope, hp]
    | some p =>
      rw [Set.disjoint_left]
      intro x hxenv hxseed
      simp only [baseEnvelope, hp] at hxenv
      have hlow := hxenv.1
      change (carrierOrigin ctx s r (firstCoordinate hd) : Real) ≤
        x (firstCoordinate hd) at hlow
      have horiginI : (2 : Int) ≤
          carrierOrigin ctx s r (firstCoordinate hd) := by
        simp [carrierOrigin]
      have horiginR : (2 : Real) ≤
          (carrierOrigin ctx s r (firstCoordinate hd) : Real) := by
        exact_mod_cast horiginI
      have hseed := (ctx.seed.A0_subset hxseed).2
      nlinarith
  · intro s r
    cases hp : ctx.plan s r with
    | none => simp [differenceEnvelope, hp]
    | some p =>
      rw [Set.disjoint_left]
      intro x hxenv hxseed
      simp only [differenceEnvelope, hp] at hxenv
      have hlow := hxenv.1
      change (carrierOrigin ctx s r (firstCoordinate hd) : Real) ≤
        x (firstCoordinate hd) at hlow
      have horiginI : (2 : Int) ≤
          carrierOrigin ctx s r (firstCoordinate hd) := by
        simp [carrierOrigin]
      have horiginR : (2 : Real) ≤
          (carrierOrigin ctx s r (firstCoordinate hd) : Real) := by
        exact_mod_cast horiginI
      have hseed := (ctx.seedWitness.S0_subset hxseed).2
      nlinarith

/-- Residual coordinates on the actual level `J+s`. -/
abbrev BlockVector {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    {mu0 : Real} {hmu0 : 0 < mu0} {hmu01 : mu0 < 1}
    (ctx : ConstructionContext d hd delta hdelta mu0 hmu0 hmu01) (s : Nat) :=
  {n : IntVec d // n ∈ dyadicBlock delta hdelta ctx.data.C0
    (ctx.threshold.J + s)} → Complex

/-- Standard proof that the offset level lies beyond the final threshold. -/
def recursionLate {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    {mu0 : Real} {hmu0 : 0 < mu0} {hmu01 : mu0 < 1}
    (ctx : ConstructionContext d hd delta hdelta mu0 hmu0 hmu01) (s : Nat) :
    ctx.threshold.J ≤ ctx.threshold.J + s := Nat.le_add_right _ _

/-- Repackage cached context plans with one uniform late proof. -/
noncomputable def cachedPlanFamily {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    {mu0 : Real} {hmu0 : 0 < mu0} {hmu01 : mu0 < 1}
    (ctx : ConstructionContext d hd delta hdelta mu0 hmu0 hmu01) (s : Nat) :
    CoordinatePlanFamily ctx.threshold (ctx.threshold.J + s)
      (recursionLate ctx s) :=
  fun r =>
    match ctx.plan s r with
    | none => none
    | some p => some
        { active := p.active
          plan := blockPlan hd ctx.data ctx.K ctx.blocks ctx.budgets
            ctx.exceptionalConstants ctx.correctionConstants ctx.threshold
            (ctx.threshold.J + s) r p.active (recursionLate ctx s) }

/-- Cached recursion plans cover exactly the active pieces. -/
theorem cachedPlanFamily_coverage {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    {mu0 : Real} {hmu0 : 0 < mu0} {hmu01 : mu0 < 1}
    (ctx : ConstructionContext d hd delta hdelta mu0 hmu0 hmu01) (s : Nat) :
    CoordinatePlanCoverage (cachedPlanFamily ctx s) := by
  constructor
  intro r
  cases hplan : ctx.plan s r with
  | none =>
      have hempty := (ctx.plan_none_iff s r).mp hplan
      simp [cachedPlanFamily, hplan, hempty]
  | some p =>
      simp [cachedPlanFamily, hplan, p.active]

/-- The global lexicographic packing specializes to one recursive level. -/
theorem carrierOrigin_levelPacking {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    {mu0 : Real} {hmu0 : 0 < mu0} {hmu01 : mu0 < 1}
    (ctx : ConstructionContext d hd delta hdelta mu0 hmu0 hmu01) (s : Nat) :
    LevelPacking (cachedPlanFamily ctx s) (fun r => carrierOrigin ctx s r) := by
  classical
  have henv := carrierOrigin_envelopes ctx
  constructor
  · intro r hr q hq hrq
    have hpairs := henv.1 (Set.mem_univ (s, r)) (Set.mem_univ (s, q))
      (by intro h; exact hrq (congrArg Prod.snd h))
    cases hpr : ctx.plan s r with
    | none => simp [levelBaseEnvelope, cachedPlanFamily, hpr]
    | some pr =>
      cases hpq : ctx.plan s q with
      | none => simp [levelBaseEnvelope, cachedPlanFamily, hpq]
      | some pq =>
        have hcr := ctx.plan_canonical s r pr hpr
        have hcq := ctx.plan_canonical s q pq hpq
        simpa [levelBaseEnvelope, cachedPlanFamily, baseEnvelope, hpr, hpq,
          hcr, hcq] using hpairs
  · intro r hr q hq hrq
    have hpairs := henv.2.1 (Set.mem_univ (s, r)) (Set.mem_univ (s, q))
      (by intro h; exact hrq (congrArg Prod.snd h))
    cases hpr : ctx.plan s r with
    | none => simp [levelDifferenceEnvelope, cachedPlanFamily, hpr]
    | some pr =>
      cases hpq : ctx.plan s q with
      | none => simp [levelDifferenceEnvelope, cachedPlanFamily, hpq]
      | some pq =>
        have hcr := ctx.plan_canonical s r pr hpr
        have hcq := ctx.plan_canonical s q pq hpq
        simpa [levelDifferenceEnvelope, cachedPlanFamily, differenceEnvelope,
          hpr, hpq, hcr, hcq] using hpairs

/-- Total active/inactive correction at one offset. -/
structure LevelCorrection {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    {mu0 : Real} {hmu0 : 0 < mu0} {hmu01 : mu0 < 1}
    (ctx : ConstructionContext d hd delta hdelta mu0 hmu0 hmu01)
    (s : Nat) (u : BlockVector ctx s) where
  carrierFn : RealVec d → Complex
  differenceFn : RealVec d → Complex
  carrierSet : Set (RealVec d)
  differenceCarrierSet : Set (RealVec d)
  differenceFn_eq : differenceFn = firstCoordinateDifference hd carrierFn
  inactive : ¬(dyadicBlock delta hdelta ctx.data.C0
      (ctx.threshold.J + s)).Nonempty →
    carrierFn = 0 ∧ differenceFn = 0 ∧ carrierSet = ∅ ∧ differenceCarrierSet = ∅
  activeResult : ∀ hactive : (dyadicBlock delta hdelta ctx.data.C0
      (ctx.threshold.J + s)).Nonempty,
    LevelCorrectionResult hd ctx.data ctx.K ctx.blocks ctx.budgets
      ctx.exceptionalConstants ctx.correctionConstants ctx.threshold
      (ctx.threshold.J + s) (recursionLate ctx s) (cachedPlanFamily ctx s)
      (fun r => carrierOrigin ctx s r) u hactive
  carrierFn_active : ∀ hactive,
    carrierFn = (activeResult hactive).carrierFn
  differenceFn_active : ∀ hactive,
    differenceFn = (activeResult hactive).differenceFn
  carrierSet_active : ∀ hactive,
    carrierSet = (activeResult hactive).carrierSet
  differenceCarrierSet_active : ∀ hactive,
    differenceCarrierSet = (activeResult hactive).differenceCarrierSet

/-- Build a level correction from cached plans and origins. -/
noncomputable def buildLevelCorrectionAt {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    {mu0 : Real} {hmu0 : 0 < mu0} {hmu01 : mu0 < 1}
    (ctx : ConstructionContext d hd delta hdelta mu0 hmu0 hmu01)
    (s : Nat) (u : BlockVector ctx s) : LevelCorrection ctx s u := by
  classical
  by_cases hactive : (dyadicBlock delta hdelta ctx.data.C0
      (ctx.threshold.J + s)).Nonempty
  · let result := buildLevelCorrection hd ctx.data ctx.K ctx.blocks ctx.budgets
      ctx.exceptionalConstants ctx.correctionConstants ctx.threshold
      (ctx.threshold.J + s) (recursionLate ctx s) (cachedPlanFamily ctx s)
      (cachedPlanFamily_coverage ctx s) (fun r => carrierOrigin ctx s r)
      (carrierOrigin_levelPacking ctx s) u hactive
    exact
      { carrierFn := result.carrierFn
        differenceFn := result.differenceFn
        carrierSet := result.carrierSet
        differenceCarrierSet := result.differenceCarrierSet
        differenceFn_eq := result.differenceFn_eq
        inactive := fun hinactive => False.elim (hinactive hactive)
        activeResult := fun hactive' => by
          have hh : hactive' = hactive := Subsingleton.elim _ _
          subst hactive'
          exact result
        carrierFn_active := fun hactive' => by
          have hh : hactive' = hactive := Subsingleton.elim _ _
          subst hactive'
          rfl
        differenceFn_active := fun hactive' => by
          have hh : hactive' = hactive := Subsingleton.elim _ _
          subst hactive'
          rfl
        carrierSet_active := fun hactive' => by
          have hh : hactive' = hactive := Subsingleton.elim _ _
          subst hactive'
          rfl
        differenceCarrierSet_active := fun hactive' => by
          have hh : hactive' = hactive := Subsingleton.elim _ _
          subst hactive'
          rfl }
  · exact
      { carrierFn := 0
        differenceFn := 0
        carrierSet := ∅
        differenceCarrierSet := ∅
        differenceFn_eq := by
          funext x
          simp [firstCoordinateDifference, vectorTranslate]
        inactive := fun _ => ⟨rfl, rfl, rfl, rfl⟩
        activeResult := fun h => False.elim (hactive h)
        carrierFn_active := fun h => False.elim (hactive h)
        differenceFn_active := fun h => False.elim (hactive h)
        carrierSet_active := fun h => False.elim (hactive h)
        differenceCarrierSet_active := fun h => False.elim (hactive h) }

/-- Exact finite prefix of the residual recursion. -/
structure CorrectionStage {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    {mu0 : Real} {hmu0 : 0 < mu0} {hmu01 : mu0 < 1}
    (ctx : ConstructionContext d hd delta hdelta mu0 hmu0 hmu01)
    (N : Nat) where
  residual : (s : Fin N) → BlockVector ctx s.1
  correction : (s : Fin N) → LevelCorrection ctx s.1 (residual s)
  residual_eq : ∀ s n,
    residual s n = inverseSample ctx.seed.G0 (frequency delta n.1) +
      Finset.univ.sum (fun i : Fin s.1 =>
        inverseSample (correction ⟨i.1, Nat.lt_trans i.2 s.2⟩).carrierFn
          (frequency delta n.1))

/-- Empty finite stage. -/
def emptyCorrectionStage {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    {mu0 : Real} {hmu0 : 0 < mu0} {hmu01 : mu0 < 1}
    (ctx : ConstructionContext d hd delta hdelta mu0 hmu0 hmu01) :
    CorrectionStage ctx 0 where
  residual := fun s => Fin.elim0 s
  correction := fun s => Fin.elim0 s
  residual_eq := fun s => Fin.elim0 s

/-- An extension together with all observable prefix facts. -/
structure StageExtension {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    {mu0 : Real} {hmu0 : 0 < mu0} {hmu01 : mu0 < 1}
    {ctx : ConstructionContext d hd delta hdelta mu0 hmu0 hmu01}
    {N : Nat} (previous : CorrectionStage ctx N) where
  stage : CorrectionStage ctx (N + 1)
  residual_prefix : ∀ s : Fin N,
    stage.residual s.castSucc = previous.residual s
  carrierFn_prefix : ∀ s : Fin N,
    (stage.correction s.castSucc).carrierFn = (previous.correction s).carrierFn
  carrierSet_prefix : ∀ s : Fin N,
    (stage.correction s.castSucc).carrierSet = (previous.correction s).carrierSet
  differenceFn_prefix : ∀ s : Fin N,
    (stage.correction s.castSucc).differenceFn = (previous.correction s).differenceFn
  differenceCarrierSet_prefix : ∀ s : Fin N,
    (stage.correction s.castSucc).differenceCarrierSet =
      (previous.correction s).differenceCarrierSet

/-- Append the exact seed-plus-prefix residual. -/
noncomputable def extendCorrectionStage {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    {mu0 : Real} {hmu0 : 0 < mu0} {hmu01 : mu0 < 1}
    {ctx : ConstructionContext d hd delta hdelta mu0 hmu0 hmu01}
    {N : Nat} (previous : CorrectionStage ctx N) : StageExtension previous := by
  classical
  let lastResidual : BlockVector ctx N := fun n =>
    inverseSample ctx.seed.G0 (frequency delta n.1) +
      ∑ i : Fin N,
        inverseSample (previous.correction i).carrierFn (frequency delta n.1)
  let residual : (s : Fin (N + 1)) → BlockVector ctx s.1 := fun s =>
    Fin.lastCases lastResidual (fun i => previous.residual i) s
  have residual_last : residual (Fin.last N) = lastResidual := by
    simp [residual]
  have residual_prefix (i : Fin N) :
      residual i.castSucc = previous.residual i := by
    simp [residual]
  let castCorrection {s : Nat} {u v : BlockVector ctx s}
      (h : u = v) (C : LevelCorrection ctx s u) : LevelCorrection ctx s v :=
    h ▸ C
  have castCorrection_carrierFn {s : Nat} {u v : BlockVector ctx s}
      (h : u = v) (C : LevelCorrection ctx s u) :
      (castCorrection h C).carrierFn = C.carrierFn := by
    subst v
    rfl
  have castCorrection_carrierSet {s : Nat} {u v : BlockVector ctx s}
      (h : u = v) (C : LevelCorrection ctx s u) :
      (castCorrection h C).carrierSet = C.carrierSet := by
    subst v
    rfl
  have castCorrection_differenceFn {s : Nat} {u v : BlockVector ctx s}
      (h : u = v) (C : LevelCorrection ctx s u) :
      (castCorrection h C).differenceFn = C.differenceFn := by
    subst v
    rfl
  have castCorrection_differenceCarrierSet {s : Nat}
      {u v : BlockVector ctx s} (h : u = v) (C : LevelCorrection ctx s u) :
      (castCorrection h C).differenceCarrierSet = C.differenceCarrierSet := by
    subst v
    rfl
  let correction : (s : Fin (N + 1)) →
      LevelCorrection ctx s.1 (residual s) := fun s =>
    Fin.lastCases
      (castCorrection residual_last.symm
        (buildLevelCorrectionAt ctx N lastResidual))
      (fun i => castCorrection (residual_prefix i).symm
        (previous.correction i)) s
  have correction_carrierFn_prefix (i : Fin N) :
      (correction i.castSucc).carrierFn =
        (previous.correction i).carrierFn := by
    simp only [correction, Fin.lastCases_castSucc]
    apply castCorrection_carrierFn
  have correction_carrierSet_prefix (i : Fin N) :
      (correction i.castSucc).carrierSet =
        (previous.correction i).carrierSet := by
    simp only [correction, Fin.lastCases_castSucc]
    apply castCorrection_carrierSet
  have correction_differenceFn_prefix (i : Fin N) :
      (correction i.castSucc).differenceFn =
        (previous.correction i).differenceFn := by
    simp only [correction, Fin.lastCases_castSucc]
    apply castCorrection_differenceFn
  have correction_differenceCarrierSet_prefix (i : Fin N) :
      (correction i.castSucc).differenceCarrierSet =
        (previous.correction i).differenceCarrierSet := by
    simp only [correction, Fin.lastCases_castSucc]
    apply castCorrection_differenceCarrierSet
  let stage : CorrectionStage ctx (N + 1) :=
    { residual := residual
      correction := correction
      residual_eq := by
        intro s n
        refine Fin.lastCases ?_ (fun i n => ?_) s n
        · intro n
          rw [residual_last]
          simp only [lastResidual]
          apply congrArg (fun z =>
            inverseSample ctx.seed.G0 (frequency delta n.1) + z)
          apply Finset.univ.sum_congr rfl
          intro i _
          have hindex :
              (⟨i.1, Nat.lt_trans i.2 (Fin.last N).2⟩ : Fin (N + 1)) =
                i.castSucc := by ext; rfl
          have hcarrier :
              (correction
                ⟨i.1, Nat.lt_trans i.2 (Fin.last N).2⟩).carrierFn =
                (previous.correction i).carrierFn :=
            (congrArg (fun q => (correction q).carrierFn) hindex).trans
              (correction_carrierFn_prefix i)
          exact congrArg (fun f => inverseSample f (frequency delta n.1))
            hcarrier.symm
        · rw [residual_prefix]
          rw [previous.residual_eq]
          apply congrArg (fun z =>
            inverseSample ctx.seed.G0 (frequency delta n.1) + z)
          apply Finset.univ.sum_congr rfl
          intro x _
          let ix : Fin N := ⟨x.1, Nat.lt_trans x.2 i.2⟩
          have hindex :
              (⟨x.1, Nat.lt_trans x.2 i.castSucc.2⟩ : Fin (N + 1)) =
                ix.castSucc := by ext; rfl
          have hcarrier :
              (correction
                ⟨x.1, Nat.lt_trans x.2 i.castSucc.2⟩).carrierFn =
                (previous.correction ix).carrierFn :=
            (congrArg (fun q => (correction q).carrierFn) hindex).trans
              (correction_carrierFn_prefix ix)
          exact congrArg (fun f => inverseSample f (frequency delta n.1))
            hcarrier.symm }
  exact
    { stage := stage
      residual_prefix := residual_prefix
      carrierFn_prefix := correction_carrierFn_prefix
      carrierSet_prefix := correction_carrierSet_prefix
      differenceFn_prefix := correction_differenceFn_prefix
      differenceCarrierSet_prefix := correction_differenceCarrierSet_prefix }

/-- The constructor exposes all five prefix projections. -/
theorem extendCorrectionStage_prefix {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    {mu0 : Real} {hmu0 : 0 < mu0} {hmu01 : mu0 < 1}
    {ctx : ConstructionContext d hd delta hdelta mu0 hmu0 hmu01}
    {N : Nat} (previous : CorrectionStage ctx N) :
    (∀ s : Fin N, (extendCorrectionStage previous).stage.residual s.castSucc =
      previous.residual s) ∧
    (∀ s : Fin N, ((extendCorrectionStage previous).stage.correction
      s.castSucc).carrierFn = (previous.correction s).carrierFn) ∧
    (∀ s : Fin N, ((extendCorrectionStage previous).stage.correction
      s.castSucc).carrierSet = (previous.correction s).carrierSet) ∧
    (∀ s : Fin N, ((extendCorrectionStage previous).stage.correction
      s.castSucc).differenceFn = (previous.correction s).differenceFn) ∧
    (∀ s : Fin N, ((extendCorrectionStage previous).stage.correction
      s.castSucc).differenceCarrierSet =
        (previous.correction s).differenceCarrierSet) := by
  exact ⟨(extendCorrectionStage previous).residual_prefix,
    (extendCorrectionStage previous).carrierFn_prefix,
    (extendCorrectionStage previous).carrierSet_prefix,
    (extendCorrectionStage previous).differenceFn_prefix,
    (extendCorrectionStage previous).differenceCarrierSet_prefix⟩

/-- Sole owner of the finite-stage recursion. -/
noncomputable def correctionStage {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    {mu0 : Real} {hmu0 : 0 < mu0} {hmu01 : mu0 < 1}
    (ctx : ConstructionContext d hd delta hdelta mu0 hmu0 hmu01) :
    (N : Nat) → CorrectionStage ctx N
  | 0 => emptyCorrectionStage ctx
  | N + 1 => (extendCorrectionStage (correctionStage ctx N)).stage

/-- All observable fields are stable under stage extension. -/
theorem correctionStage_prefix {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    {mu0 : Real} {hmu0 : 0 < mu0} {hmu01 : mu0 < 1}
    (ctx : ConstructionContext d hd delta hdelta mu0 hmu0 hmu01)
    {M N : Nat} (hMN : M ≤ N) :
    (∀ s : Fin M, (correctionStage ctx N).residual
      ⟨s.1, lt_of_lt_of_le s.2 hMN⟩ = (correctionStage ctx M).residual s) ∧
    (∀ s : Fin M, ((correctionStage ctx N).correction
      ⟨s.1, lt_of_lt_of_le s.2 hMN⟩).carrierFn =
        ((correctionStage ctx M).correction s).carrierFn) ∧
    (∀ s : Fin M, ((correctionStage ctx N).correction
      ⟨s.1, lt_of_lt_of_le s.2 hMN⟩).carrierSet =
        ((correctionStage ctx M).correction s).carrierSet) ∧
    (∀ s : Fin M, ((correctionStage ctx N).correction
      ⟨s.1, lt_of_lt_of_le s.2 hMN⟩).differenceFn =
        ((correctionStage ctx M).correction s).differenceFn) ∧
    (∀ s : Fin M, ((correctionStage ctx N).correction
      ⟨s.1, lt_of_lt_of_le s.2 hMN⟩).differenceCarrierSet =
        ((correctionStage ctx M).correction s).differenceCarrierSet) := by
  induction N, hMN using Nat.le_induction with
  | base => exact ⟨fun _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl,
      fun _ ↦ rfl, fun _ ↦ rfl⟩
  | succ N hMN ih =>
      have hs := extendCorrectionStage_prefix (correctionStage ctx N)
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro s
        let q : Fin N := ⟨s.1, lt_of_lt_of_le s.2 hMN⟩
        simpa only [q, correctionStage, Fin.castSucc_mk] using
          (hs.1 q).trans (ih.1 s)
      · intro s
        let q : Fin N := ⟨s.1, lt_of_lt_of_le s.2 hMN⟩
        simpa only [q, correctionStage, Fin.castSucc_mk] using
          (hs.2.1 q).trans (ih.2.1 s)
      · intro s
        let q : Fin N := ⟨s.1, lt_of_lt_of_le s.2 hMN⟩
        simpa only [q, correctionStage, Fin.castSucc_mk] using
          (hs.2.2.1 q).trans (ih.2.2.1 s)
      · intro s
        let q : Fin N := ⟨s.1, lt_of_lt_of_le s.2 hMN⟩
        simpa only [q, correctionStage, Fin.castSucc_mk] using
          (hs.2.2.2.1 q).trans (ih.2.2.2.1 s)
      · intro s
        let q : Fin N := ⟨s.1, lt_of_lt_of_le s.2 hMN⟩
        simpa only [q, correctionStage, Fin.castSucc_mk] using
          (hs.2.2.2.2 q).trans (ih.2.2.2.2 s)

/-- Last residual in the stage of length `s+1`. -/
def residualAt {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    {mu0 : Real} {hmu0 : 0 < mu0} {hmu01 : mu0 < 1}
    (ctx : ConstructionContext d hd delta hdelta mu0 hmu0 hmu01) (s : Nat) :
    BlockVector ctx s := (correctionStage ctx (s + 1)).residual (Fin.last s)

/-- Last correction in the stage of length `s+1`. -/
def correctionAt {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    {mu0 : Real} {hmu0 : 0 < mu0} {hmu01 : mu0 < 1}
    (ctx : ConstructionContext d hd delta hdelta mu0 hmu0 hmu01) (s : Nat) :
    LevelCorrection ctx s (residualAt ctx s) :=
  (correctionStage ctx (s + 1)).correction (Fin.last s)

/-- Exact seed-plus-finite-prefix residual identity. -/
theorem residualAt_eq_inverseSample_prefix {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    {mu0 : Real} {hmu0 : 0 < mu0} {hmu01 : mu0 < 1}
    (ctx : ConstructionContext d hd delta hdelta mu0 hmu0 hmu01)
    (s : Nat) (n : {n : IntVec d // n ∈ dyadicBlock delta hdelta ctx.data.C0
      (ctx.threshold.J + s)}) :
    residualAt ctx s n = inverseSample ctx.seed.G0 (frequency delta n.1) +
      (Finset.range s).sum (fun i =>
        inverseSample (correctionAt ctx i).carrierFn (frequency delta n.1)) := by
  classical
  have hstage := (correctionStage ctx (s + 1)).residual_eq
    (Fin.last s) n
  change residualAt ctx s n = _ at hstage
  rw [hstage]
  apply congrArg (fun z ↦ inverseSample ctx.seed.G0 (frequency delta n.1) + z)
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  have hle : i.1 + 1 ≤ s + 1 := by omega
  have hp := correctionStage_prefix ctx hle
  have hcarrier :
      ((correctionStage ctx (s + 1)).correction
        ⟨i.1, lt_of_lt_of_le (Nat.lt_succ_self i.1) hle⟩).carrierFn =
        (correctionAt ctx i.1).carrierFn := by
    exact hp.2.1 ⟨i.1, Nat.lt_succ_self i.1⟩
  exact congrArg (fun f ↦ inverseSample f (frequency delta n.1)) hcarrier

/-- Current cancellation, new-prefix zero, and guard zero. -/
theorem correctionAt_trace {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    {mu0 : Real} {hmu0 : 0 < mu0} {hmu01 : mu0 < 1}
    (ctx : ConstructionContext d hd delta hdelta mu0 hmu0 hmu01) (s : Nat) :
    (∀ n : {n : IntVec d // n ∈ dyadicBlock delta hdelta ctx.data.C0
        (ctx.threshold.J + s)},
      inverseSample (correctionAt ctx s).carrierFn (frequency delta n.1) =
        -residualAt ctx s n) ∧
    (∀ n : {n : IntVec d // n ∈ dyadicBlock delta hdelta ctx.data.C0
        (ctx.threshold.J + s)},
      inverseSample ctx.seed.G0 (frequency delta n.1) +
        (Finset.range (s + 1)).sum (fun i =>
          inverseSample (correctionAt ctx i).carrierFn (frequency delta n.1)) = 0) ∧
    (∀ k, 3 ≤ k → k ≤ 4 * (ctx.threshold.J + s) →
      k ≠ ctx.threshold.J + s → ∀ n ∈ dyadicBlock delta hdelta ctx.data.C0 k,
        inverseSample (correctionAt ctx s).carrierFn (frequency delta n) = 0) := by
  classical
  by_cases hactive : (dyadicBlock delta hdelta ctx.data.C0
      (ctx.threshold.J + s)).Nonempty
  · let R := (correctionAt ctx s).activeResult hactive
    have hcarrier : (correctionAt ctx s).carrierFn = R.carrierFn :=
      (correctionAt ctx s).carrierFn_active hactive
    constructor
    · intro n
      rw [hcarrier]
      exact R.current_trace n
    constructor
    · intro n
      have ht : inverseSample (correctionAt ctx s).carrierFn
          (frequency delta n.1) = -residualAt ctx s n := by
        rw [hcarrier]
        exact R.current_trace n
      rw [Finset.sum_range_succ, ht]
      calc
        _ = (inverseSample ctx.seed.G0 (frequency delta n.1) +
              (Finset.range s).sum (fun i ↦
                inverseSample (correctionAt ctx i).carrierFn
                  (frequency delta n.1))) - residualAt ctx s n := by ring
        _ = 0 := by
          rw [← residualAt_eq_inverseSample_prefix ctx s n]
          ring
    · intro k hk3 hkguard hkne n hn
      rw [hcarrier]
      exact R.guard_trace k hk3 hkguard hkne n hn
  · have hz := (correctionAt ctx s).inactive hactive
    have hempty : ∀ n : {n : IntVec d // n ∈ dyadicBlock delta hdelta
        ctx.data.C0 (ctx.threshold.J + s)}, False := by
      intro n
      exact hactive ⟨n.1, n.2⟩
    constructor
    · intro n
      exact False.elim (hempty n)
    constructor
    · intro n
      exact False.elim (hempty n)
    · intro k hk3 hkguard hkne n hn
      rw [hz.1]
      simp [inverseSample, inverseSampleOn]

/-- Later corrections preserve earlier blocks and all exceptions. -/
theorem correctionAt_earlier_and_exception_zero {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    {mu0 : Real} {hmu0 : 0 < mu0} {hmu01 : mu0 < 1}
    (ctx : ConstructionContext d hd delta hdelta mu0 hmu0 hmu01) :
    (∀ s t, s < t → ∀ n ∈ dyadicBlock delta hdelta ctx.data.C0
      (ctx.threshold.J + s),
        inverseSample (correctionAt ctx t).carrierFn (frequency delta n) = 0) ∧
    (∀ s n, n ∈ ctx.data.C0 →
      inverseSample (correctionAt ctx s).carrierFn (frequency delta n) = 0) := by
  classical
  constructor
  · intro s t hst n hn
    exact (correctionAt_trace ctx t).2.2 (ctx.threshold.J + s)
      (by
        have hJ : 3 ≤ ctx.threshold.J :=
          (le_max_left 3 ctx.exceptionalConstants.jSep).trans ctx.threshold.J_ge
        omega)
      (by omega) (by omega) n hn
  · intro s n hn
    by_cases hactive : (dyadicBlock delta hdelta ctx.data.C0
        (ctx.threshold.J + s)).Nonempty
    · let R := (correctionAt ctx s).activeResult hactive
      rw [(correctionAt ctx s).carrierFn_active hactive]
      exact R.exceptional_trace n hn
    · have hz := (correctionAt ctx s).inactive hactive
      rw [hz.1]
      simp [inverseSample, inverseSampleOn]

/-- Complete per-level support facts and global disjointness. -/
theorem correctionAt_support_pairwiseDisjoint {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    {mu0 : Real} {hmu0 : 0 < mu0} {hmu01 : mu0 < 1}
    (ctx : ConstructionContext d hd delta hdelta mu0 hmu0 hmu01) :
    (∀ s,
      MeasurableSet (correctionAt ctx s).carrierSet ∧
      MeasurableSet (correctionAt ctx s).differenceCarrierSet ∧
      AEStronglyMeasurable (correctionAt ctx s).carrierFn volume ∧
      AEStronglyMeasurable (correctionAt ctx s).differenceFn volume ∧
      Integrable (correctionAt ctx s).carrierFn volume ∧
      Integrable (correctionAt ctx s).differenceFn volume ∧
      MemLp (correctionAt ctx s).carrierFn (2 : ENNReal) volume ∧
      MemLp (correctionAt ctx s).differenceFn (2 : ENNReal) volume ∧
      AESupportedIn (correctionAt ctx s).carrierFn (correctionAt ctx s).carrierSet ∧
      AESupportedIn (correctionAt ctx s).differenceFn
        (correctionAt ctx s).differenceCarrierSet ∧
      volume (correctionAt ctx s).carrierSet ≤
        ENNReal.ofReal (ctx.blocks.eta (ctx.threshold.J + s) / 2) ∧
      volume (correctionAt ctx s).carrierSet ≠ ∞ ∧
      (volume (correctionAt ctx s).carrierSet).toReal ≤
        ctx.blocks.eta (ctx.threshold.J + s) / 2 ∧
      volume (correctionAt ctx s).differenceCarrierSet ≤
        ENNReal.ofReal (ctx.blocks.eta (ctx.threshold.J + s)) ∧
      (correctionAt ctx s).carrierSet ⊆ ⋃ r,
        baseEnvelope ctx s r (carrierOrigin ctx s r) ∧
      (correctionAt ctx s).differenceCarrierSet ⊆ ⋃ r,
        differenceEnvelope ctx s r (carrierOrigin ctx s r)) ∧
    Set.Pairwise (Set.univ : Set Nat) (fun s t =>
      Disjoint (correctionAt ctx s).carrierSet (correctionAt ctx t).carrierSet) ∧
    Set.Pairwise (Set.univ : Set Nat) (fun s t =>
      Disjoint (correctionAt ctx s).differenceCarrierSet
        (correctionAt ctx t).differenceCarrierSet) ∧
    (∀ s, Disjoint ctx.seed.A0 (correctionAt ctx s).carrierSet) ∧
    (∀ s, Disjoint ctx.seedWitness.S0
      (correctionAt ctx s).differenceCarrierSet) := by
  classical
  have hJ3 : 3 ≤ ctx.threshold.J :=
    (le_max_left 3 ctx.exceptionalConstants.jSep).trans ctx.threshold.J_ge
  have hlocal (s : Nat) :
      MeasurableSet (correctionAt ctx s).carrierSet ∧
      MeasurableSet (correctionAt ctx s).differenceCarrierSet ∧
      AEStronglyMeasurable (correctionAt ctx s).carrierFn volume ∧
      AEStronglyMeasurable (correctionAt ctx s).differenceFn volume ∧
      Integrable (correctionAt ctx s).carrierFn volume ∧
      Integrable (correctionAt ctx s).differenceFn volume ∧
      MemLp (correctionAt ctx s).carrierFn (2 : ENNReal) volume ∧
      MemLp (correctionAt ctx s).differenceFn (2 : ENNReal) volume ∧
      AESupportedIn (correctionAt ctx s).carrierFn (correctionAt ctx s).carrierSet ∧
      AESupportedIn (correctionAt ctx s).differenceFn
        (correctionAt ctx s).differenceCarrierSet ∧
      volume (correctionAt ctx s).carrierSet ≤
        ENNReal.ofReal (ctx.blocks.eta (ctx.threshold.J + s) / 2) ∧
      volume (correctionAt ctx s).carrierSet ≠ ∞ ∧
      (volume (correctionAt ctx s).carrierSet).toReal ≤
        ctx.blocks.eta (ctx.threshold.J + s) / 2 ∧
      volume (correctionAt ctx s).differenceCarrierSet ≤
        ENNReal.ofReal (ctx.blocks.eta (ctx.threshold.J + s)) ∧
      (correctionAt ctx s).carrierSet ⊆ ⋃ r,
        baseEnvelope ctx s r (carrierOrigin ctx s r) ∧
      (correctionAt ctx s).differenceCarrierSet ⊆ ⋃ r,
        differenceEnvelope ctx s r (carrierOrigin ctx s r) := by
    have heta : 0 < ctx.blocks.eta (ctx.threshold.J + s) :=
      ctx.blocks.eta_pos _ (by omega)
    by_cases hactive : (dyadicBlock delta hdelta ctx.data.C0
        (ctx.threshold.J + s)).Nonempty
    · let R := (correctionAt ctx s).activeResult hactive
      have hC := (correctionAt ctx s).carrierFn_active hactive
      have hD := (correctionAt ctx s).differenceFn_active hactive
      have hA := (correctionAt ctx s).carrierSet_active hactive
      have hB := (correctionAt ctx s).differenceCarrierSet_active hactive
      have hAne : volume R.carrierSet ≠ ∞ :=
        ne_top_of_le_ne_top ENNReal.ofReal_ne_top R.carrier_volume
      have hAreal : (volume R.carrierSet).toReal ≤
          ctx.blocks.eta (ctx.threshold.J + s) / 2 := by
        have hmono := ENNReal.toReal_mono ENNReal.ofReal_ne_top R.carrier_volume
        have hdiv : 0 ≤ ctx.blocks.eta (ctx.threshold.J + s) / 2 :=
          div_nonneg heta.le (by norm_num)
        simpa only [ENNReal.toReal_ofReal hdiv] using hmono
      have hbaseEq (r : Fin d) :
          levelBaseEnvelope (cachedPlanFamily ctx s)
              (fun r ↦ carrierOrigin ctx s r) r =
            baseEnvelope ctx s r (carrierOrigin ctx s r) := by
        cases hp : ctx.plan s r with
        | none => simp [levelBaseEnvelope, cachedPlanFamily, baseEnvelope, hp]
        | some p =>
          have hc := ctx.plan_canonical s r p hp
          simp [levelBaseEnvelope, cachedPlanFamily, baseEnvelope, hp, hc]
      have hdifferenceEq (r : Fin d) :
          levelDifferenceEnvelope (cachedPlanFamily ctx s)
              (fun r ↦ carrierOrigin ctx s r) r =
            differenceEnvelope ctx s r (carrierOrigin ctx s r) := by
        cases hp : ctx.plan s r with
        | none =>
          simp [levelDifferenceEnvelope, cachedPlanFamily, differenceEnvelope, hp]
        | some p =>
          have hc := ctx.plan_canonical s r p hp
          simp [levelDifferenceEnvelope, cachedPlanFamily, differenceEnvelope,
            hp, hc]
      rw [hC, hD, hA, hB]
      refine ⟨R.carrierSet_measurable, R.differenceCarrierSet_measurable,
        R.carrierFn_stronglyMeasurable, R.differenceFn_stronglyMeasurable,
        R.carrierFn_integrable, R.differenceFn_integrable,
        R.carrierFn_memLp, R.differenceFn_memLp,
        R.carrierFn_supported, R.differenceFn_supported,
        R.carrier_volume, hAne, hAreal, R.differenceCarrier_volume, ?_, ?_⟩
      · intro x hx
        have hx' := R.carrierSet_contained hx
        simpa only [hbaseEq] using hx'
      · intro x hx
        have hx' := R.differenceCarrierSet_contained hx
        simpa only [hdifferenceEq] using hx'
    · obtain ⟨hC, hD, hA, hB⟩ := (correctionAt ctx s).inactive hactive
      rw [hC, hD, hA, hB]
      simp [AESupportedIn]
      exact ⟨aestronglyMeasurable_zero,
        div_nonneg heta.le (by norm_num)⟩
  have henv := carrierOrigin_envelopes ctx
  refine ⟨hlocal, ?_, ?_, ?_, ?_⟩
  · intro s hs t ht hst
    rw [Set.disjoint_left]
    intro x hxs hxt
    have hCs := (hlocal s).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hxs
    have hCt := (hlocal t).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hxt
    obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hCs
    obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hCt
    have hpairs := henv.1 (Set.mem_univ (s, r)) (Set.mem_univ (t, q))
      (by intro h; exact hst (congrArg Prod.fst h))
    exact Set.disjoint_left.mp hpairs hr hq
  · intro s hs t ht hst
    rw [Set.disjoint_left]
    intro x hxs hxt
    have hDs := (hlocal s).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 hxs
    have hDt := (hlocal t).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 hxt
    obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hDs
    obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hDt
    have hpairs := henv.2.1 (Set.mem_univ (s, r)) (Set.mem_univ (t, q))
      (by intro h; exact hst (congrArg Prod.fst h))
    exact Set.disjoint_left.mp hpairs hr hq
  · intro s
    rw [Set.disjoint_left]
    intro x hxseed hxC
    have hx := (hlocal s).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hxC
    obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hx
    exact Set.disjoint_left.mp (henv.2.2.1 s r) hr hxseed
  · intro s
    rw [Set.disjoint_left]
    intro x hxseed hxD
    have hx := (hlocal s).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 hxD
    obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hx
    exact Set.disjoint_left.mp (henv.2.2.2 s r) hr hxseed

/-- Sole normalized residual-energy definition. -/
def residualEnergy {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    {mu0 : Real} {hmu0 : 0 < mu0} {hmu01 : mu0 < 1}
    (ctx : ConstructionContext d hd delta hdelta mu0 hmu0 hmu01)
    (s : Nat) : Real :=
  (1 / ctx.blocks.eta (ctx.threshold.J + s)) *
    ∑ n : {n : IntVec d // n ∈ dyadicBlock delta hdelta ctx.data.C0
      (ctx.threshold.J + s)}, ‖residualAt ctx s n‖ ^ 2

/-- Totalized leakage beyond the protected guard. -/
def correctionFutureLeakage {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    {mu0 : Real} {hmu0 : 0 < mu0} {hmu01 : mu0 < 1}
    (ctx : ConstructionContext d hd delta hdelta mu0 hmu0 hmu01)
    (s k : Nat) : Real :=
  if 4 * (ctx.threshold.J + s) < k then
    blockEnergyTerm ctx.blocks (correctionAt ctx s).carrierFn k
  else 0

/-- Summability and quantitative bound for one leakage tail. -/
theorem correctionAt_futureLeakage {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    {mu0 : Real} {hmu0 : 0 < mu0} {hmu01 : mu0 < 1}
    (ctx : ConstructionContext d hd delta hdelta mu0 hmu0 hmu01) (s : Nat) :
    Summable (correctionFutureLeakage ctx s) ∧
    ∑' k, correctionFutureLeakage ctx s k ≤
      (ctx.correctionConstants.leak * dyadicScale (ctx.threshold.J + s)) ^ 2 *
        residualEnergy ctx s := by
  classical
  by_cases hactive : (dyadicBlock delta hdelta ctx.data.C0
      (ctx.threshold.J + s)).Nonempty
  · let R := (correctionAt ctx s).activeResult hactive
    have hcarrier : (correctionAt ctx s).carrierFn = R.carrierFn :=
      (correctionAt ctx s).carrierFn_active hactive
    have hleak : correctionFutureLeakage ctx s = fun k : Nat ↦
        if 4 * (ctx.threshold.J + s) < k then
          blockEnergyTerm ctx.blocks R.carrierFn k else 0 := by
      funext k
      simp only [correctionFutureLeakage]
      rw [hcarrier]
    rw [hleak]
    have hR := levelCorrection_futureLeakage R
    refine ⟨hR.1, hR.2.trans_eq ?_⟩
    rfl
  · have hzero := ((correctionAt ctx s).inactive hactive).1
    have hleak : correctionFutureLeakage ctx s = 0 := by
      funext k
      simp [correctionFutureLeakage, hzero, blockEnergyTerm,
        inverseSample, inverseSampleOn]
    have hres : residualEnergy ctx s = 0 := by
      unfold residualEnergy
      have hsum : (∑ n : {n : IntVec d // n ∈ dyadicBlock delta hdelta
          ctx.data.C0 (ctx.threshold.J + s)}, ‖residualAt ctx s n‖ ^ 2) = 0 := by
        apply Finset.univ.sum_eq_zero
        intro n hn
        exact False.elim (hactive ⟨n.1, n.2⟩)
      rw [hsum]
      ring
    rw [hleak, hres]
    exact ⟨summable_zero, by simp⟩

/-- Exact residual identity and global energy control. -/
theorem correctionSequence_energy {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    {mu0 : Real} {hmu0 : 0 < mu0} {hmu01 : mu0 < 1}
    (ctx : ConstructionContext d hd delta hdelta mu0 hmu0 hmu01) :
    (∀ s, residualEnergy ctx s = blockEnergyTerm ctx.blocks
      (fun x => ctx.seed.G0 x +
        (Finset.range s).sum (fun i => (correctionAt ctx i).carrierFn x))
      (ctx.threshold.J + s)) ∧
    Summable (residualEnergy ctx) ∧
    (∑' s, residualEnergy ctx s) ≤ 4 * seedEnergyTotal ctx.seed ∧
    Summable (fun s => sqNormOn Set.univ (correctionAt ctx s).carrierFn) ∧
    (∑' s, sqNormOn Set.univ (correctionAt ctx s).carrierFn) ≤
      ctx.correctionConstants.cost * 4 * seedEnergyTotal ctx.seed ∧
    Summable (fun s => sqNormOn Set.univ (correctionAt ctx s).differenceFn) ∧
    (∑' s, sqNormOn Set.univ (correctionAt ctx s).differenceFn) ≤
      ctx.correctionConstants.cost * 4 * seedEnergyTotal ctx.seed := by
  classical
  have hJ3 : 3 ≤ ctx.threshold.J :=
    (le_max_left 3 ctx.exceptionalConstants.jSep).trans ctx.threshold.J_ge
  have hchar_integrable (F : RealVec d → Complex) (hF : Integrable F volume)
      (xi : RealVec d) :
      Integrable (fun x ↦ F x * fourierChar xi x) volume := by
    have hchar : Continuous (fourierChar xi) := by
      unfold fourierChar
      fun_prop
    apply hF.mul_bdd (c := 1) hchar.aestronglyMeasurable
    filter_upwards [] with x
    simp [fourierChar, Complex.norm_exp]
  have hinverse_add (F G : RealVec d → Complex) (hF : Integrable F volume)
      (hG : Integrable G volume) (xi : RealVec d) :
      inverseSample (fun x ↦ F x + G x) xi =
        inverseSample F xi + inverseSample G xi := by
    simp only [inverseSample, inverseSampleOn, setIntegral_univ, add_mul]
    exact integral_add (hchar_integrable F hF xi) (hchar_integrable G hG xi)
  have hinverse_sum {m : Nat} (F : Nat → RealVec d → Complex)
      (hF : ∀ i < m, Integrable (F i) volume) (xi : RealVec d) :
      inverseSample (fun x ↦ (Finset.range m).sum (fun i ↦ F i x)) xi =
        (Finset.range m).sum (fun i ↦ inverseSample (F i) xi) := by
    simp only [inverseSample, inverseSampleOn, setIntegral_univ, Finset.sum_mul]
    rw [integral_finsetSum]
    intro i hi
    exact hchar_integrable (F i) (hF i (Finset.mem_range.mp hi)) xi
  have hcorrection_integrable (i : Nat) :
      Integrable (correctionAt ctx i).carrierFn volume := by
    by_cases hactive : (dyadicBlock delta hdelta ctx.data.C0
        (ctx.threshold.J + i)).Nonempty
    · rw [(correctionAt ctx i).carrierFn_active hactive]
      exact ((correctionAt ctx i).activeResult hactive).carrierFn_integrable
    · rw [((correctionAt ctx i).inactive hactive).1]
      exact integrable_zero _ _ _
  have henergyEq (s : Nat) :
      residualEnergy ctx s = blockEnergyTerm ctx.blocks
        (fun x ↦ ctx.seed.G0 x +
          (Finset.range s).sum (fun i ↦ (correctionAt ctx i).carrierFn x))
        (ctx.threshold.J + s) := by
    rw [residualEnergy, blockEnergyTerm, if_pos (by omega : 3 ≤ ctx.threshold.J + s)]
    apply congrArg (fun z ↦ (1 / ctx.blocks.eta (ctx.threshold.J + s)) * z)
    rw [← (dyadicBlock delta hdelta ctx.data.C0
      (ctx.threshold.J + s)).sum_attach]
    apply Finset.univ.sum_congr rfl
    intro n _
    congr 2
    rw [residualAt_eq_inverseSample_prefix ctx s n]
    rw [hinverse_add ctx.seed.G0
      (fun x ↦ (Finset.range s).sum
        (fun i ↦ (correctionAt ctx i).carrierFn x))
      ctx.seed.G0_integrable
      (integrable_finsetSum _ fun i _ ↦ hcorrection_integrable i)
      (frequency delta n.1)]
    rw [hinverse_sum (fun i ↦ (correctionAt ctx i).carrierFn)]
    intro i _
    exact hcorrection_integrable i
  have hresidual_inactive (s : Nat)
      (hinactive : ¬(dyadicBlock delta hdelta ctx.data.C0
        (ctx.threshold.J + s)).Nonempty) : residualEnergy ctx s = 0 := by
    unfold residualEnergy
    have hsum : (∑ n : {n : IntVec d // n ∈ dyadicBlock delta hdelta
        ctx.data.C0 (ctx.threshold.J + s)}, ‖residualAt ctx s n‖ ^ 2) = 0 := by
      apply Finset.univ.sum_eq_zero
      intro n hn
      exact False.elim (hinactive ⟨n.1, n.2⟩)
    rw [hsum]
    ring
  have hcost (s : Nat) :
      sqNormOn Set.univ (correctionAt ctx s).carrierFn +
          sqNormOn Set.univ (correctionAt ctx s).differenceFn ≤
        ctx.correctionConstants.cost * residualEnergy ctx s := by
    by_cases hactive : (dyadicBlock delta hdelta ctx.data.C0
        (ctx.threshold.J + s)).Nonempty
    · let R := (correctionAt ctx s).activeResult hactive
      rw [(correctionAt ctx s).carrierFn_active hactive,
        (correctionAt ctx s).differenceFn_active hactive]
      calc
        sqNormOn Set.univ R.carrierFn + sqNormOn Set.univ R.differenceFn ≤
            ctx.correctionConstants.cost /
              ctx.blocks.eta (ctx.threshold.J + s) *
              ∑ n, ‖residualAt ctx s n‖ ^ 2 := R.combined_energy
        _ = ctx.correctionConstants.cost * residualEnergy ctx s := by
          unfold residualEnergy
          ring
    · obtain ⟨hC, hD, _, _⟩ := (correctionAt ctx s).inactive hactive
      rw [hC, hD, hresidual_inactive s hactive]
      simp [sqNormOn]
  have ha (s : Nat) : 0 ≤ residualEnergy ctx s := by
    unfold residualEnergy
    exact mul_nonneg (one_div_nonneg.mpr
      (ctx.blocks.eta_pos _ (by omega)).le)
      (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
  have hblock_nonneg (H : RealVec d → Complex) (j : Nat) :
      0 ≤ blockEnergyTerm ctx.blocks H j := by
    rw [blockEnergyTerm]
    split_ifs with hj
    · exact mul_nonneg (one_div_nonneg.mpr (ctx.blocks.eta_pos j hj).le)
        (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
    · exact le_rfl
  let seedTail : Nat → Real := fun s ↦
    blockEnergyTerm ctx.blocks ctx.seed.G0 (ctx.threshold.J + s)
  let leakageWeight : Nat → Real := fun s ↦
    ctx.correctionConstants.leak * dyadicScale (ctx.threshold.J + s)
  have hseedTail_nonneg (s : Nat) : 0 ≤ seedTail s := hblock_nonneg _ _
  have hleakageWeight_nonneg (s : Nat) : 0 ≤ leakageWeight s := by
    exact mul_nonneg (le_trans (by norm_num)
      ctx.correctionConstants.one_le_leak)
      (by unfold dyadicScale; positivity)
  obtain ⟨hseedSummable, hseedEnergy_nonneg, hseedHasSum⟩ :=
    seedEnergy_summable ctx.seed
  have hseedTailSummable : Summable seedTail := by
    apply hseedSummable.comp_injective
    intro i j hij
    exact Nat.add_left_cancel hij
  have hseedTailTsum : ∑' s, seedTail s ≤ seedEnergyTotal ctx.seed := by
    have hsplit := hseedSummable.sum_add_tsum_nat_add ctx.threshold.J
    have hprefix : 0 ≤
        ∑ i ∈ Finset.range ctx.threshold.J,
          blockEnergyTerm ctx.blocks ctx.seed.G0 i :=
      Finset.sum_nonneg fun i _ ↦ hblock_nonneg _ i
    have htail : (∑' i, blockEnergyTerm ctx.blocks ctx.seed.G0
        (i + ctx.threshold.J)) ≤ seedEnergyTotal ctx.seed := by
      rw [seedEnergyTotal]
      linarith
    simpa only [seedTail, Nat.add_comm] using htail
  let squareTail : Nat → Real := fun j ↦
    if ctx.threshold.J ≤ j then
      (ctx.correctionConstants.leak * dyadicScale j) ^ 2 else 0
  have hsquareTail_nonneg (j : Nat) : 0 ≤ squareTail j := by
    simp only [squareTail]
    split_ifs
    · positivity
    · exact le_rfl
  have hsquareTailSummable : Summable squareTail := by
    simpa only [squareTail] using ctx.threshold.squareTail_summable
  have hshift_inj : Function.Injective (fun s : Nat ↦ ctx.threshold.J + s) := by
    intro i j hij
    exact Nat.add_left_cancel hij
  have hleakageSqEq : (fun s ↦ (leakageWeight s) ^ 2) =
      squareTail ∘ (fun s : Nat ↦ ctx.threshold.J + s) := by
    funext s
    simp [leakageWeight, squareTail]
  have hleakageSqSummable : Summable (fun s ↦ (leakageWeight s) ^ 2) := by
    rw [hleakageSqEq]
    exact hsquareTailSummable.comp_injective hshift_inj
  have hleakageSqTsum : ∑' s, (leakageWeight s) ^ 2 ≤ 1 / 4 := by
    rw [hleakageSqEq]
    exact (tsum_comp_le_tsum_of_inj hsquareTailSummable hsquareTail_nonneg
      hshift_inj).trans ctx.threshold.squareTail_tsum_le
  let shellIndex (N : Nat) := Σ s : Fin N,
    {n : IntVec d // n ∈ dyadicBlock delta hdelta ctx.data.C0
      (ctx.threshold.J + s.1)}
  let levelWeight (s : Nat) : Real :=
    Real.sqrt (1 / ctx.blocks.eta (ctx.threshold.J + s))
  let residualVec (N : Nat) : EuclideanSpace Complex (shellIndex N) :=
    WithLp.toLp 2 (fun z ↦
      (levelWeight z.1.1 : Complex) * residualAt ctx z.1.1 z.2)
  let seedVec (N : Nat) : EuclideanSpace Complex (shellIndex N) :=
    WithLp.toLp 2 (fun z ↦
      (levelWeight z.1.1 : Complex) *
        inverseSample ctx.seed.G0 (frequency delta z.2.1))
  let correctionVec (N i : Nat) : EuclideanSpace Complex (shellIndex N) :=
    WithLp.toLp 2 (fun z ↦
      if i < z.1.1 then
        (levelWeight z.1.1 : Complex) *
          inverseSample (correctionAt ctx i).carrierFn
            (frequency delta z.2.1)
      else 0)
  have hresidualVec_norm (N : Nat) :
      ‖residualVec N‖ =
        Real.sqrt (∑ s ∈ Finset.range N, residualEnergy ctx s) := by
    rw [EuclideanSpace.norm_eq]
    congr 1
    rw [← Fin.sum_univ_eq_sum_range]
    simp only [shellIndex, residualVec]
    rw [Fintype.sum_sigma]
    apply Finset.univ.sum_congr rfl
    intro s _
    rw [residualEnergy]
    simp only [levelWeight, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), mul_pow]
    rw [Real.sq_sqrt (one_div_nonneg.mpr
      (ctx.blocks.eta_pos _ (by omega)).le)]
    rw [Finset.mul_sum]
  have hseedVec_norm (N : Nat) :
      ‖seedVec N‖ = Real.sqrt (∑ s ∈ Finset.range N, seedTail s) := by
    rw [EuclideanSpace.norm_eq]
    congr 1
    rw [← Fin.sum_univ_eq_sum_range]
    simp only [shellIndex, seedVec]
    rw [Fintype.sum_sigma]
    apply Finset.univ.sum_congr rfl
    intro s _
    change _ = blockEnergyTerm ctx.blocks ctx.seed.G0
      (ctx.threshold.J + s.1)
    rw [blockEnergyTerm, if_pos (by omega : 3 ≤ ctx.threshold.J + s.1)]
    rw [← (dyadicBlock delta hdelta ctx.data.C0
      (ctx.threshold.J + s.1)).sum_attach]
    simp only [levelWeight, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), mul_pow]
    rw [Real.sq_sqrt (one_div_nonneg.mpr
      (ctx.blocks.eta_pos _ (by omega)).le)]
    rw [Finset.mul_sum]
    simp
  have hvector_eq (N : Nat) :
      residualVec N = seedVec N +
        (Finset.range N).sum (fun i ↦ correctionVec N i) := by
    ext z
    simp only [residualVec, seedVec, PiLp.add_apply]
    rw [WithLp.ofLp_sum]
    simp only [Finset.sum_apply, correctionVec]
    change (levelWeight z.1.1 : Complex) * residualAt ctx z.1.1 z.2 =
        (levelWeight z.1.1 : Complex) *
          inverseSample ctx.seed.G0 (frequency delta z.2.1) +
        (Finset.range N).sum (fun i ↦ if i < z.1.1 then
          (levelWeight z.1.1 : Complex) *
            inverseSample (correctionAt ctx i).carrierFn
              (frequency delta z.2.1) else 0)
    rw [residualAt_eq_inverseSample_prefix ctx z.1.1 z.2]
    have hfilter : (Finset.range N).filter (fun i ↦ i < z.1.1) =
        Finset.range z.1.1 := by
      ext i
      simp
      omega
    rw [← Finset.sum_filter]
    rw [hfilter]
    rw [← Finset.mul_sum]
    ring
  have hweighted_inverse_block (H : RealVec d → Complex) (s : Nat) :
      (∑ n : {n : IntVec d // n ∈ dyadicBlock delta hdelta ctx.data.C0
          (ctx.threshold.J + s)},
        ‖(levelWeight s : Complex) *
          inverseSample H (frequency delta n.1)‖ ^ 2) =
        blockEnergyTerm ctx.blocks H (ctx.threshold.J + s) := by
    rw [blockEnergyTerm, if_pos (by omega : 3 ≤ ctx.threshold.J + s)]
    rw [← (dyadicBlock delta hdelta ctx.data.C0
      (ctx.threshold.J + s)).sum_attach]
    simp only [levelWeight, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), mul_pow]
    rw [Real.sq_sqrt (one_div_nonneg.mpr
      (ctx.blocks.eta_pos _ (by omega)).le)]
    rw [Finset.mul_sum]
    simp
  have hcorrection_sample_zero (i s : Nat) (his : i < s)
      (hnotfuture : ¬ 4 * (ctx.threshold.J + i) < ctx.threshold.J + s)
      (n : {n : IntVec d // n ∈ dyadicBlock delta hdelta ctx.data.C0
        (ctx.threshold.J + s)}) :
      inverseSample (correctionAt ctx i).carrierFn
        (frequency delta n.1) = 0 := by
    exact (correctionAt_trace ctx i).2.2 (ctx.threshold.J + s)
      (by omega) (by omega) (by omega) n.1 n.2
  have hcorrection_block_energy (i s : Nat) (his : i < s) :
      (∑ n : {n : IntVec d // n ∈ dyadicBlock delta hdelta ctx.data.C0
          (ctx.threshold.J + s)},
        ‖(levelWeight s : Complex) *
          inverseSample (correctionAt ctx i).carrierFn
            (frequency delta n.1)‖ ^ 2) =
        correctionFutureLeakage ctx i (ctx.threshold.J + s) := by
    by_cases hfuture : 4 * (ctx.threshold.J + i) < ctx.threshold.J + s
    · rw [correctionFutureLeakage, if_pos hfuture]
      exact hweighted_inverse_block _ _
    · rw [correctionFutureLeakage, if_neg hfuture]
      apply Finset.sum_eq_zero
      intro n hn
      rw [hcorrection_sample_zero i s his hfuture n]
      simp
  have hcorrectionVec_norm_sq (N i : Nat) :
      ‖correctionVec N i‖ ^ 2 =
        ∑ s ∈ Finset.range N,
          if i < s then
            correctionFutureLeakage ctx i (ctx.threshold.J + s)
          else 0 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [shellIndex, correctionVec]
    rw [Fintype.sum_sigma]
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.univ.sum_congr rfl
    intro s hs
    by_cases his : i < s.1
    · simp only [his, if_pos]
      exact hcorrection_block_energy i s.1 his
    · simp [his]
  have hfuture_nonneg (i k : Nat) :
      0 ≤ correctionFutureLeakage ctx i k := by
    rw [correctionFutureLeakage]
    split_ifs
    · exact hblock_nonneg _ _
    · exact le_rfl
  have hcorrectionVec_norm_sq_le (N i : Nat) :
      ‖correctionVec N i‖ ^ 2 ≤
        (leakageWeight i) ^ 2 * residualEnergy ctx i := by
    rw [hcorrectionVec_norm_sq]
    obtain ⟨hfutureSummable, hfutureTsum⟩ :=
      correctionAt_futureLeakage ctx i
    have hshiftSummable : Summable (fun s ↦
        correctionFutureLeakage ctx i (ctx.threshold.J + s)) :=
      hfutureSummable.comp_injective hshift_inj
    calc
      (∑ s ∈ Finset.range N,
          if i < s then correctionFutureLeakage ctx i
            (ctx.threshold.J + s) else 0) ≤
          ∑ s ∈ Finset.range N,
            correctionFutureLeakage ctx i (ctx.threshold.J + s) := by
        apply Finset.sum_le_sum
        intro s hs
        split_ifs
        · exact le_rfl
        · exact hfuture_nonneg _ _
      _ ≤ ∑' s, correctionFutureLeakage ctx i (ctx.threshold.J + s) :=
        hshiftSummable.sum_le_tsum (Finset.range N)
          (fun s _ ↦ hfuture_nonneg _ _)
      _ ≤ ∑' k, correctionFutureLeakage ctx i k := by
        change tsum (correctionFutureLeakage ctx i ∘
          fun s : Nat ↦ ctx.threshold.J + s) ≤ _
        exact tsum_comp_le_tsum_of_inj hfutureSummable
          (hfuture_nonneg i) hshift_inj
      _ ≤ (leakageWeight i) ^ 2 * residualEnergy ctx i := by
        simpa only [leakageWeight] using hfutureTsum
  have hcorrectionVec_norm_le (N i : Nat) :
      ‖correctionVec N i‖ ≤
        leakageWeight i * Real.sqrt (residualEnergy ctx i) := by
    rw [← sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (hleakageWeight_nonneg i) (Real.sqrt_nonneg _))]
    rw [mul_pow, Real.sq_sqrt (ha i)]
    exact hcorrectionVec_norm_sq_le N i
  have htri (N : Nat) :
      Real.sqrt (∑ s ∈ Finset.range N, residualEnergy ctx s) ≤
        Real.sqrt (∑ s ∈ Finset.range N, seedTail s) +
          ∑ i ∈ Finset.range N,
            leakageWeight i * Real.sqrt (residualEnergy ctx i) := by
    rw [← hresidualVec_norm N, hvector_eq N]
    calc
      ‖seedVec N + (Finset.range N).sum (fun i ↦ correctionVec N i)‖ ≤
          ‖seedVec N‖ + ‖(Finset.range N).sum
            (fun i ↦ correctionVec N i)‖ := norm_add_le _ _
      _ ≤ ‖seedVec N‖ + (Finset.range N).sum
          (fun i ↦ ‖correctionVec N i‖) :=
        add_le_add_right (norm_sum_le (Finset.range N)
          (fun i ↦ correctionVec N i)) _
      _ ≤ Real.sqrt (∑ s ∈ Finset.range N, seedTail s) +
          ∑ i ∈ Finset.range N,
            leakageWeight i * Real.sqrt (residualEnergy ctx i) := by
        rw [hseedVec_norm N]
        exact add_le_add_right
          (Finset.sum_le_sum fun i _ ↦ hcorrectionVec_norm_le N i) _
  obtain ⟨haSummable, haTsum⟩ :=
    triangular_residual_energy
      (residualEnergy ctx) seedTail leakageWeight (seedEnergyTotal ctx.seed)
      ha hseedTail_nonneg hleakageWeight_nonneg hseedTailSummable
      hseedTailTsum hseedEnergy_nonneg hleakageSqSummable hleakageSqTsum htri
  have hsqNorm_nonneg (F : RealVec d → Complex) :
      0 ≤ sqNormOn Set.univ F := by
    rw [sqNormOn, setIntegral_univ]
    exact integral_nonneg fun x ↦ sq_nonneg ‖F x‖
  let carrierEnergy : Nat → Real := fun s ↦
    sqNormOn Set.univ (correctionAt ctx s).carrierFn
  let differenceEnergy : Nat → Real := fun s ↦
    sqNormOn Set.univ (correctionAt ctx s).differenceFn
  have hcarrier_nonneg (s : Nat) : 0 ≤ carrierEnergy s :=
    hsqNorm_nonneg _
  have hdifference_nonneg (s : Nat) : 0 ≤ differenceEnergy s :=
    hsqNorm_nonneg _
  have hcarrier_le (s : Nat) :
      carrierEnergy s ≤
        ctx.correctionConstants.cost * residualEnergy ctx s :=
    (le_add_of_nonneg_right (hdifference_nonneg s)).trans (hcost s)
  have hdifference_le (s : Nat) :
      differenceEnergy s ≤
        ctx.correctionConstants.cost * residualEnergy ctx s :=
    (le_add_of_nonneg_left (hcarrier_nonneg s)).trans (hcost s)
  have hmajor : Summable (fun s ↦
      ctx.correctionConstants.cost * residualEnergy ctx s) :=
    haSummable.mul_left ctx.correctionConstants.cost
  have hcarrierSummable : Summable carrierEnergy :=
    Summable.of_nonneg_of_le hcarrier_nonneg hcarrier_le hmajor
  have hdifferenceSummable : Summable differenceEnergy :=
    Summable.of_nonneg_of_le hdifference_nonneg hdifference_le hmajor
  have hcarrierTsum : ∑' s, carrierEnergy s ≤
      ctx.correctionConstants.cost * 4 * seedEnergyTotal ctx.seed := by
    calc
      (∑' s, carrierEnergy s) ≤ ∑' s,
          ctx.correctionConstants.cost * residualEnergy ctx s :=
        Summable.tsum_le_tsum hcarrier_le hcarrierSummable hmajor
      _ = ctx.correctionConstants.cost * ∑' s, residualEnergy ctx s := by
        rw [tsum_mul_left]
      _ ≤ ctx.correctionConstants.cost *
          (4 * seedEnergyTotal ctx.seed) :=
        mul_le_mul_of_nonneg_left haTsum
          ctx.correctionConstants.cost_pos.le
      _ = ctx.correctionConstants.cost * 4 * seedEnergyTotal ctx.seed := by ring
  have hdifferenceTsum : ∑' s, differenceEnergy s ≤
      ctx.correctionConstants.cost * 4 * seedEnergyTotal ctx.seed := by
    calc
      (∑' s, differenceEnergy s) ≤ ∑' s,
          ctx.correctionConstants.cost * residualEnergy ctx s :=
        Summable.tsum_le_tsum hdifference_le hdifferenceSummable hmajor
      _ = ctx.correctionConstants.cost * ∑' s, residualEnergy ctx s := by
        rw [tsum_mul_left]
      _ ≤ ctx.correctionConstants.cost *
          (4 * seedEnergyTotal ctx.seed) :=
        mul_le_mul_of_nonneg_left haTsum
          ctx.correctionConstants.cost_pos.le
      _ = ctx.correctionConstants.cost * 4 * seedEnergyTotal ctx.seed := by ring
  refine ⟨henergyEq, haSummable, haTsum, ?_, ?_, ?_, ?_⟩
  · simpa only [carrierEnergy] using hcarrierSummable
  · simpa only [carrierEnergy] using hcarrierTsum
  · simpa only [differenceEnergy] using hdifferenceSummable
  · simpa only [differenceEnergy] using hdifferenceTsum

end Internal

end AsymptoticallyIntegerHD
