import AsymptoticallyIntegerHD.Definitions
import AsymptoticallyIntegerHD.FrequencyCarriers
import AsymptoticallyIntegerHD.Seed
import AsymptoticallyIntegerHD.CorrectionRecursion
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

/-!
# Infinite assembly of the higher-dimensional annihilating witness

This module assembles the higher-dimensional annihilating witness using
transparent definitions and the dimension-free one-dimensional argument.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Pointwise

namespace AsymptoticallyIntegerHD
namespace Internal

variable {d : Nat} {hd : 0 < d}
variable {delta : IntVec d → RealVec d}
variable {hdelta : TendsToZeroAtIntVecInfinity delta}
variable {mu0 : Real} {hmu0 : 0 < mu0} {hmu01 : mu0 < 1}

private theorem integral_norm_le_sqrt_measure_mul_sqrt_sqNorm
    (A : Set (RealVec d)) (f : RealVec d → Complex) (hne : volume A ≠ ∞)
    (hmem : MemLp f (2 : ENNReal) volume) (hsupp : AESupportedIn f A) :
    (∫ x : RealVec d, ‖f x‖) ≤
      Real.sqrt (volume A).toReal * Real.sqrt (sqNormOn Set.univ f) := by
  have hL1 : (∫ x : RealVec d, ‖f x‖) = ∫ x in A, ‖f x‖ := by
    symm
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [hsupp] with x hx
    intro hxA
    rw [hx hxA, norm_zero]
  have hL2 : (∫ x in A, Real.rpow ‖f x‖ 2) = sqNormOn Set.univ f := by
    calc
      (∫ x in A, Real.rpow ‖f x‖ 2) = ∫ x in A, ‖f x‖ ^ (2 : Nat) := by
        apply integral_congr_ae
        filter_upwards [] with x
        exact Real.rpow_two _
      _ = ∫ x : RealVec d, ‖f x‖ ^ (2 : Nat) :=
        setIntegral_eq_integral_of_ae_compl_eq_zero <| by
          filter_upwards [hsupp] with x hx
          intro hxA
          rw [hx hxA, norm_zero]
          norm_num
      _ = sqNormOn Set.univ f := by simp [sqNormOn]
  letI : IsFiniteMeasure (volume.restrict A) :=
    isFiniteMeasure_restrict.mpr hne
  have hmem' : MemLp f (ENNReal.ofReal (2 : Real)) (volume.restrict A) := by
    norm_num
    exact hmem.restrict A
  have hholder := integral_mul_norm_le_Lp_mul_Lq
    (μ := volume.restrict A) Real.HolderConjugate.two_two
    (memLp_const (p := ENNReal.ofReal (2 : Real)) (1 : Complex)) hmem'
  have hholder' : (∫ x in A, ‖f x‖) ≤
      Real.sqrt (volume A).toReal *
        Real.sqrt (∫ x in A, Real.rpow ‖f x‖ 2) := by
    simpa [Real.sqrt_eq_rpow, measureReal_def] using hholder
  rw [hL1]
  calc
    (∫ x in A, ‖f x‖) ≤ Real.sqrt (volume A).toReal *
        Real.sqrt (∫ x in A, Real.rpow ‖f x‖ 2) := hholder'
    _ = Real.sqrt (volume A).toReal * Real.sqrt (sqNormOn Set.univ f) := by
      rw [hL2]

/- Proof idea: port the 1D carrier-supported Cauchy--Schwarz estimate, then apply
finite-prefix Cauchy--Schwarz to support budgets and correction energies. -/
theorem correction_l1Norm_summable
    (ctx : ConstructionContext d hd delta hdelta mu0 hmu0 hmu01) :
    Summable (fun s =>
      ∫ x : RealVec d, ‖(correctionAt ctx s).carrierFn x‖) := by
  let a : Nat → Real := fun s =>
    (volume (correctionAt ctx s).carrierSet).toReal
  let b : Nat → Real := fun s =>
    sqNormOn Set.univ (correctionAt ctx s).carrierFn
  have ha0 : ∀ s, 0 ≤ a s := fun s => ENNReal.toReal_nonneg
  have hb0 : ∀ s, 0 ≤ b s := by
    intro s
    dsimp [b, sqNormOn]
    exact integral_nonneg fun _ => sq_nonneg _
  have hetaTail : Summable
      (fun s => ctx.blocks.eta (ctx.threshold.J + s)) :=
    ctx.budgets.eta_summable.comp_injective (by
      intro i j h
      omega)
  have haBound : ∀ s, a s ≤
      ctx.blocks.eta (ctx.threshold.J + s) / 2 := by
    intro s
    rcases (correctionAt_support_pairwiseDisjoint ctx).1 s with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, h, _⟩
    exact h
  have haSummable : Summable a :=
    Summable.of_nonneg_of_le ha0 haBound (hetaTail.div_const 2)
  have hbSummable : Summable b := by
    simpa [b] using (correctionSequence_energy ctx).2.2.2.1
  have hsqrtProduct : Summable
      (fun s => Real.sqrt (a s) * Real.sqrt (b s)) := by
    apply Summable.of_nonneg_of_le
      (f := fun s => (a s + b s) / 2)
    · intro s
      positivity
    · intro s
      have haSq := Real.sq_sqrt (ha0 s)
      have hbSq := Real.sq_sqrt (hb0 s)
      nlinarith [sq_nonneg (Real.sqrt (a s) - Real.sqrt (b s))]
    · exact (haSummable.add hbSummable).div_const 2
  apply Summable.of_nonneg_of_le
    (f := fun s => Real.sqrt (a s) * Real.sqrt (b s))
  · intro s
    exact integral_nonneg fun _ => norm_nonneg _
  · intro s
    rcases (correctionAt_support_pairwiseDisjoint ctx).1 s with
      ⟨_, _, _, _, _, _, hmem, _, hsupp, _, _, hne, _⟩
    simpa [a, b] using
      integral_norm_le_sqrt_measure_mul_sqrt_sqNorm
        (correctionAt ctx s).carrierSet (correctionAt ctx s).carrierFn
        hne hmem hsupp
  · exact hsqrtProduct

/- Proof idea: Tonelli on the nonnegative norm series; export one common conull
event carrying both forms of summability. -/
theorem correction_pointwise_summable_ae
    (ctx : ConstructionContext d hd delta hdelta mu0 hmu0 hmu01) :
    ∀ᵐ x ∂volume,
      Summable (fun s => (correctionAt ctx s).carrierFn x) ∧
      Summable (fun s => ‖(correctionAt ctx s).carrierFn x‖) := by
  have hmeas : ∀ s,
      AEStronglyMeasurable (correctionAt ctx s).carrierFn volume := by
    intro s
    rcases (correctionAt_support_pairwiseDisjoint ctx).1 s with
      ⟨_, _, h, _⟩
    exact h
  have hint : ∀ s, Integrable (correctionAt ctx s).carrierFn volume := by
    intro s
    rcases (correctionAt_support_pairwiseDisjoint ctx).1 s with
      ⟨_, _, _, _, h, _⟩
    exact h
  have hnorm (s : Nat) :
      eLpNorm (correctionAt ctx s).carrierFn 1 volume =
        ENNReal.ofReal
          (∫ x : RealVec d, ‖(correctionAt ctx s).carrierFn x‖) := by
    rw [eLpNorm_one_eq_lintegral_enorm]
    change (∫⁻ x : RealVec d, ↑‖(correctionAt ctx s).carrierFn x‖₊ ∂volume) = _
    rw [lintegral_coe_eq_integral _ (hint s).norm]
    simp only [coe_nnnorm]
  have hLpSum :
      ∑' s, eLpNorm (correctionAt ctx s).carrierFn 1 volume ≠ ∞ := by
    simp_rw [hnorm]
    exact (correction_l1Norm_summable ctx).tsum_ofReal_ne_top
  filter_upwards [summable_norm_of_tsum_eLpNorm_ne_top
      (p := (1 : ENNReal)) (by simp) hmeas hLpSum] with x hx
  exact ⟨hx.of_norm, hx⟩

/-!
The sole pointwise carrier representative; it exists before convergence is
proved.
-/
def assembledCarrierFunction
    (ctx : ConstructionContext d hd delta hdelta mu0 hmu0 hmu01)
    (x : RealVec d) : Complex :=
  ctx.seed.G0 x + ∑' s, (correctionAt ctx s).carrierFn x

/- Proof idea: identify the pointwise `tsum` on the shared conull event. -/
theorem assembledCarrier_hasSum_ae
    (ctx : ConstructionContext d hd delta hdelta mu0 hmu0 hmu01) :
    ∀ᵐ x ∂volume,
      HasSum (fun s => (correctionAt ctx s).carrierFn x)
        (assembledCarrierFunction ctx x - ctx.seed.G0 x) := by
  filter_upwards [correction_pointwise_summable_ae ctx] with x hx
  have hsum := hx.1.hasSum
  simpa [assembledCarrierFunction] using hsum

private theorem integrable_tsum_of_summable_integral_norm'
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [CompleteSpace E] (μ : Measure α) (F : Nat → α → E)
    (hFint : ∀ s, Integrable (F s) μ)
    (hFsum : Summable (fun s => ∫ x, ‖F s x‖ ∂μ)) :
    Integrable (fun x => ∑' s, F s x) μ := by
  let hmem : ∀ s, MemLp (F s) (1 : ENNReal) μ := fun s =>
    memLp_one_iff_integrable.mpr (hFint s)
  let g : Nat → Lp E (1 : ENNReal) μ := fun s => (hmem s).toLp (F s)
  have hnorm (s : Nat) : ‖g s‖ₑ = ENNReal.ofReal (∫ x, ‖F s x‖ ∂μ) := by
    change ‖(hmem s).toLp (F s)‖ₑ = _
    rw [Lp.enorm_toLp, eLpNorm_one_eq_lintegral_enorm]
    change (∫⁻ x, ↑‖F s x‖₊ ∂μ) = _
    rw [lintegral_coe_eq_integral _ (hFint s).norm]
    simp only [coe_nnnorm]
  have hnormSum : ∑' s, ‖g s‖ₑ ≠ ∞ := by
    simp_rw [hnorm]
    exact hFsum.tsum_ofReal_ne_top
  have hcoeEach : ∀ᵐ x ∂μ, ∀ s, ⇑(g s) x = F s x := by
    rw [ae_all_iff]
    intro s
    exact (hmem s).coeFn_toLp
  have hcoeSum :
      (⇑(∑' s, g s) : α → E) =ᵐ[μ] fun x => ∑' s, F s x := by
    filter_upwards [Lp.coeFn_tsum hnormSum, hcoeEach] with x hsum hterm
    rw [hsum]
    congr 1
    funext s
    exact hterm s
  exact (memLp_one_iff_integrable.mp (Lp.memLp (∑' s, g s))).congr hcoeSum

/- Proof idea: use the local Bochner-series bridge and identify its sum through
`assembledCarrier_hasSum_ae`.  No second representative is introduced. -/
theorem assembledCarrier_integrable
    (ctx : ConstructionContext d hd delta hdelta mu0 hmu0 hmu01) :
    Integrable (assembledCarrierFunction ctx) volume := by
  let f : Nat → RealVec d → Complex := fun s => (correctionAt ctx s).carrierFn
  have hint : ∀ s, Integrable (f s) volume := by
    intro s
    rcases (correctionAt_support_pairwiseDisjoint ctx).1 s with
      ⟨_, _, _, _, h, _⟩
    exact h
  have hsumInt : Integrable (fun x => ∑' s, f s x) volume :=
    integrable_tsum_of_summable_integral_norm' volume f hint <| by
      simpa [f] using correction_l1Norm_summable ctx
  apply (ctx.seed.G0_integrable.add hsumInt).congr
  apply Filter.Eventually.of_forall
  intro x
  rfl

/- Proof idea: use seed/correction avoidance and pairwise disjoint correction
carriers on one conull event. -/
theorem assembledCarrier_norm_sq_ae
    (ctx : ConstructionContext d hd delta hdelta mu0 hmu0 hmu01) :
    ∀ᵐ x ∂volume,
      ‖assembledCarrierFunction ctx x‖ ^ 2 =
        ‖ctx.seed.G0 x‖ ^ 2 +
          ∑' s, ‖(correctionAt ctx s).carrierFn x‖ ^ 2 := by
  rcases correctionAt_support_pairwiseDisjoint ctx with
    ⟨hlevel, hpairCarrier, _, hseedCarrier, _⟩
  have hcarrierSupport : ∀ᵐ x ∂volume, ∀ s,
      x ∉ (correctionAt ctx s).carrierSet →
        (correctionAt ctx s).carrierFn x = 0 := by
    rw [ae_all_iff]
    intro s
    rcases hlevel s with ⟨_, _, _, _, _, _, _, _, h, _⟩
    exact h
  filter_upwards [ctx.seed.G0_supported, hcarrierSupport] with x hseed hcarrier
  by_cases hexists : ∃ s, (correctionAt ctx s).carrierFn x ≠ 0
  · obtain ⟨s, hs⟩ := hexists
    have hxs : x ∈ (correctionAt ctx s).carrierSet := by
      by_contra hx
      exact hs (hcarrier s hx)
    have hseedZero : ctx.seed.G0 x = 0 := by
      apply hseed
      intro hxSeed
      exact (Set.disjoint_left.1 (hseedCarrier s) hxSeed) hxs
    have hother : ∀ k, k ≠ s → (correctionAt ctx k).carrierFn x = 0 := by
      intro k hks
      apply hcarrier k
      intro hxk
      exact (Set.disjoint_left.1
        (hpairCarrier (Set.mem_univ s) (Set.mem_univ k) hks.symm) hxs) hxk
    have hcarrierTsum :
        (∑' k, (correctionAt ctx k).carrierFn x) =
          (correctionAt ctx s).carrierFn x :=
      tsum_eq_single s hother
    have hnormTsum :
        (∑' k, ‖(correctionAt ctx k).carrierFn x‖ ^ 2) =
          ‖(correctionAt ctx s).carrierFn x‖ ^ 2 := by
      apply tsum_eq_single s
      intro k hks
      rw [hother k hks, norm_zero, zero_pow (by norm_num : (2 : Nat) ≠ 0)]
    simp [assembledCarrierFunction, hseedZero, hcarrierTsum, hnormTsum]
  · have hall : ∀ s, (correctionAt ctx s).carrierFn x = 0 := by
      intro s
      by_contra hs
      exact hexists ⟨s, hs⟩
    have hcarrierZero :
        (fun s => (correctionAt ctx s).carrierFn x) =
          fun _ : Nat => (0 : Complex) := by
      funext s
      exact hall s
    have hnormZero :
        (fun s => ‖(correctionAt ctx s).carrierFn x‖ ^ 2) =
          fun _ : Nat => (0 : Real) := by
      funext s
      rw [hall s, norm_zero, zero_pow (by norm_num : (2 : Nat) ≠ 0)]
    simp [assembledCarrierFunction, hcarrierZero, hnormZero]

/- Proof idea: integrate `assembledCarrier_norm_sq_ae` after establishing summability; every
`sqNormOn` call has the carrier set first. -/
theorem assembledCarrier_sqNorm_eq
    (ctx : ConstructionContext d hd delta hdelta mu0 hmu0 hmu01) :
    sqNormOn Set.univ (assembledCarrierFunction ctx) =
      sqNormOn Set.univ ctx.seed.G0 +
        ∑' s, sqNormOn Set.univ (correctionAt ctx s).carrierFn := by
  let q : Nat → RealVec d → Real :=
    fun s x => ‖(correctionAt ctx s).carrierFn x‖ ^ 2
  have hqInt : ∀ s, Integrable (q s) volume := by
    intro s
    rcases (correctionAt_support_pairwiseDisjoint ctx).1 s with
      ⟨_, _, _, _, _, _, hmem, _⟩
    simpa [q] using hmem.integrable_norm_pow (by norm_num : (2 : Nat) ≠ 0)
  have henergy : Summable
      (fun s => sqNormOn Set.univ (correctionAt ctx s).carrierFn) :=
    (correctionSequence_energy ctx).2.2.2.1
  have hqNormSum : Summable (fun s => ∫ x : RealVec d, ‖q s x‖) := by
    simpa [q, sqNormOn, Real.norm_of_nonneg] using henergy
  have hqSumInt : Integrable (fun x => ∑' s, q s x) volume :=
    integrable_tsum_of_summable_integral_norm' volume q hqInt hqNormSum
  have hseedInt : Integrable (fun x => ‖ctx.seed.G0 x‖ ^ 2) volume := by
    simpa using ctx.seed.G0_memLp.integrable_norm_pow (by norm_num : (2 : Nat) ≠ 0)
  have hIntegralTsum :
      (∫ x : RealVec d, ∑' s, q s x) = ∑' s, ∫ x : RealVec d, q s x :=
    (integral_tsum_of_summable_integral_norm hqInt hqNormSum).symm
  unfold sqNormOn
  simp only [Measure.restrict_univ]
  calc
    (∫ x : RealVec d, ‖assembledCarrierFunction ctx x‖ ^ 2) =
        ∫ x : RealVec d, ‖ctx.seed.G0 x‖ ^ 2 + ∑' s, q s x := by
      apply integral_congr_ae
      filter_upwards [assembledCarrier_norm_sq_ae ctx] with x hx
      simpa [q] using hx
    _ = (∫ x : RealVec d, ‖ctx.seed.G0 x‖ ^ 2) +
          ∫ x : RealVec d, ∑' s, q s x := integral_add hseedInt hqSumInt
    _ = (∫ x : RealVec d, ‖ctx.seed.G0 x‖ ^ 2) +
          ∑' s, ∫ x : RealVec d, q s x := by rw [hIntegralTsum]
    _ = (∫ x : RealVec d, ‖ctx.seed.G0 x‖ ^ 2) +
          ∑' s, ∫ x : RealVec d, ‖(correctionAt ctx s).carrierFn x‖ ^ 2 := by
      rfl

/-!
`assembledCarrier_stronglyMeasurable` gives almost-everywhere strong
measurability, following from `assembledCarrier_integrable`.
-/
theorem assembledCarrier_stronglyMeasurable
    (ctx : ConstructionContext d hd delta hdelta mu0 hmu0 hmu01) :
    AEStronglyMeasurable (assembledCarrierFunction ctx) volume := by
  exact (assembledCarrier_integrable ctx).aestronglyMeasurable

/- Proof idea: convert the finite whole-space squared norm to ambient `MemLp 2`. -/
theorem assembledCarrier_memLp_two
    (ctx : ConstructionContext d hd delta hdelta mu0 hmu0 hmu01) :
    MemLp (assembledCarrierFunction ctx) (2 : ENNReal) volume := by
  let q : Nat → RealVec d → Real :=
    fun s x => ‖(correctionAt ctx s).carrierFn x‖ ^ 2
  have hqInt : ∀ s, Integrable (q s) volume := by
    intro s
    rcases (correctionAt_support_pairwiseDisjoint ctx).1 s with
      ⟨_, _, _, _, _, _, hmem, _⟩
    simpa [q] using hmem.integrable_norm_pow (by norm_num : (2 : Nat) ≠ 0)
  have henergy : Summable
      (fun s => sqNormOn Set.univ (correctionAt ctx s).carrierFn) :=
    (correctionSequence_energy ctx).2.2.2.1
  have hqNormSum : Summable (fun s => ∫ x : RealVec d, ‖q s x‖) := by
    simpa [q, sqNormOn, Real.norm_of_nonneg] using henergy
  have hqSumInt : Integrable (fun x => ∑' s, q s x) volume :=
    integrable_tsum_of_summable_integral_norm' volume q hqInt hqNormSum
  have hseedInt : Integrable (fun x => ‖ctx.seed.G0 x‖ ^ 2) volume := by
    simpa using ctx.seed.G0_memLp.integrable_norm_pow (by norm_num : (2 : Nat) ≠ 0)
  have hnormInt : Integrable
      (fun x => ‖assembledCarrierFunction ctx x‖ ^ 2) volume :=
    (hseedInt.add hqSumInt).congr <| by
      filter_upwards [assembledCarrier_norm_sq_ae ctx] with x hx
      simpa [q] using hx.symm
  apply (integrable_norm_rpow_iff (assembledCarrier_stronglyMeasurable ctx)
    (by norm_num : (2 : ENNReal) ≠ 0) (by norm_num : (2 : ENNReal) ≠ ∞)).mp
  simpa using hnormInt

/-!
The sole pointwise witness representative.
-/
def assembledWitness
    (ctx : ConstructionContext d hd delta hdelta mu0 hmu0 hmu01) :
    RealVec d → Complex :=
  firstCoordinateDifference hd (assembledCarrierFunction ctx)

/- Proof idea: intersect translated and untranslated conull events, subtract the
two `HasSum` statements, and retain norm summability as the second conjunct. -/
theorem assembledWitness_series_ae
    (ctx : ConstructionContext d hd delta hdelta mu0 hmu0 hmu01) :
    ∀ᵐ x ∂volume,
      HasSum (fun s => (correctionAt ctx s).differenceFn x)
          (assembledWitness ctx x - ctx.seedWitness.F0 x) ∧
        Summable (fun s => ‖(correctionAt ctx s).differenceFn x‖) := by
  have hnow := assembledCarrier_hasSum_ae ctx
  have hshift : ∀ᵐ x ∂volume,
      HasSum (fun s => (correctionAt ctx s).carrierFn
          (x - basisVector (firstCoordinate hd)))
        (assembledCarrierFunction ctx (x - basisVector (firstCoordinate hd)) -
          ctx.seed.G0 (x - basisVector (firstCoordinate hd))) := by
    have h := (quasiMeasurePreserving_add_left volume
      (-basisVector (firstCoordinate hd))).ae hnow
    simpa [sub_eq_add_neg, add_comm] using h
  filter_upwards [hnow, hshift] with x hx hxshift
  have hdifference := hxshift.sub hx
  have hterms :
      (fun s => (correctionAt ctx s).differenceFn x) =
        fun s => (correctionAt ctx s).carrierFn
            (x - basisVector (firstCoordinate hd)) -
          (correctionAt ctx s).carrierFn x := by
    funext s
    rw [(correctionAt ctx s).differenceFn_eq]
    rfl
  have htarget :
      (assembledCarrierFunction ctx (x - basisVector (firstCoordinate hd)) -
          ctx.seed.G0 (x - basisVector (firstCoordinate hd))) -
        (assembledCarrierFunction ctx x - ctx.seed.G0 x) =
          assembledWitness ctx x - ctx.seedWitness.F0 x := by
    rw [ctx.seedWitness.F0_eq]
    simp only [assembledWitness, firstCoordinateDifference, vectorTranslate]
    ring
  have hsum : HasSum (fun s => (correctionAt ctx s).differenceFn x)
      (assembledWitness ctx x - ctx.seedWitness.F0 x) := by
    rw [hterms]
    rw [← htarget]
    exact hdifference
  exact ⟨hsum, hsum.summable.norm⟩

/-!
This is only the explicit carrier definition; it is not `Function.support`.
-/
def witnessCarrier
    (ctx : ConstructionContext d hd delta hdelta mu0 hmu0 hmu01) :
    Set (RealVec d) :=
  ctx.seedWitness.S0 ∪
    ⋃ s, (correctionAt ctx s).differenceCarrierSet

/- Proof idea: use the witness series for support, countable subadditivity for the
carrier union, and the real-to-ENNReal summable-series bridge. -/
theorem assembledWitness_support_integrability
    (ctx : ConstructionContext d hd delta hdelta mu0 hmu0 hmu01) :
    MeasurableSet (witnessCarrier ctx) ∧
    AEStronglyMeasurable (assembledWitness ctx) volume ∧
    Integrable (assembledWitness ctx) volume ∧
    MemLp (assembledWitness ctx) (2 : ENNReal) volume ∧
    AESupportedIn (assembledWitness ctx) (witnessCarrier ctx) ∧
    volume (witnessCarrier ctx) ≤
      ENNReal.ofReal (mu0 / 4) +
        ∑' s, ENNReal.ofReal (ctx.blocks.eta (ctx.threshold.J + s)) ∧
    ENNReal.ofReal (mu0 / 4) +
        ∑' s, ENNReal.ofReal (ctx.blocks.eta (ctx.threshold.J + s)) ≤
      ENNReal.ofReal (mu0 / 2) ∧
    ENNReal.ofReal (mu0 / 2) < ENNReal.ofReal mu0 := by
  have hdiffMeas : ∀ s,
      MeasurableSet (correctionAt ctx s).differenceCarrierSet := by
    intro s
    rcases (correctionAt_support_pairwiseDisjoint ctx).1 s with
      ⟨_, h, _⟩
    exact h
  have hdiffSupport : ∀ s,
      AESupportedIn (correctionAt ctx s).differenceFn
        (correctionAt ctx s).differenceCarrierSet := by
    intro s
    rcases (correctionAt_support_pairwiseDisjoint ctx).1 s with
      ⟨_, _, _, _, _, _, _, _, _, h, _⟩
    exact h
  have hdiffVolume : ∀ s,
      volume (correctionAt ctx s).differenceCarrierSet ≤
        ENNReal.ofReal (ctx.blocks.eta (ctx.threshold.J + s)) := by
    intro s
    rcases (correctionAt_support_pairwiseDisjoint ctx).1 s with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, h, _⟩
    exact h
  have hSmeas : MeasurableSet (witnessCarrier ctx) := by
    exact ctx.seedWitness.S0_measurable.union
      (MeasurableSet.iUnion fun s => hdiffMeas s)
  have hcarrierUniv : AESupportedIn (assembledCarrierFunction ctx) Set.univ := by
    filter_upwards [] with x
    simp
  rcases firstCoordinateDifference_support_cost hd MeasurableSet.univ
      (assembledCarrier_stronglyMeasurable ctx)
      (assembledCarrier_integrable ctx) (assembledCarrier_memLp_two ctx)
      hcarrierUniv with ⟨_, hFmeas, hFint, hFLp, _, _, _⟩
  have hcorrSupport : ∀ᵐ x ∂volume, ∀ s,
      x ∉ (correctionAt ctx s).differenceCarrierSet →
        (correctionAt ctx s).differenceFn x = 0 := by
    rw [ae_all_iff]
    intro s
    exact hdiffSupport s
  have hFsupp : AESupportedIn (assembledWitness ctx) (witnessCarrier ctx) := by
    filter_upwards [assembledWitness_series_ae ctx,
      ctx.seedWitness.F0_supported, hcorrSupport] with x hseries hseed hcorr
    intro hx
    have hxSeed : x ∉ ctx.seedWitness.S0 := by
      intro hmem
      exact hx (Set.mem_union_left _ hmem)
    have hxCorr : ∀ s, x ∉ (correctionAt ctx s).differenceCarrierSet := by
      intro s hmem
      apply hx
      exact Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨s, hmem⟩)
    have hterms : ∀ s, (correctionAt ctx s).differenceFn x = 0 :=
      fun s => hcorr s (hxCorr s)
    have hzero : HasSum (fun s => (correctionAt ctx s).differenceFn x) 0 := by
      convert (hasSum_zero : HasSum (fun _ : Nat => (0 : Complex)) 0) using 1
      funext s
      exact hterms s
    have htarget : assembledWitness ctx x - ctx.seedWitness.F0 x = 0 :=
      hseries.1.unique hzero
    rw [hseed hxSeed] at htarget
    simpa using htarget
  have hmeasure : volume (witnessCarrier ctx) ≤
      ENNReal.ofReal (mu0 / 4) +
        ∑' s, ENNReal.ofReal (ctx.blocks.eta (ctx.threshold.J + s)) := by
    calc
      volume (witnessCarrier ctx) ≤ volume ctx.seedWitness.S0 +
          volume (⋃ s, (correctionAt ctx s).differenceCarrierSet) := by
        exact measure_union_le _ _
      _ ≤ ENNReal.ofReal (mu0 / 4) +
          ∑' s, volume (correctionAt ctx s).differenceCarrierSet := by
        exact add_le_add ctx.seedWitness.volume_S0_lt.le (measure_iUnion_le _)
      _ ≤ ENNReal.ofReal (mu0 / 4) +
          ∑' s, ENNReal.ofReal
            (ctx.blocks.eta (ctx.threshold.J + s)) := by
        exact add_le_add_right (ENNReal.tsum_le_tsum hdiffVolume) _
  have htailSummable : Summable
      (fun s => ctx.blocks.eta (ctx.threshold.J + s)) :=
    ctx.budgets.eta_summable.comp_injective (by
      intro a b h
      omega)
  have htailNonneg : ∀ s, 0 ≤ ctx.blocks.eta (ctx.threshold.J + s) :=
    fun s => ctx.budgets.eta_nonneg _
  have htailReal : (∑' s, ctx.blocks.eta (ctx.threshold.J + s)) ≤ mu0 / 4 := by
    have hsplit := ctx.budgets.eta_summable.sum_add_tsum_nat_add ctx.threshold.J
    have hsplit' :
        ∑ s ∈ Finset.range ctx.threshold.J, ctx.blocks.eta s +
            ∑' s, ctx.blocks.eta (ctx.threshold.J + s) =
          ∑' s, ctx.blocks.eta s := by
      simpa [Nat.add_comm] using hsplit
    have hprefix : 0 ≤ ∑ s ∈ Finset.range ctx.threshold.J, ctx.blocks.eta s :=
      Finset.sum_nonneg fun s _ => ctx.budgets.eta_nonneg s
    linarith [ctx.budgets.eta_tsum_le, hsplit']
  have htailENN :
      ∑' s, ENNReal.ofReal (ctx.blocks.eta (ctx.threshold.J + s)) ≤
        ENNReal.ofReal (mu0 / 4) := by
    rw [← ENNReal.ofReal_tsum_of_nonneg htailNonneg htailSummable]
    exact ENNReal.ofReal_le_ofReal htailReal
  have hbudget : ENNReal.ofReal (mu0 / 4) +
        ∑' s, ENNReal.ofReal (ctx.blocks.eta (ctx.threshold.J + s)) ≤
      ENNReal.ofReal (mu0 / 2) := by
    calc
      _ ≤ ENNReal.ofReal (mu0 / 4) + ENNReal.ofReal (mu0 / 4) :=
        add_le_add_right htailENN _
      _ = ENNReal.ofReal (mu0 / 2) := by
        have hquarter : 0 ≤ mu0 / 4 := by linarith
        rw [← ENNReal.ofReal_add hquarter hquarter]
        congr 1
        ring
  have hstrict : ENNReal.ofReal (mu0 / 2) < ENNReal.ofReal mu0 := by
    exact (ENNReal.ofReal_lt_ofReal_iff hmu0).mpr (by linarith)
  exact ⟨hSmeas, hFmeas, hFint, hFLp, hFsupp, hmeasure, hbudget, hstrict⟩

/- Proof idea: on the reserved seed-witness carrier all correction differences
vanish, so the witness agrees with the nonzero seed witness.  This theorem
does not depend on the support-budget package `assembledWitness_support_integrability`. -/
theorem assembledWitness_ne_zero
    (ctx : ConstructionContext d hd delta hdelta mu0 hmu0 hmu01) :
    ¬ assembledWitness ctx =ᵐ[volume]
      (0 : RealVec d → Complex) := by
  intro hzeroWitness
  rcases correctionAt_support_pairwiseDisjoint ctx with
    ⟨hlevel, _, _, _, hseedDiff⟩
  have hcorrOnSeed : ∀ᵐ x ∂volume, ∀ s,
      x ∈ ctx.seedWitness.S0 → (correctionAt ctx s).differenceFn x = 0 := by
    rw [ae_all_iff]
    intro s
    rcases hlevel s with ⟨_, _, _, _, _, _, _, _, _, hsupp, _⟩
    filter_upwards [hsupp] with x hx
    intro hxSeed
    apply hx
    intro hxCorr
    exact Set.disjoint_left.1 (hseedDiff s) hxSeed hxCorr
  apply ctx.seedWitness.F0_ae_ne_zero
  filter_upwards [assembledWitness_series_ae ctx, hcorrOnSeed,
    hzeroWitness, ctx.seedWitness.F0_supported] with x hseries hcorr hW hseed
  by_cases hxSeed : x ∈ ctx.seedWitness.S0
  · have hterms : ∀ s, (correctionAt ctx s).differenceFn x = 0 :=
      fun s => hcorr s hxSeed
    have hzeroSeries : HasSum
        (fun s => (correctionAt ctx s).differenceFn x) 0 := by
      convert (hasSum_zero : HasSum (fun _ : Nat => (0 : Complex)) 0) using 1
      funext s
      exact hterms s
    have htarget : assembledWitness ctx x - ctx.seedWitness.F0 x = 0 :=
      hseries.1.unique hzeroSeries
    rw [hW] at htarget
    simpa using htarget
  · exact hseed hxSeed

/- Proof idea: exchange the absolutely L1-summable series with the integral; the
vector character has norm one. -/
theorem inverseSample_corrections_hasSum
    (ctx : ConstructionContext d hd delta hdelta mu0 hmu0 hmu01)
    (xi : RealVec d) :
    HasSum
      (fun s => inverseSample (correctionAt ctx s).carrierFn xi)
      (inverseSample (assembledCarrierFunction ctx) xi -
        inverseSample ctx.seed.G0 xi) := by
  let e : RealVec d → Complex := fun x => fourierChar xi x
  let f : Nat → RealVec d → Complex :=
    fun s x => (correctionAt ctx s).carrierFn x * e x
  have heMeas : AEStronglyMeasurable e volume := by
    exact (show Continuous e by
      dsimp [e, fourierChar]
      fun_prop).aestronglyMeasurable
  have heBound : ∀ᵐ x ∂volume, ‖e x‖ ≤ 1 := by
    apply Filter.Eventually.of_forall
    intro x
    dsimp [e, fourierChar]
    rw [Complex.norm_exp]
    norm_num
  have hcarrierInt : ∀ s,
      Integrable (correctionAt ctx s).carrierFn volume := by
    intro s
    rcases (correctionAt_support_pairwiseDisjoint ctx).1 s with
      ⟨_, _, _, _, h, _⟩
    exact h
  have hfInt : ∀ s, Integrable (f s) volume := fun s =>
    (hcarrierInt s).mul_bdd heMeas heBound
  have hfNorm : Summable (fun s => ∫ x : RealVec d, ‖f s x‖) := by
    convert correction_l1Norm_summable ctx using 1
    funext s
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    dsimp [f, e, fourierChar]
    rw [norm_mul, Complex.norm_exp]
    norm_num
  have hsum := hasSum_integral_of_summable_integral_norm hfInt hfNorm
  have htarget : (∫ x : RealVec d, ∑' s, f s x) =
      inverseSample (assembledCarrierFunction ctx) xi -
        inverseSample ctx.seed.G0 xi := by
    have hassembled : Integrable
        (fun x => assembledCarrierFunction ctx x * e x) volume :=
      (assembledCarrier_integrable ctx).mul_bdd heMeas heBound
    have hseed : Integrable (fun x => ctx.seed.G0 x * e x) volume :=
      ctx.seed.G0_integrable.mul_bdd heMeas heBound
    calc
      (∫ x : RealVec d, ∑' s, f s x) =
          ∫ x : RealVec d,
            (assembledCarrierFunction ctx x - ctx.seed.G0 x) * e x := by
        apply integral_congr_ae
        apply Filter.Eventually.of_forall
        intro x
        change (∑' s, f s x) =
          (assembledCarrierFunction ctx x - ctx.seed.G0 x) * e x
        rw [show (∑' s, f s x) =
            (∑' s, (correctionAt ctx s).carrierFn x) * e x by
          simpa [f] using
            (tsum_mul_right :
              (∑' s, (correctionAt ctx s).carrierFn x * e x) =
                (∑' s, (correctionAt ctx s).carrierFn x) * e x)]
        simp [assembledCarrierFunction]
      _ = (∫ x : RealVec d, assembledCarrierFunction ctx x * e x) -
          ∫ x : RealVec d, ctx.seed.G0 x * e x := by
        simpa [sub_mul] using integral_sub hassembled hseed
      _ = inverseSample (assembledCarrierFunction ctx) xi -
          inverseSample ctx.seed.G0 xi := by
        simp [inverseSample, inverseSampleOn, e]
  rw [← htarget]
  simpa only [inverseSample, inverseSampleOn, Measure.restrict_univ, f, e] using hsum

/-!
`inverseSample_assembledCarrier_eq`. Dependency: `inverseSample_corrections_hasSum`.
Proof idea: rearrange `HasSum.tsum_eq`, retaining the positive Fourier sign.
-/
theorem inverseSample_assembledCarrier_eq
    (ctx : ConstructionContext d hd delta hdelta mu0 hmu0 hmu01)
    (xi : RealVec d) :
    inverseSample (assembledCarrierFunction ctx) xi =
      inverseSample ctx.seed.G0 xi +
        ∑' s, inverseSample (correctionAt ctx s).carrierFn xi := by
  have hsum := (inverseSample_corrections_hasSum ctx xi).tsum_eq
  rw [hsum]
  ring

/- Proof idea: split exhaustively into actual integral, central nonintegral,
outside-central early, and corrected-tail cases. -/
theorem assembledWitness_samples_zero
    (ctx : ConstructionContext d hd delta hdelta mu0 hmu0 hmu01)
    (n : IntVec d) :
    inverseSample (assembledWitness ctx) (frequency delta n) = 0 := by
  classical
  by_cases hintegral : IsIntegralVector (frequency delta n)
  · obtain ⟨m, hm⟩ := hintegral
    rw [assembledWitness, hm]
    exact (inverseSample_firstCoordinateDifference hd
      (assembledCarrier_integrable ctx) (integerEmbed m)).2 m
  have hcarrierZero :
      inverseSample (assembledCarrierFunction ctx) (frequency delta n) = 0 := by
    by_cases hncentral : n ∈ ctx.data.C0
    · have hseed : inverseSample ctx.seed.G0 (frequency delta n) = 0 := by
        apply ctx.seed.G0_samples_zero n
        simp [seedException, exceptionalFinset, hncentral, hintegral]
      have hcorrection : ∀ s,
          inverseSample (correctionAt ctx s).carrierFn (frequency delta n) = 0 := by
        intro s
        exact (correctionAt_earlier_and_exception_zero ctx).2 s n hncentral
      rw [inverseSample_assembledCarrier_eq ctx, hseed]
      have hzero : (fun s =>
          inverseSample (correctionAt ctx s).carrierFn (frequency delta n)) =
          fun _ : Nat => (0 : Complex) := by
        funext s
        exact hcorrection s
      rw [hzero, tsum_zero]
      simp
    · have hnzero : delta n ≠ 0 := by
        intro hzero
        apply hintegral
        refine ⟨n, ?_⟩
        ext i
        simp [frequency, integerEmbed, hzero]
      have hsmall : ‖delta n‖ < (1 / 8 : Real) := by
        have hpert : ‖frequency delta n - integerEmbed n‖ ≤ perturbRadius d := by
          simpa [ctx.data.nu_outside n hncentral] using ctx.data.perturb_le n
        have hdiff : frequency delta n - integerEmbed n = delta n := by
          ext i
          simp [frequency, integerEmbed]
        rw [hdiff] at hpert
        have hdR : (1 : Real) ≤ (d : Real) := by exact_mod_cast hd
        have hpiD : (2 : Real) ≤ Real.pi * (d : Real) := by
          calc
            (2 : Real) = 2 * 1 := by ring
            _ ≤ Real.pi * (d : Real) :=
              mul_le_mul Real.two_le_pi hdR (by norm_num) Real.pi_pos.le
        have hradius : perturbRadius d < (1 / 8 : Real) := by
          rw [perturbRadius]
          have hden : 0 < 16 * Real.pi * (d : Real) := by positivity
          rw [div_lt_div_iff₀ hden (by norm_num : (0 : Real) < 8)]
          nlinarith
        exact hpert.trans_lt hradius
      obtain ⟨p, hp, _⟩ :=
        (coordinateBlocks_partition hd hdelta ctx.data.C0).2.2.2
          n hncentral hnzero hsmall
      let j : Nat := p.1
      have hj3 : 3 ≤ j := hp.1
      have hnblock : n ∈ dyadicBlock delta hdelta ctx.data.C0 j :=
        (mem_coordinateBlock_iff.mp hp.2).choose
      by_cases hjearly : j < ctx.threshold.J
      · have hseed : inverseSample ctx.seed.G0 (frequency delta n) = 0 := by
          apply ctx.seed.G0_samples_zero n
          rw [seedException]
          apply Finset.mem_union_right
          apply Finset.mem_biUnion.mpr
          refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjearly, hj3⟩, ?_⟩
          exact Finset.mem_filter.mpr ⟨hnblock, hintegral⟩
        have hcorrection : ∀ s,
            inverseSample (correctionAt ctx s).carrierFn
              (frequency delta n) = 0 := by
          intro s
          exact (correctionAt_trace ctx s).2.2 j hj3 (by
            have hJ3 : 3 ≤ ctx.threshold.J :=
              (le_max_left 3 ctx.exceptionalConstants.jSep).trans
                ctx.threshold.J_ge
            omega) (by omega) n hnblock
        rw [inverseSample_assembledCarrier_eq ctx, hseed]
        have hzero : (fun s =>
            inverseSample (correctionAt ctx s).carrierFn (frequency delta n)) =
            fun _ : Nat => (0 : Complex) := by
          funext s
          exact hcorrection s
        rw [hzero, tsum_zero]
        simp
      · have hjlate : ctx.threshold.J ≤ j := Nat.le_of_not_gt hjearly
        obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_le hjlate
        have hnblock' : n ∈ dyadicBlock delta hdelta ctx.data.C0
            (ctx.threshold.J + s) := by
          simpa [j, hs] using hnblock
        have hcurrent := (correctionAt_trace ctx s).2.1 ⟨n, hnblock'⟩
        have hlater : ∀ k ∉ Finset.range (s + 1),
            inverseSample (correctionAt ctx k).carrierFn
              (frequency delta n) = 0 := by
          intro k hk
          have hsk : s < k := by
            simpa [Finset.mem_range, not_lt] using hk
          exact (correctionAt_earlier_and_exception_zero ctx).1
            s k hsk n hnblock'
        rw [inverseSample_assembledCarrier_eq ctx, tsum_eq_sum hlater]
        exact hcurrent
  rw [assembledWitness,
    (inverseSample_firstCoordinateDifference hd
      (assembledCarrier_integrable ctx) (frequency delta n)).1,
    hcarrierZero]
  simp

end Internal

/-!
`SmallAnnihilatorHD`. Dependency: `AESupportedIn`.
Complete constructive output consumed by the noncompleteness bridge.
-/
structure SmallAnnihilatorHD {d : Nat}
    (delta : IntVec d → RealVec d) (mu : Real) where
  S : Set (RealVec d)
  S_measurable : MeasurableSet S
  F : RealVec d → Complex
  F_stronglyMeasurable : AEStronglyMeasurable F volume
  F_integrable : Integrable F volume
  F_memLp : MemLp F (2 : ENNReal) volume
  F_supported : AESupportedIn F S
  measure_lt : volume S < ENNReal.ofReal mu
  F_ae_ne_zero : ¬ F =ᵐ[volume] (0 : RealVec d → Complex)
  samples_zero : ∀ n : IntVec d,
    inverseSample F (frequency delta n) = 0

/-!
`SmallAnnihilatorHD.measure_ne_top`. Dependency: `SmallAnnihilatorHD`.
The strict measure budget yields the separate finite-measure witness.
-/
theorem SmallAnnihilatorHD.measure_ne_top {d : Nat}
    {delta : IntVec d → RealVec d} {mu : Real}
    (W : SmallAnnihilatorHD delta mu) : volume W.S ≠ ∞ := by
  exact ne_top_of_lt W.measure_lt

namespace Internal

/-!
This constructor packages the unique assembled set and function from one
completed context; it performs no new choice.
-/
noncomputable def constructionContext_toSmallAnnihilatorHD
    {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d}
    {hdelta : TendsToZeroAtIntVecInfinity delta}
    {mu0 : Real} {hmu0 : 0 < mu0} {hmu01 : mu0 < 1}
    (ctx : ConstructionContext d hd delta hdelta mu0 hmu0 hmu01) :
    SmallAnnihilatorHD delta mu0 := by
  rcases assembledWitness_support_integrability ctx with
    ⟨hSmeas, hFmeas, hFint, hFLp, hFsupp,
      hmeasure, hbudget, hstrict⟩
  exact
    { S := witnessCarrier ctx
      S_measurable := hSmeas
      F := assembledWitness ctx
      F_stronglyMeasurable := hFmeas
      F_integrable := hFint
      F_memLp := hFLp
      F_supported := hFsupp
      measure_lt := lt_of_le_of_lt (hmeasure.trans hbudget) hstrict
      F_ae_ne_zero := assembledWitness_ne_zero ctx
      samples_zero := assembledWitness_samples_zero ctx }

end Internal

/-!
Choose `mu0 = min (mu/2) (1/2)`, build exactly one context, package it, and
weaken only the strict measure field to the caller's budget.
-/
noncomputable def exists_small_annihilator_hd
    (d : Nat) (hd : 0 < d)
    (delta : IntVec d → RealVec d)
    (hdelta : TendsToZeroAtIntVecInfinity delta)
    (mu : Real) (hmu : 0 < mu) :
    SmallAnnihilatorHD delta mu := by
  let mu0 : Real := min (mu / 2) (1 / 2)
  have hmu0 : 0 < mu0 := by
    dsimp [mu0]
    exact lt_min (by linarith) (by norm_num)
  have hmu01 : mu0 < 1 := by
    exact lt_of_le_of_lt (min_le_right (mu / 2) (1 / 2)) (by norm_num)
  have hmu0mu : mu0 < mu := by
    exact lt_of_le_of_lt (min_le_left (mu / 2) (1 / 2)) (by linarith)
  let ctx := Internal.constructionContext
    d hd delta hdelta mu0 hmu0 hmu01
  let W := Internal.constructionContext_toSmallAnnihilatorHD ctx
  exact
    { S := W.S
      S_measurable := W.S_measurable
      F := W.F
      F_stronglyMeasurable := W.F_stronglyMeasurable
      F_integrable := W.F_integrable
      F_memLp := W.F_memLp
      F_supported := W.F_supported
      measure_lt := W.measure_lt.trans_le
        (ENNReal.ofReal_le_ofReal (le_of_lt hmu0mu))
      F_ae_ne_zero := W.F_ae_ne_zero
      samples_zero := W.samples_zero }

end AsymptoticallyIntegerHD
