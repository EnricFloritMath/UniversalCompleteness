import AsymptoticallyIntegerHD.Definitions
import AsymptoticallyIntegerHD.DyadicBlocks
import AsymptoticallyIntegerHD.BlockMultipliers
import AsymptoticallyIntegerHD.FrequencyCarriers
import AsymptoticallyIntegerHD.BlockCorrection

/-!
# Compactly supported smooth seed and its first-coordinate difference

The finite exception set, root polynomial, Schwartz representative, energy
total, and witness carrier are constructed and analyzed below.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Pointwise FourierTransform

namespace AsymptoticallyIntegerHD.Internal

/-- Central exceptions and nonintegral early-shell indices. -/
def seedException {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d}
    {hdelta : TendsToZeroAtIntVecInfinity delta}
    {data : ModifiedFrequencyData delta} {mu0 : Real}
    {K : ExponentialBoundsHD data.nu}
    {P : BlockParameters hd delta hdelta data mu0}
    {budgets : BudgetConstants P}
    {EC : ExceptionalConstants hd delta hdelta data P}
    {CC : CorrectionConstants hd data K P budgets EC}
    (threshold : BlockThreshold CC) : Finset (IntVec d) := by
  classical
  exact exceptionalFinset data ∪
    ((Finset.range threshold.J).filter fun j => 3 ≤ j).biUnion fun j =>
      (dyadicBlock delta hdelta data.C0 j).filter fun n =>
        ¬ IsIntegralVector (frequency delta n)

/-- Exact first-axis translation and root-polynomial data. -/
structure SeedTranslationParameters {d : Nat} (hd : 0 < d)
    {delta : IntVec d → RealVec d}
    {hdelta : TendsToZeroAtIntVecInfinity delta}
    {data : ModifiedFrequencyData delta} {mu0 : Real}
    {K : ExponentialBoundsHD data.nu}
    {P : BlockParameters hd delta hdelta data mu0}
    {budgets : BudgetConstants P}
    {EC : ExceptionalConstants hd delta hdelta data P}
    {CC : CorrectionConstants hd data K P budgets EC}
    (threshold : BlockThreshold CC) where
  A : Finset (IntVec d)
  A_eq : A = seedException threshold
  h : Real
  h_eq : h = mu0 / (32 * (A.card + 1 : Nat))
  w : Real
  w_eq : w = h / 2
  h_pos : 0 < h
  w_pos : 0 < w
  w_lt_h : w < h
  p : Polynomial Complex
  p_eq : p = ∏ a ∈ A,
    (Polynomial.X - Polynomial.C
      (fourierChar (frequency delta a)
        (h • basisVector (firstCoordinate hd))))
  p_root : ∀ a ∈ A,
    p.eval (fourierChar (frequency delta a)
      (h • basisVector (firstCoordinate hd))) = 0
  p_monic : p.Monic
  p_natDegree_le : p.natDegree ≤ A.card
  p_support_card_le : p.support.card ≤ A.card + 1

/-- Existence certificate for the exact first-axis translation data. -/
theorem seedTranslationParameters_nonempty {d : Nat} (hd : 0 < d)
    {delta : IntVec d → RealVec d}
    {hdelta : TendsToZeroAtIntVecInfinity delta}
    {data : ModifiedFrequencyData delta} {mu0 : Real}
    {K : ExponentialBoundsHD data.nu}
    {P : BlockParameters hd delta hdelta data mu0}
    {budgets : BudgetConstants P}
    {EC : ExceptionalConstants hd delta hdelta data P}
    {CC : CorrectionConstants hd data K P budgets EC}
    (threshold : BlockThreshold CC) :
    Nonempty (SeedTranslationParameters hd threshold) := by
  classical
  let A := seedException threshold
  let h : Real := mu0 / (32 * (A.card + 1 : Nat))
  let w : Real := h / 2
  let p : Polynomial Complex := ∏ a ∈ A,
    (Polynomial.X - Polynomial.C
      (fourierChar (frequency delta a)
        (h • basisVector (firstCoordinate hd))))
  have hh : 0 < h := by
    dsimp [h]
    exact div_pos P.mu0_pos (by positivity)
  have hpmonic : p.Monic := by
    dsimp [p]
    exact Polynomial.monic_prod_of_monic A _
      (fun a ha ↦ Polynomial.monic_X_sub_C _)
  have hpdegree : p.natDegree ≤ A.card := by
    rw [show p = ∏ a ∈ A,
      (Polynomial.X - Polynomial.C
        (fourierChar (frequency delta a)
          (h • basisVector (firstCoordinate hd)))) from rfl,
      Polynomial.natDegree_finsetProd_X_sub_C_eq_card]
  refine ⟨
    { A := A
      A_eq := rfl
      h := h
      h_eq := rfl
      w := w
      w_eq := rfl
      h_pos := hh
      w_pos := by dsimp [w]; positivity
      w_lt_h := by dsimp [w]; linarith
      p := p
      p_eq := rfl
      p_root := ?_
      p_monic := hpmonic
      p_natDegree_le := hpdegree
      p_support_card_le := ?_ }⟩
  · intro a ha
    dsimp [p]
    simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C]
    apply Finset.prod_eq_zero ha
    ring
  · exact (Polynomial.card_supp_le_succ_natDegree p).trans
      (Nat.add_le_add_right hpdegree 1)

/-- Concrete data constructor belonging to `SeedTranslationParameters`. -/
noncomputable def seedTranslationData {d : Nat} (hd : 0 < d)
    {delta : IntVec d → RealVec d}
    {hdelta : TendsToZeroAtIntVecInfinity delta}
    {data : ModifiedFrequencyData delta} {mu0 : Real}
    {K : ExponentialBoundsHD data.nu}
    {P : BlockParameters hd delta hdelta data mu0}
    {budgets : BudgetConstants P}
    {EC : ExceptionalConstants hd delta hdelta data P}
    {CC : CorrectionConstants hd data K P budgets EC}
    (threshold : BlockThreshold CC) : SeedTranslationParameters hd threshold :=
  Classical.choice (seedTranslationParameters_nonempty hd threshold)

/-- One literal smooth seed and all of its analytic data. -/
structure SeedData {d : Nat} (hd : 0 < d)
    {delta : IntVec d → RealVec d}
    {hdelta : TendsToZeroAtIntVecInfinity delta}
    {data : ModifiedFrequencyData delta} {mu0 : Real}
    {K : ExponentialBoundsHD data.nu}
    (P : BlockParameters hd delta hdelta data mu0)
    {budgets : BudgetConstants P}
    {EC : ExceptionalConstants hd delta hdelta data P}
    {CC : CorrectionConstants hd data K P budgets EC}
    (threshold : BlockThreshold CC) where
  translation : SeedTranslationParameters hd threshold
  Phi : RealVec d → Complex
  Phi_contDiff : ContDiff Real (↑(⊤ : ℕ∞)) Phi
  Phi_hasCompactSupport : HasCompactSupport Phi
  Phi_tsupport_subset : tsupport Phi ⊆
    {x | 0 < x (firstCoordinate hd) ∧
      x (firstCoordinate hd) < translation.w}
  Phi_ne_zero : Phi ≠ 0
  Phi_ae_ne_zero : ¬ Phi =ᵐ[volume] (0 : RealVec d → Complex)
  G0 : RealVec d → Complex
  G0_eq : G0 = axisPolynomialCarrierAtStep hd translation.h translation.p Phi
  G0_contDiff : ContDiff Real (↑(⊤ : ℕ∞)) G0
  G0_hasCompactSupport : HasCompactSupport G0
  A0 : Set (RealVec d)
  A0_measurable : MeasurableSet A0
  A0_subset : A0 ⊆ {x | 0 < x (firstCoordinate hd) ∧
    x (firstCoordinate hd) < mu0 / 8}
  volume_A0_lt : volume A0 < ENNReal.ofReal (mu0 / 8)
  G0_tsupport_subset : tsupport G0 ⊆ A0
  G0_stronglyMeasurable : AEStronglyMeasurable G0 volume
  G0_integrable : Integrable G0 volume
  G0_memLp : MemLp G0 (2 : ENNReal) volume
  G0_supported : AESupportedIn G0 A0
  G0_ae_ne_zero : ¬ G0 =ᵐ[volume] (0 : RealVec d → Complex)
  G0_samples_zero : ∀ n ∈ seedException threshold,
    inverseSample G0 (frequency delta n) = 0

/-- Existence certificate for the smooth product-bump seed. -/
theorem seedData_nonempty {d : Nat} (hd : 0 < d)
    {delta : IntVec d → RealVec d}
    {hdelta : TendsToZeroAtIntVecInfinity delta}
    {data : ModifiedFrequencyData delta} {mu0 : Real}
    {K : ExponentialBoundsHD data.nu}
    (P : BlockParameters hd delta hdelta data mu0)
    {budgets : BudgetConstants P}
    {EC : ExceptionalConstants hd delta hdelta data P}
    {CC : CorrectionConstants hd data K P budgets EC}
    (threshold : BlockThreshold CC) : Nonempty (SeedData hd P threshold) := by
  classical
  let tr := seedTranslationData hd threshold
  let center : RealVec d :=
    (tr.w / 2) • basisVector (firstCoordinate hd)
  let bump : ContDiffBump center :=
    ⟨tr.w / 8, tr.w / 4, div_pos tr.w_pos (by norm_num),
      by linarith [tr.w_pos]⟩
  let Phi : RealVec d → Complex := fun x ↦ (bump x : Complex)
  let Omega : Set (RealVec d) := Metric.closedBall center (tr.w / 4)
  let G0 : RealVec d → Complex :=
    axisPolynomialCarrierAtStep hd tr.h tr.p Phi
  let carrier : Set (RealVec d) :=
    axisPolynomialCarrierSet hd tr.h tr.p Omega
  have hPhiSmooth : ContDiff Real (↑(⊤ : ℕ∞)) Phi := by
    exact Complex.ofRealCLM.contDiff.comp bump.contDiff
  have hPhiTsupp : tsupport Phi = Omega := by
    change closure (Function.support fun x : RealVec d ↦ (bump x : Complex)) = _
    rw [show Function.support (fun x : RealVec d ↦ (bump x : Complex)) =
        Function.support bump by ext x; simp [Function.mem_support]]
    exact bump.tsupport_eq
  have hPhiCompact : HasCompactSupport Phi := by
    rw [HasCompactSupport, hPhiTsupp]
    exact isCompact_closedBall _ _
  have hOmegaCoord : Omega ⊆
      {x | tr.w / 4 ≤ x (firstCoordinate hd) ∧
        x (firstCoordinate hd) ≤ 3 * tr.w / 4} := by
    intro x hx
    have hxball : dist x center ≤ tr.w / 4 := by
      simpa only [Omega, Metric.mem_closedBall] using hx
    have hquarter : 0 ≤ tr.w / 4 := div_nonneg tr.w_pos.le (by norm_num)
    have hxcoord : dist (x (firstCoordinate hd)) (center (firstCoordinate hd)) ≤
        tr.w / 4 :=
      ((dist_pi_le_iff hquarter).mp hxball)
        (firstCoordinate hd)
    have hcenter : center (firstCoordinate hd) = tr.w / 2 := by
      simp [center, basisVector_apply]
    rw [hcenter, Real.dist_eq] at hxcoord
    have habs := abs_le.mp hxcoord
    constructor <;> nlinarith
  have hOmegaSubH : Omega ⊆
      {x | 0 < x (firstCoordinate hd) ∧
        x (firstCoordinate hd) < tr.h} := by
    intro x hx
    rcases hOmegaCoord hx with ⟨hxl, hxu⟩
    constructor
    · nlinarith [tr.w_pos]
    · nlinarith [tr.w_pos, tr.w_lt_h]
  have hOmegaSubW : Omega ⊆
      {x | 0 < x (firstCoordinate hd) ∧
        x (firstCoordinate hd) < tr.w} := by
    intro x hx
    rcases hOmegaCoord hx with ⟨hxl, hxu⟩
    constructor <;> nlinarith [tr.w_pos]
  have hPhiSub : tsupport Phi ⊆
      {x | 0 < x (firstCoordinate hd) ∧
        x (firstCoordinate hd) < tr.w} := by
    rw [hPhiTsupp]
    exact hOmegaSubW
  have hPhiNe : Phi ≠ 0 := by
    intro hz
    have hz' := congr_fun hz center
    have hone : bump center = 1 :=
      bump.one_of_mem_closedBall (Metric.mem_closedBall_self bump.rIn_pos.le)
    simp [Phi, hone] at hz'
  have hPhiAeNe : ¬ Phi =ᵐ[volume] (0 : RealVec d → Complex) := by
    intro hae
    apply hPhiNe
    exact (hPhiSmooth.continuous.ae_eq_iff_eq volume continuous_zero).mp hae
  have hPhiMeas : AEStronglyMeasurable Phi volume :=
    hPhiSmooth.continuous.aestronglyMeasurable
  have hPhiInt : Integrable Phi volume :=
    hPhiSmooth.continuous.integrable_of_hasCompactSupport hPhiCompact
  have hPhiLp : MemLp Phi (2 : ENNReal) volume :=
    hPhiSmooth.continuous.memLp_of_hasCompactSupport hPhiCompact
  have hPhiSupported : AESupportedIn Phi Omega := by
    filter_upwards [] with x
    intro hx
    apply image_eq_zero_of_notMem_tsupport
    intro hts
    exact hx (hPhiTsupp ▸ hts)
  have hgeo := axisPolynomialCarrier_geometry hd tr.h tr.h_pos tr.p
    measurableSet_closedBall hPhiInt hPhiLp hPhiSupported
    ⟨0, tr.w, by simpa using tr.w_lt_h, hOmegaSubW⟩
  have hG0Smooth : ContDiff Real (↑(⊤ : ℕ∞)) G0 := by
    change ContDiff Real (↑(⊤ : ℕ∞))
      (fun x : RealVec d ↦ ∑ k ∈ tr.p.support,
        tr.p.coeff k * Phi (x -
          ((k : Real) * tr.h) • basisVector (firstCoordinate hd)))
    fun_prop
  have hG0Compact : HasCompactSupport G0 := by
    have hterms : ∀ k ∈ tr.p.support,
        HasCompactSupport (fun x : RealVec d ↦ tr.p.coeff k *
          vectorTranslate (((k : Real) * tr.h) •
            basisVector (firstCoordinate hd)) Phi x) := by
      intro k hk
      have ht : HasCompactSupport (vectorTranslate
          (((k : Real) * tr.h) • basisVector (firstCoordinate hd)) Phi) := by
        change HasCompactSupport (Phi ∘ Homeomorph.subRight
          (((k : Real) * tr.h) • basisVector (firstCoordinate hd)))
        exact hPhiCompact.comp_homeomorph _
      exact ht.mul_left
    have hs := HasCompactSupport.finset_sum hterms
    rw [show G0 = axisPolynomialCarrierAtStep hd tr.h tr.p Phi from rfl]
    rw [show axisPolynomialCarrierAtStep hd tr.h tr.p Phi =
        ∑ k ∈ tr.p.support, fun x : RealVec d ↦ tr.p.coeff k *
          vectorTranslate (((k : Real) * tr.h) •
            basisVector (firstCoordinate hd)) Phi x by
      funext x
      simp only [axisPolynomialCarrierAtStep, Finset.sum_apply]]
    exact hs
  have hcarrierClosed : IsClosed carrier := by
    dsimp [carrier, axisPolynomialCarrierSet]
    apply isClosed_biUnion_finset
    intro k hk
    simpa [Omega, Metric.vadd_closedBall, vadd_eq_add] using
      (Metric.isClosed_closedBall : IsClosed (Metric.closedBall
        ((((k : Real) * tr.h) • basisVector (firstCoordinate hd)) + center)
        (tr.w / 4)))
  have hcarrierSub : carrier ⊆
      {x | 0 < x (firstCoordinate hd) ∧
        x (firstCoordinate hd) < mu0 / 8} := by
    intro x hx
    dsimp [carrier, axisPolynomialCarrierSet] at hx
    rcases Set.mem_iUnion.mp hx with ⟨k, hx⟩
    rcases Set.mem_iUnion.mp hx with ⟨hkSupp, hx⟩
    rcases Set.mem_vadd_set.mp hx with ⟨u, hu, hux⟩
    have huI := hOmegaSubH hu
    have hkdeg : k ≤ tr.p.natDegree :=
      Polynomial.le_natDegree_of_mem_supp k hkSupp
    have hkcard : k ≤ tr.A.card := hkdeg.trans tr.p_natDegree_le
    have hkcardR : (k : Real) ≤ (tr.A.card : Real) := by
      exact_mod_cast hkcard
    have hscale : ((tr.A.card : Real) + 1) * tr.h = mu0 / 32 := by
      rw [tr.h_eq]
      push_cast
      field_simp
    change (((k : Real) * tr.h) • basisVector (firstCoordinate hd)) + u = x at hux
    have hcoord := congr_fun hux (firstCoordinate hd)
    simp [basisVector_apply] at hcoord
    constructor
    · have hk0 : 0 ≤ (k : Real) * tr.h :=
        mul_nonneg (Nat.cast_nonneg k) tr.h_pos.le
      nlinarith [huI.1]
    · have hkMul : (k : Real) * tr.h ≤ (tr.A.card : Real) * tr.h :=
        mul_le_mul_of_nonneg_right hkcardR tr.h_pos.le
      nlinarith [huI.2, P.mu0_pos]
  have hG0SupportCarrier : Function.support G0 ⊆ carrier := by
    intro x hx
    by_contra hxout
    apply hx
    dsimp [G0, axisPolynomialCarrierAtStep]
    apply Finset.sum_eq_zero
    intro k hk
    have hzero : vectorTranslate (((k : Real) * tr.h) •
        basisVector (firstCoordinate hd)) Phi x = 0 := by
      dsimp [vectorTranslate]
      apply image_eq_zero_of_notMem_tsupport
      intro hts
      have hu : x - (((k : Real) * tr.h) •
          basisVector (firstCoordinate hd)) ∈ Omega := hPhiTsupp ▸ hts
      apply hxout
      dsimp [carrier, axisPolynomialCarrierSet]
      apply Set.mem_iUnion.mpr
      refine ⟨k, ?_⟩
      apply Set.mem_iUnion.mpr
      refine ⟨hk, ?_⟩
      apply Set.mem_vadd_set.mpr
      refine ⟨x - (((k : Real) * tr.h) •
        basisVector (firstCoordinate hd)), hu, ?_⟩
      simp only [vadd_eq_add]
      abel
    rw [hzero, mul_zero]
  have hG0TsuppCarrier : tsupport G0 ⊆ carrier := by
    rw [tsupport]
    exact hcarrierClosed.closure_subset_iff.mpr hG0SupportCarrier
  have hvolume : volume carrier < ENNReal.ofReal (mu0 / 8) := by
    have ht0 : 0 ≤ tr.w / 2 := div_nonneg tr.w_pos.le (by norm_num)
    have ht1 : tr.w / 2 ≤ 1 := by
      have hhmu : tr.h < 1 := by
        rw [tr.h_eq]
        have hcard1 : (1 : Real) ≤ (tr.A.card + 1 : Nat) := by
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le tr.A.card)
        have hden : 1 ≤ (32 : Real) * (tr.A.card + 1 : Nat) := by nlinarith
        exact (div_lt_one (mul_pos (by norm_num) (by positivity))).mpr
          (P.mu0_lt_one.trans_le hden)
      linarith [tr.w_lt_h]
    have hpow : (tr.w / 2) ^ d ≤ tr.w / 2 :=
      pow_le_of_le_one ht0 ht1 (Nat.ne_zero_of_lt hd)
    have hreal : (tr.p.support.card : Real) * (tr.w / 2) ^ d < mu0 / 8 := by
      have hcard : (tr.p.support.card : Real) ≤ tr.A.card + 1 := by
        exact_mod_cast tr.p_support_card_le
      have hscale : ((tr.A.card : Real) + 1) * tr.h = mu0 / 32 := by
        rw [tr.h_eq]
        push_cast
        field_simp
      have hm := mul_le_mul hcard hpow (pow_nonneg ht0 d) (by positivity)
      have hw : tr.w = tr.h / 2 := tr.w_eq
      rw [hw] at hm
      nlinarith [P.mu0_pos]
    calc
      volume carrier ≤ tr.p.support.card * volume Omega := hgeo.2.2.2.1
      _ = ENNReal.ofReal
          ((tr.p.support.card : Real) * (tr.w / 2) ^ d) := by
        rw [show Omega = Metric.closedBall center (tr.w / 4) from rfl,
          Real.volume_pi_closedBall center
            (div_nonneg tr.w_pos.le (by norm_num))]
        have hbase : 2 * (tr.w / 4) = tr.w / 2 := by ring
        rw [hbase, Fintype.card_fin, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      _ < ENNReal.ofReal (mu0 / 8) :=
        (ENNReal.ofReal_lt_ofReal_iff
          (div_pos P.mu0_pos (by norm_num))).2 hreal
  have hG0AeNe : ¬ G0 =ᵐ[volume] (0 : RealVec d → Complex) := by
    have hcoeff : 0 < ∑ k ∈ tr.p.support, ‖tr.p.coeff k‖ ^ 2 := by
      have hpmem : tr.p.natDegree ∈ tr.p.support :=
        Polynomial.natDegree_mem_support_of_nonzero tr.p_monic.ne_zero
      have hle : ‖tr.p.coeff tr.p.natDegree‖ ^ 2 ≤
          ∑ k ∈ tr.p.support, ‖tr.p.coeff k‖ ^ 2 := by
        exact Finset.single_le_sum (s := tr.p.support)
          (f := fun k ↦ ‖tr.p.coeff k‖ ^ 2) (fun k hk ↦ sq_nonneg _) hpmem
      rw [tr.p_monic.coeff_natDegree, norm_one, one_pow] at hle
      linarith
    have hPhiNorm : 0 < sqNormOn Set.univ Phi := by
      rw [sqNormOn, setIntegral_univ]
      have hint : Integrable (fun x : RealVec d ↦ ‖Phi x‖ ^ 2) volume :=
        hPhiLp.integrable_norm_pow (by norm_num)
      have hnonneg : 0 ≤ ∫ x : RealVec d, ‖Phi x‖ ^ 2 :=
        integral_nonneg (fun x ↦ sq_nonneg _)
      refine lt_of_le_of_ne hnonneg ?_
      intro heq
      apply hPhiAeNe
      have hae : (fun x : RealVec d ↦ ‖Phi x‖ ^ 2) =ᵐ[volume]
          (0 : RealVec d → Real) :=
        (integral_eq_zero_iff_of_nonneg_ae
          (Filter.Eventually.of_forall (fun x ↦ sq_nonneg _)) hint).mp heq.symm
      filter_upwards [hae] with x hx
      have hx' : ‖Phi x‖ ^ 2 = 0 := by simpa only [Pi.zero_apply] using hx
      have hn : ‖Phi x‖ = 0 := by nlinarith [norm_nonneg (Phi x)]
      exact norm_eq_zero.mp hn
    have hG0Norm : 0 < sqNormOn Set.univ G0 := by
      rw [hgeo.2.2.2.2.2.2]
      positivity
    intro hae
    have hzero : sqNormOn Set.univ G0 = 0 := by
      rw [sqNormOn, setIntegral_univ]
      apply integral_eq_zero_of_ae
      filter_upwards [hae] with x hx
      simp only [Pi.zero_apply, hx, norm_zero,
        zero_pow (by norm_num : (2 : Nat) ≠ 0)]
    linarith
  refine ⟨
    { translation := tr
      Phi := Phi
      Phi_contDiff := hPhiSmooth
      Phi_hasCompactSupport := hPhiCompact
      Phi_tsupport_subset := hPhiSub
      Phi_ne_zero := hPhiNe
      Phi_ae_ne_zero := hPhiAeNe
      G0 := G0
      G0_eq := rfl
      G0_contDiff := hG0Smooth
      G0_hasCompactSupport := hG0Compact
      A0 := carrier
      A0_measurable := hgeo.1
      A0_subset := hcarrierSub
      volume_A0_lt := hvolume
      G0_tsupport_subset := hG0TsuppCarrier
      G0_stronglyMeasurable := hG0Smooth.continuous.aestronglyMeasurable
      G0_integrable := hgeo.2.2.2.2.1
      G0_memLp := hgeo.2.2.2.2.2.1
      G0_supported := hgeo.2.2.1
      G0_ae_ne_zero := hG0AeNe
      G0_samples_zero := ?_ }⟩
  intro n hn
  rw [show G0 = axisPolynomialCarrierAtStep hd tr.h tr.p Phi from rfl]
  rw [inverseSample_axisPolynomialCarrierAtStep hd tr.h tr.p hPhiInt]
  rw [tr.p_root n (by simpa [tr.A_eq] using hn), zero_mul]

/-- Construct the smooth product-bump seed. -/
noncomputable def seedData {d : Nat} (hd : 0 < d)
    {delta : IntVec d → RealVec d}
    {hdelta : TendsToZeroAtIntVecInfinity delta}
    {data : ModifiedFrequencyData delta} {mu0 : Real}
    {K : ExponentialBoundsHD data.nu}
    (P : BlockParameters hd delta hdelta data mu0)
    {budgets : BudgetConstants P}
    {EC : ExceptionalConstants hd delta hdelta data P}
    {CC : CorrectionConstants hd data K P budgets EC}
    (threshold : BlockThreshold CC) : SeedData hd P threshold :=
  Classical.choice (seedData_nonempty hd P threshold)

/-- Schwartz representative of the exact stored `G0`. -/
def seedSchwartz {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d}
    {hdelta : TendsToZeroAtIntVecInfinity delta}
    {data : ModifiedFrequencyData delta} {mu0 : Real}
    {K : ExponentialBoundsHD data.nu}
    {P : BlockParameters hd delta hdelta data mu0}
    {budgets : BudgetConstants P}
    {EC : ExceptionalConstants hd delta hdelta data P}
    {CC : CorrectionConstants hd data K P budgets EC}
    {threshold : BlockThreshold CC}
    (seed : SeedData hd P threshold) : SchwartzMap (EuclideanVec d) Complex :=
  (hasCompactSupport_comp_fromEuclidean seed.G0_hasCompactSupport).toSchwartzMap
    (contDiff_comp_fromEuclidean seed.G0_contDiff)

/-- Coercion of the Schwartz seed is pointwise literal. -/
@[simp] theorem seedSchwartz_apply {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d}
    {hdelta : TendsToZeroAtIntVecInfinity delta}
    {data : ModifiedFrequencyData delta} {mu0 : Real}
    {K : ExponentialBoundsHD data.nu}
    {P : BlockParameters hd delta hdelta data mu0}
    {budgets : BudgetConstants P}
    {EC : ExceptionalConstants hd delta hdelta data P}
    {CC : CorrectionConstants hd data K P budgets EC}
    {threshold : BlockThreshold CC}
    (seed : SeedData hd P threshold) (z : EuclideanVec d) :
    seedSchwartz seed z = seed.G0 (fromEuclidean z) := by
  rfl

/-- Exact positive-sign Fourier-inverse normalization. -/
theorem seed_inverseSample_eq_schwartzFourierInv {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d}
    {hdelta : TendsToZeroAtIntVecInfinity delta}
    {data : ModifiedFrequencyData delta} {mu0 : Real}
    {K : ExponentialBoundsHD data.nu}
    {P : BlockParameters hd delta hdelta data mu0}
    {budgets : BudgetConstants P}
    {EC : ExceptionalConstants hd delta hdelta data P}
    {CC : CorrectionConstants hd data K P budgets EC}
    {threshold : BlockThreshold CC}
    (seed : SeedData hd P threshold) (xi : RealVec d) :
    inverseSample seed.G0 xi =
      (𝓕⁻ (seedSchwartz seed)) (toEuclidean xi) := by
  rw [inverseSample, inverseSampleOn, setIntegral_univ,
    SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
  have hchar : Continuous (fourierChar xi) := by
    unfold fourierChar
    fun_prop
  rw [← integral_comp_fromEuclidean
    (fun x : RealVec d ↦ seed.G0 x * fourierChar xi x)
    (seed.G0_integrable.mul_bdd (c := 1) hchar.aestronglyMeasurable
      (Filter.Eventually.of_forall (by
        intro x
        simp [fourierChar, Complex.norm_exp])))]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [seedSchwartz_apply, smul_eq_mul, fourierChar, fromEuclidean_apply]
  rw [real_inner_comm (toEuclidean xi) z]
  have hinner : inner Real (toEuclidean xi) z =
      (∑ i : Fin d, xi i * (fromEuclidean z) i : Real) := by
    rw [← toEuclidean_fromEuclidean z]
    exact toEuclidean_inner_eq_sum xi (fromEuclidean z)
  rw [hinner]
  simp only [fromEuclidean_apply]
  rw [mul_comm (seed.G0 (fromEuclidean z))]
  apply congrArg (fun w : Complex ↦ w * seed.G0 (fromEuclidean z))
  apply congrArg Complex.exp
  push_cast
  ring

/-- Dimension-dependent rapid inverse-sample decay. -/
theorem seed_inverseSample_decay {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d}
    {hdelta : TendsToZeroAtIntVecInfinity delta}
    {data : ModifiedFrequencyData delta} {mu0 : Real}
    {K : ExponentialBoundsHD data.nu}
    {P : BlockParameters hd delta hdelta data mu0}
    {budgets : BudgetConstants P}
    {EC : ExceptionalConstants hd delta hdelta data P}
    {CC : CorrectionConstants hd data K P budgets EC}
    {threshold : BlockThreshold CC}
    (seed : SeedData hd P threshold) :
    ∃ Cseed : Real, 0 < Cseed ∧ ∀ xi : RealVec d,
      ‖inverseSample seed.G0 xi‖ ≤
        Cseed / (1 + ‖xi‖) ^ (4 * d + 8) := by
  let q : Nat := 4 * d + 8
  let f : SchwartzMap (EuclideanVec d) Complex :=
    FourierTransform.fourierInvCLM Complex
      (SchwartzMap (EuclideanVec d) Complex) (seedSchwartz seed)
  obtain ⟨C0, hC0, hbound0⟩ := f.decay 0 0
  obtain ⟨Cq, hCq, hboundq⟩ := f.decay q 0
  refine ⟨2 ^ q * (C0 + Cq), by positivity, ?_⟩
  intro xi
  let z : EuclideanVec d := toEuclidean xi
  have hb0 : ‖f z‖ ≤ C0 := by
    simpa only [norm_iteratedFDeriv_zero, pow_zero, one_mul] using hbound0 z
  have hbq : ‖z‖ ^ q * ‖f z‖ ≤ Cq := by
    simpa only [norm_iteratedFDeriv_zero] using hboundq z
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
  have hfinal : ‖f z‖ ≤ 2 ^ q * (C0 + Cq) / (1 + ‖xi‖) ^ q := by
    have hden : 0 < (1 + ‖xi‖) ^ q := by positivity
    rw [le_div_iff₀ hden]
    by_cases hxi : ‖xi‖ ≤ 1
    · have hbase : 1 + ‖xi‖ ≤ 2 := by linarith [norm_nonneg xi]
      have hp : (1 + ‖xi‖) ^ q ≤ (2 : Real) ^ q :=
        pow_le_pow_left₀ (by positivity) hbase q
      nlinarith [norm_nonneg (f z)]
    · have hxi1 : 1 ≤ ‖xi‖ := le_of_not_ge hxi
      have hpi : ‖xi‖ ≤ ‖z‖ := piNorm_le_toEuclidean_norm xi
      have hbase : 1 + ‖xi‖ ≤ 2 * ‖z‖ := by linarith
      have hp : (1 + ‖xi‖) ^ q ≤ (2 * ‖z‖) ^ q :=
        pow_le_pow_left₀ (by positivity) hbase q
      rw [mul_pow] at hp
      have hmul := mul_le_mul_of_nonneg_left hbq
        (pow_nonneg (by norm_num : (0 : Real) ≤ 2) q)
      nlinarith [norm_nonneg (f z), pow_nonneg hz0 q]
  rw [seed_inverseSample_eq_schwartzFourierInv seed xi]
  simpa only [f, z, FourierTransform.fourierInvCLM_apply, q] using hfinal

/-- Exact total seed residual energy. -/
def seedEnergyTotal {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d}
    {hdelta : TendsToZeroAtIntVecInfinity delta}
    {data : ModifiedFrequencyData delta} {mu0 : Real}
    {K : ExponentialBoundsHD data.nu}
    {P : BlockParameters hd delta hdelta data mu0}
    {budgets : BudgetConstants P}
    {EC : ExceptionalConstants hd delta hdelta data P}
    {CC : CorrectionConstants hd data K P budgets EC}
    {threshold : BlockThreshold CC}
    (seed : SeedData hd P threshold) : Real :=
  ∑' j, blockEnergyTerm P seed.G0 j

/-- Seed energy is summable with the exact stored sum. -/
theorem seedEnergy_summable {d : Nat} {hd : 0 < d}
    {delta : IntVec d → RealVec d}
    {hdelta : TendsToZeroAtIntVecInfinity delta}
    {data : ModifiedFrequencyData delta} {mu0 : Real}
    {K : ExponentialBoundsHD data.nu}
    {P : BlockParameters hd delta hdelta data mu0}
    {budgets : BudgetConstants P}
    {EC : ExceptionalConstants hd delta hdelta data P}
    {CC : CorrectionConstants hd data K P budgets EC}
    {threshold : BlockThreshold CC}
    (seed : SeedData hd P threshold) :
    Summable (fun j => blockEnergyTerm P seed.G0 j) ∧
      0 ≤ seedEnergyTotal seed ∧
      HasSum (fun j => blockEnergyTerm P seed.G0 j) (seedEnergyTotal seed) := by
  classical
  obtain ⟨Cseed, hCseed, hdecay⟩ := seed_inverseSample_decay seed
  let q : Nat := 4 * d + 8
  let r : Nat := 2 * d + 2
  let c : Real := d + 1
  let D : Real := budgets.Ceta * c ^ (2 * q) * Cseed ^ 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hD : 0 ≤ D := by
    dsimp [D]
    exact mul_nonneg
      (mul_nonneg budgets.Ceta_pos.le (pow_nonneg hc.le _)) (sq_nonneg Cseed)
  have hradius : perturbRadius d ≤ (1 : Real) / 2 := by
    rw [perturbRadius]
    have hdR : (1 : Real) ≤ d := by exact_mod_cast hd
    have hden : 0 < 16 * Real.pi * (d : Real) := by positivity
    rw [div_le_iff₀ hden]
    nlinarith [Real.two_le_pi]
  have hsampleBudget : ∀ j n,
      3 ≤ j → n ∈ dyadicBlock delta hdelta data.C0 j →
      (1 / P.eta j) * ‖inverseSample seed.G0 (frequency delta n)‖ ^ 2 ≤
        D * indexWeight n := by
    intro j n hj hn
    have hnC0 : n ∉ data.C0 := (mem_dyadicBlock_iff.mp hn).1
    have hpert : ‖frequency delta n - integerEmbed n‖ ≤ perturbRadius d := by
      have hp := data.perturb_le n
      rw [data.nu_outside n hnC0] at hp
      exact hp
    have hindex : (indexSize n : Real) ≤
        (d : Real) * ‖integerEmbed n‖ := by
      rw [indexSize, Nat.cast_sum]
      calc
        ∑ i : Fin d, ((n i).natAbs : Real) ≤
            ∑ _i : Fin d, ‖integerEmbed n‖ := by
          apply Finset.sum_le_sum
          intro i hi
          calc
            ((n i).natAbs : Real) = ‖(integerEmbed n) i‖ := by
              simp [integerEmbed_apply, Real.norm_eq_abs]
            _ ≤ ‖integerEmbed n‖ := norm_le_pi_norm _ i
        _ = (d : Real) * ‖integerEmbed n‖ := by simp
    have hinteger : ‖integerEmbed n‖ ≤
        ‖frequency delta n‖ + perturbRadius d := by
      calc
        ‖integerEmbed n‖ =
            ‖(integerEmbed n - frequency delta n) + frequency delta n‖ := by
              congr 1
              abel
        _ ≤ ‖integerEmbed n - frequency delta n‖ +
            ‖frequency delta n‖ := norm_add_le _ _
        _ = ‖frequency delta n - integerEmbed n‖ +
            ‖frequency delta n‖ := by rw [norm_sub_rev]
        _ ≤ ‖frequency delta n‖ + perturbRadius d := by linarith
    let a : Real := 1 + indexSize n
    let b : Real := 1 + ‖frequency delta n‖
    let s : Real := ‖inverseSample seed.G0 (frequency delta n)‖
    have ha : 1 ≤ a := by
      dsimp [a]
      exact le_add_of_nonneg_right (Nat.cast_nonneg _)
    have ha0 : 0 < a := zero_lt_one.trans_le ha
    have hb0 : 0 < b := by dsimp [b]; positivity
    have hdc : (1 : Real) ≤ d := by exact_mod_cast hd
    have hab : a ≤ c * b := by
      dsimp [a, b, c]
      have hp := hpert.trans hradius
      nlinarith [norm_nonneg (frequency delta n)]
    have hsamp : s ≤ Cseed / b ^ q := by
      simpa only [s, b, q] using hdecay (frequency delta n)
    have hsMul : s * b ^ q ≤ Cseed :=
      (le_div_iff₀ (pow_pos hb0 q)).mp hsamp
    have hsMulSq : (s * b ^ q) ^ 2 ≤ Cseed ^ 2 :=
      pow_le_pow_left₀ (by positivity) hsMul 2
    have hsBig : s ^ 2 * b ^ (2 * q) ≤ Cseed ^ 2 := by
      calc
        s ^ 2 * b ^ (2 * q) = (s * b ^ q) ^ 2 := by ring
        _ ≤ Cseed ^ 2 := hsMulSq
    have habBig : a ^ (2 * q) ≤ c ^ (2 * q) * b ^ (2 * q) := by
      have hp := pow_le_pow_left₀ ha0.le hab (2 * q)
      simpa only [mul_pow] using hp
    have hsaBig : s ^ 2 * a ^ (2 * q) ≤ c ^ (2 * q) * Cseed ^ 2 := by
      have h1 := mul_le_mul_of_nonneg_left habBig (sq_nonneg s)
      have h2 := mul_le_mul_of_nonneg_left hsBig
        (pow_nonneg hc.le (2 * q))
      nlinarith
    have hrq : 2 * r ≤ 2 * q := by
      dsimp [r, q]
      omega
    have har : a ^ (2 * r) ≤ a ^ (2 * q) :=
      pow_le_pow_right₀ ha hrq
    have hsa : s ^ 2 * a ^ (2 * r) ≤ c ^ (2 * q) * Cseed ^ 2 := by
      exact (mul_le_mul_of_nonneg_left har (sq_nonneg s)).trans hsaBig
    have hinv := budgets.inv_eta_le_weight j n hn
    change 1 / P.eta j ≤ budgets.Ceta * a ^ r at hinv
    have hprod1 := mul_le_mul_of_nonneg_right hinv (sq_nonneg s)
    have hprod2 := mul_le_mul_of_nonneg_right hprod1
      (pow_nonneg ha0.le r)
    have hprod3 := mul_le_mul_of_nonneg_left hsa budgets.Ceta_pos.le
    have hfull : (1 / P.eta j) * s ^ 2 * a ^ r ≤ D := by
      calc
        (1 / P.eta j) * s ^ 2 * a ^ r ≤
            budgets.Ceta * a ^ r * s ^ 2 * a ^ r := hprod2
        _ = budgets.Ceta * (s ^ 2 * a ^ (2 * r)) := by ring
        _ ≤ budgets.Ceta * (c ^ (2 * q) * Cseed ^ 2) := hprod3
        _ = D := by dsimp [D]; ring
    have henergy : (1 / P.eta j) * s ^ 2 ≤ D / a ^ r :=
      (le_div_iff₀ (pow_pos ha0 r)).mpr hfull
    have hcoord (i : Fin d) :
        (1 + ((n i).natAbs : Real)) ^ 2 ≤ a ^ 2 := by
      apply pow_le_pow_left₀ (by positivity)
      dsimp [a]
      have hi := indexSize_coordinate_le n i
      exact_mod_cast Nat.add_le_add_left hi 1
    have hprodpos : 0 < ∏ i : Fin d,
        (1 + ((n i).natAbs : Real)) ^ 2 := by
      exact Finset.prod_pos fun _ _ ↦ by positivity
    have hprod : (∏ i : Fin d,
        (1 + ((n i).natAbs : Real)) ^ 2) ≤ a ^ r := by
      calc
        (∏ i : Fin d, (1 + ((n i).natAbs : Real)) ^ 2) ≤
            ∏ _i : Fin d, a ^ 2 := by
          exact Finset.prod_le_prod (fun _ _ ↦ by positivity)
            (fun i _ ↦ hcoord i)
        _ = a ^ (2 * d) := by simp [pow_mul]
        _ ≤ a ^ r := pow_le_pow_right₀ ha (by dsimp [r]; omega)
    have hweightLower : 1 / a ^ r ≤ indexWeight n := by
      calc
        1 / a ^ r ≤ 1 / (∏ i : Fin d,
            (1 + ((n i).natAbs : Real)) ^ 2) :=
          one_div_le_one_div_of_le hprodpos hprod
        _ = indexWeight n := by
          simp [indexWeight, zpow_neg]
          rfl
    calc
      (1 / P.eta j) * ‖inverseSample seed.G0 (frequency delta n)‖ ^ 2 =
          (1 / P.eta j) * s ^ 2 := rfl
      _ ≤ D / a ^ r := henergy
      _ = D * (1 / a ^ r) := by ring
      _ ≤ D * indexWeight n :=
        mul_le_mul_of_nonneg_left hweightLower hD
  have henergyNonneg : ∀ j, 0 ≤ blockEnergyTerm P seed.G0 j := by
    intro j
    rw [blockEnergyTerm]
    split_ifs with hj
    · exact mul_nonneg (div_nonneg zero_le_one (P.eta_pos j hj).le)
        (Finset.sum_nonneg fun n hn ↦ sq_nonneg _)
    · exact le_rfl
  let majorant : Nat → Real := fun j ↦
    ∑ n ∈ dyadicBlock delta hdelta data.C0 j, D * indexWeight n
  have henergyMajorant : ∀ j,
      blockEnergyTerm P seed.G0 j ≤ majorant j := by
    intro j
    rw [blockEnergyTerm]
    split_ifs with hj
    · dsimp [majorant]
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun n hn ↦ hsampleBudget j n hj hn
    · dsimp [majorant]
      exact Finset.sum_nonneg fun n hn ↦ mul_nonneg hD (by
        rw [indexWeight]
        exact Finset.prod_nonneg fun _ _ ↦ zpow_nonneg (by positivity) _)
  have hweight : Summable (fun n : IntVec d ↦ D * indexWeight n) :=
    (indexWeight_summable d).mul_left D
  have hSigmaInj : Function.Injective
      (fun x : (Σ j : Nat, (dyadicBlock delta hdelta data.C0 j : Set (IntVec d))) ↦
        (x.2.1 : IntVec d)) := by
    intro x y hxy
    rcases x with ⟨j, n⟩
    rcases y with ⟨k, m⟩
    simp only at hxy
    have hjk : j = k := by
      by_contra hne
      have hdis := (coordinateBlocks_partition hd hdelta data.C0).2.2.1 j k hne
      exact (Finset.disjoint_left.mp hdis) n.property (hxy ▸ m.property)
    subst k
    have hnm : n = m := Subtype.ext hxy
    subst m
    rfl
  have hSigma : Summable
      (fun x : (Σ j : Nat, (dyadicBlock delta hdelta data.C0 j : Set (IntVec d))) ↦
        D * indexWeight x.2.1) :=
    hweight.comp_injective hSigmaInj
  have hmajorant : Summable majorant := by
    have houter : Summable (fun j : Nat ↦
        ∑' n : (dyadicBlock delta hdelta data.C0 j : Set (IntVec d)),
          D * indexWeight n.1) :=
      (summable_sigma_of_nonneg (fun x ↦ mul_nonneg hD (by
        rw [indexWeight]
        exact Finset.prod_nonneg fun _ _ ↦ zpow_nonneg (by positivity) _))).mp
          hSigma |>.2
    simpa only [majorant, ← Finset.tsum_subtype'] using houter
  have hsum : Summable (fun j ↦ blockEnergyTerm P seed.G0 j) :=
    hmajorant.of_nonneg_of_le henergyNonneg henergyMajorant
  refine ⟨hsum, ?_, ?_⟩
  · exact tsum_nonneg henergyNonneg
  · exact hsum.hasSum

/-- First-coordinate-difference witness and exact carrier. -/
structure SeedWitnessData {d : Nat} (hd : 0 < d)
    {delta : IntVec d → RealVec d}
    {hdelta : TendsToZeroAtIntVecInfinity delta}
    {data : ModifiedFrequencyData delta} {mu0 : Real}
    {K : ExponentialBoundsHD data.nu}
    {P : BlockParameters hd delta hdelta data mu0}
    {budgets : BudgetConstants P}
    {EC : ExceptionalConstants hd delta hdelta data P}
    {CC : CorrectionConstants hd data K P budgets EC}
    {threshold : BlockThreshold CC}
    (seed : SeedData hd P threshold) where
  F0 : RealVec d → Complex
  F0_eq : F0 = firstCoordinateDifference hd seed.G0
  S0 : Set (RealVec d)
  S0_eq : S0 = (basisVector (firstCoordinate hd) +ᵥ seed.A0) ∪ seed.A0
  S0_subset : S0 ⊆ {x | 0 < x (firstCoordinate hd) ∧
    x (firstCoordinate hd) < 1 + mu0 / 8}
  S0_measurable : MeasurableSet S0
  F0_stronglyMeasurable : AEStronglyMeasurable F0 volume
  F0_integrable : Integrable F0 volume
  F0_memLp : MemLp F0 (2 : ENNReal) volume
  F0_supported : AESupportedIn F0 S0
  volume_S0_lt : volume S0 < ENNReal.ofReal (mu0 / 4)
  F0_ae_ne_zero : ¬ F0 =ᵐ[volume] (0 : RealVec d → Complex)

/-- Existence certificate for the literal first-coordinate-difference witness. -/
theorem seedWitnessData_nonempty {d : Nat} (hd : 0 < d)
    {delta : IntVec d → RealVec d}
    {hdelta : TendsToZeroAtIntVecInfinity delta}
    {data : ModifiedFrequencyData delta} {mu0 : Real}
    {K : ExponentialBoundsHD data.nu}
    {P : BlockParameters hd delta hdelta data mu0}
    {budgets : BudgetConstants P}
    {EC : ExceptionalConstants hd delta hdelta data P}
    {CC : CorrectionConstants hd data K P budgets EC}
    {threshold : BlockThreshold CC}
    (seed : SeedData hd P threshold) : Nonempty (SeedWitnessData hd seed) := by
  let F0 : RealVec d → Complex := firstCoordinateDifference hd seed.G0
  let S0 : Set (RealVec d) :=
    (basisVector (firstCoordinate hd) +ᵥ seed.A0) ∪ seed.A0
  have hcost := firstCoordinateDifference_support_cost hd seed.A0_measurable
    seed.G0_stronglyMeasurable seed.G0_integrable seed.G0_memLp seed.G0_supported
  have hdisj : Disjoint seed.A0
      (basisVector (firstCoordinate hd) +ᵥ seed.A0) := by
    rw [Set.disjoint_left]
    intro x hxA hxShift
    rcases Set.mem_vadd_set.mp hxShift with ⟨u, huA, hux⟩
    rcases seed.A0_subset hxA with ⟨hx0, hxUpper⟩
    rcases seed.A0_subset huA with ⟨hu0, huUpper⟩
    change basisVector (firstCoordinate hd) + u = x at hux
    have hcoord := congr_fun hux (firstCoordinate hd)
    simp [basisVector_apply] at hcoord
    nlinarith [P.mu0_pos, P.mu0_lt_one]
  have hS0Sub : S0 ⊆
      {x | 0 < x (firstCoordinate hd) ∧
        x (firstCoordinate hd) < 1 + mu0 / 8} := by
    intro x hx
    rcases hx with hx | hx
    · rcases Set.mem_vadd_set.mp hx with ⟨u, huA, hux⟩
      rcases seed.A0_subset huA with ⟨hu0, huUpper⟩
      change basisVector (firstCoordinate hd) + u = x at hux
      have hcoord := congr_fun hux (firstCoordinate hd)
      simp [basisVector_apply] at hcoord
      constructor <;> nlinarith
    · rcases seed.A0_subset hx with ⟨hx0, hxUpper⟩
      constructor <;> nlinarith
  have hG0Norm : 0 < sqNormOn Set.univ seed.G0 := by
    rw [sqNormOn, setIntegral_univ]
    have hint : Integrable (fun x : RealVec d ↦ ‖seed.G0 x‖ ^ 2) volume :=
      seed.G0_memLp.integrable_norm_pow (by norm_num)
    have hnonneg : 0 ≤ ∫ x : RealVec d, ‖seed.G0 x‖ ^ 2 :=
      integral_nonneg (fun x ↦ sq_nonneg _)
    refine lt_of_le_of_ne hnonneg ?_
    intro heq
    apply seed.G0_ae_ne_zero
    have hae : (fun x : RealVec d ↦ ‖seed.G0 x‖ ^ 2) =ᵐ[volume]
        (0 : RealVec d → Real) :=
      (integral_eq_zero_iff_of_nonneg_ae
        (Filter.Eventually.of_forall (fun x ↦ sq_nonneg _)) hint).mp heq.symm
    filter_upwards [hae] with x hx
    have hx' : ‖seed.G0 x‖ ^ 2 = 0 := by
      simpa only [Pi.zero_apply] using hx
    have hn : ‖seed.G0 x‖ = 0 := by nlinarith [norm_nonneg (seed.G0 x)]
    exact norm_eq_zero.mp hn
  have hF0AeNe : ¬ F0 =ᵐ[volume] (0 : RealVec d → Complex) := by
    have hnorm := firstCoordinateDifference_sqNorm_of_disjoint hd
      seed.A0_measurable seed.G0_stronglyMeasurable seed.G0_memLp
      seed.G0_supported hdisj
    intro hae
    have hzero : sqNormOn Set.univ F0 = 0 := by
      rw [sqNormOn, setIntegral_univ]
      apply integral_eq_zero_of_ae
      filter_upwards [hae] with x hx
      simp only [Pi.zero_apply, hx, norm_zero,
        zero_pow (by norm_num : (2 : Nat) ≠ 0)]
    change sqNormOn Set.univ F0 = 2 * sqNormOn Set.univ seed.G0 at hnorm
    nlinarith
  have hvolume : volume S0 < ENNReal.ofReal (mu0 / 4) := by
    have htwice : 2 * volume seed.A0 <
        2 * ENNReal.ofReal (mu0 / 8) := by
      simpa only [two_mul] using
        ENNReal.add_lt_add seed.volume_A0_lt seed.volume_A0_lt
    calc
      volume S0 ≤ 2 * volume seed.A0 := hcost.2.2.2.2.2.1
      _ < 2 * ENNReal.ofReal (mu0 / 8) := htwice
      _ = ENNReal.ofReal (mu0 / 4) := by
        rw [← ENNReal.ofReal_ofNat,
          ← ENNReal.ofReal_mul (by norm_num : (0 : Real) ≤ 2)]
        congr 1
        ring
  refine ⟨
    { F0 := F0
      F0_eq := rfl
      S0 := S0
      S0_eq := rfl
      S0_subset := hS0Sub
      S0_measurable := hcost.1
      F0_stronglyMeasurable := hcost.2.1
      F0_integrable := hcost.2.2.1
      F0_memLp := hcost.2.2.2.1
      F0_supported := hcost.2.2.2.2.1
      volume_S0_lt := hvolume
      F0_ae_ne_zero := hF0AeNe }⟩

/-- Constructor required by the unique construction context for `SeedWitnessData`. -/
noncomputable def seedWitnessData {d : Nat} (hd : 0 < d)
    {delta : IntVec d → RealVec d}
    {hdelta : TendsToZeroAtIntVecInfinity delta}
    {data : ModifiedFrequencyData delta} {mu0 : Real}
    {K : ExponentialBoundsHD data.nu}
    {P : BlockParameters hd delta hdelta data mu0}
    {budgets : BudgetConstants P}
    {EC : ExceptionalConstants hd delta hdelta data P}
    {CC : CorrectionConstants hd data K P budgets EC}
    {threshold : BlockThreshold CC}
    (seed : SeedData hd P threshold) : SeedWitnessData hd seed :=
  Classical.choice (seedWitnessData_nonempty hd seed)

end AsymptoticallyIntegerHD.Internal
