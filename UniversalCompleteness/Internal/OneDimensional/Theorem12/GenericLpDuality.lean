import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Complex
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic

noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal Topology BigOperators symmDiff

namespace Theorem12.Generic

/- Proof idea: install `Fact (1 ≤ p)` locally and use Mathlib's finite-measure indicator
constructor, whose representative is the complex-valued indicator of `A`. -/
def indicatorLp {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [IsFiniteMeasure mu] (p : ENNReal) (hp : 1 ≤ p)
    (A : Set X) (hA : MeasurableSet A) : Lp ℂ p mu := by
  letI : Fact (1 ≤ p) := ⟨hp⟩
  exact MeasureTheory.indicatorConstLp p hA (measure_ne_top mu A) (1 : ℂ)

private def dualPhase (z : ℂ) : ℂ := (‖z‖ : ℂ) * z⁻¹

private lemma measurable_dualPhase : Measurable dualPhase := by
  unfold dualPhase
  fun_prop

private lemma norm_dualPhase_le_one (z : ℂ) : ‖dualPhase z‖ ≤ 1 := by
  by_cases hz : z = 0
  · simp [dualPhase, hz]
  · simp [dualPhase, norm_inv, hz]

private lemma dualPhase_mul (z : ℂ) (hz : z ≠ 0) :
    dualPhase z * z = (‖z‖ : ℂ) := by
  rw [dualPhase, mul_assoc, inv_mul_cancel₀ hz, mul_one]

private lemma dualPhase_mul_all (z : ℂ) :
    dualPhase z * z = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · simp [hz]
  · exact dualPhase_mul z hz

private theorem sum_norm_functional_indicator_le
    {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [IsFiniteMeasure mu] (p : ENNReal) (hp : 1 ≤ p)
    (L : letI : Fact (1 ≤ p) := ⟨hp⟩; Lp ℂ p mu →L[ℂ] ℂ)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (A : ι → Set X)
    (hA : ∀ i, MeasurableSet (A i))
    (hdisj : (s : Set ι).PairwiseDisjoint A) :
    ∑ i ∈ s, ‖L (indicatorLp mu p hp (A i) (hA i))‖ ≤
      ‖L‖ * (mu Set.univ ^ (p.toReal)⁻¹).toReal := by
  letI : Fact (1 ≤ p) := ⟨hp⟩
  let z : ι → ℂ := fun i => L (indicatorLp mu p hp (A i) (hA i))
  let testLp : Lp ℂ p mu :=
    ∑ i ∈ s, dualPhase (z i) • indicatorLp mu p hp (A i) (hA i)
  let v : X → ℂ := fun x =>
    ∑ i ∈ s, (A i).indicator (fun _ => dualPhase (z i)) x
  have hvBound (x : X) : ‖v x‖ ≤ 1 := by
    by_cases hex : ∃ i ∈ s, x ∈ A i
    · obtain ⟨i, hiS, hxi⟩ := hex
      have hzero : ∀ j ∈ s, j ≠ i →
          (A j).indicator (fun _ => dualPhase (z j)) x = 0 := by
        intro j hjS hji
        have hij : Disjoint (A j) (A i) := hdisj hjS hiS hji
        have hxj : x ∉ A j := fun hxj => Set.disjoint_left.1 hij hxj hxi
        simp [hxj]
      rw [show v x = (A i).indicator (fun _ => dualPhase (z i)) x by
        simp only [v]
        exact Finset.sum_eq_single i (fun j hjS hji => hzero j hjS hji) (by simp [hiS])]
      simpa [hxi] using norm_dualPhase_le_one (z i)
    · have hx : ∀ i ∈ s, x ∉ A i := by simpa only [not_exists, not_and] using hex
      rw [show v x = 0 by
        simp only [v]
        apply Finset.sum_eq_zero
        intro i hi
        simp [hx i hi]]
      norm_num
  have hcoe : (testLp : X → ℂ) =ᵐ[mu] v := by
    have hfin : ∀ t : Finset ι,
        (((∑ i ∈ t, dualPhase (z i) • indicatorLp mu p hp (A i) (hA i) :
            Lp ℂ p mu) : X → ℂ) =ᵐ[mu]
          fun x => ∑ i ∈ t, (A i).indicator (fun _ => dualPhase (z i)) x) := by
      intro t
      induction t using Finset.induction_on with
      | empty =>
          simp only [Finset.sum_empty]
          exact Lp.coeFn_zero ℂ p mu
      | @insert i t hit ih =>
          filter_upwards [Lp.coeFn_add
              (dualPhase (z i) • indicatorLp mu p hp (A i) (hA i))
              (∑ j ∈ t, dualPhase (z j) • indicatorLp mu p hp (A j) (hA j)),
            Lp.coeFn_smul (dualPhase (z i)) (indicatorLp mu p hp (A i) (hA i)),
            indicatorConstLp_coeFn (α := X) (E := ℂ) (p := p) (μ := mu)
              (s := A i) (hs := hA i) (hμs := measure_ne_top mu (A i)) (c := (1 : ℂ)),
            ih] with x hxadd hxsmul hxind hxih
          simp only [Finset.sum_insert hit]
          rw [hxadd]
          simp only [Pi.add_apply]
          rw [hxsmul, hxih]
          simp only [Pi.smul_apply, smul_eq_mul]
          change ((indicatorLp mu p hp (A i) (hA i) : Lp ℂ p mu) : X → ℂ) x =
            (A i).indicator (fun _ => (1 : ℂ)) x at hxind
          rw [hxind]
          by_cases hxi : x ∈ A i <;> simp [hxi]
    simpa [testLp, v] using hfin s
  have htestNorm : ‖testLp‖ ≤ (mu Set.univ ^ (p.toReal)⁻¹).toReal := by
    rw [Lp.norm_def, eLpNorm_congr_ae hcoe]
    apply ENNReal.toReal_mono
    · finiteness
    simpa using eLpNorm_le_of_ae_bound
      (p := p) (μ := mu) (Filter.Eventually.of_forall hvBound)
  have hLtest : L testLp = ((∑ i ∈ s, ‖z i‖ : ℝ) : ℂ) := by
    calc
      L testLp = ∑ i ∈ s, dualPhase (z i) * z i := by
        simp [testLp, z, smul_eq_mul]
      _ = ∑ i ∈ s, (‖z i‖ : ℂ) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact dualPhase_mul_all (z i)
      _ = ((∑ i ∈ s, ‖z i‖ : ℝ) : ℂ) := by push_cast; rfl
  have hsumNonneg : 0 ≤ ∑ i ∈ s, ‖z i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hop := L.le_opNorm testLp
  rw [hLtest, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsumNonneg] at hop
  exact hop.trans (mul_le_mul_of_nonneg_left htestNorm (norm_nonneg L))

/- Proof idea: prove countable
additivity from disjoint indicator convergence and use null indicators for absolute
continuity. -/
theorem exists_complexMeasure_of_Lp_functional {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [SigmaFinite mu] [IsFiniteMeasure mu]
    (p : ENNReal) (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (L : letI : Fact (1 ≤ p) := ⟨hp⟩; Lp ℂ p mu →L[ℂ] ℂ) :
    ∃ nu : ComplexMeasure X, IsFiniteMeasure nu.variation ∧
      nu ≪ᵥ mu.toENNRealVectorMeasure ∧
      ∀ A : Set X, ∀ hA : MeasurableSet A,
        nu A = L (indicatorLp mu p hp A hA) := by
  classical
  letI : Fact (1 ≤ p) := ⟨hp⟩
  let m : Set X → ℂ := fun A =>
    if hA : MeasurableSet A then L (indicatorLp mu p hp A hA) else 0
  have hm_meas (A : Set X) (hA : MeasurableSet A) :
      m A = L (indicatorLp mu p hp A hA) := by simp [m, hA]
  have hm_nonmeas (A : Set X) (hA : ¬MeasurableSet A) : m A = 0 := by simp [m, hA]
  have hm_add (A B : Set X) (hA : MeasurableSet A) (hB : MeasurableSet B)
      (hAB : Disjoint A B) : m (A ∪ B) = m A + m B := by
    rw [hm_meas _ (hA.union hB), hm_meas _ hA, hm_meas _ hB]
    rw [indicatorLp, indicatorLp, indicatorLp,
      indicatorConstLp_disjoint_union hA hB (measure_ne_top mu A)
        (measure_ne_top mu B) hAB (1 : ℂ), map_add]
  have hind_empty : indicatorLp mu p hp ∅ MeasurableSet.empty = 0 := by
    apply Lp.ext
    filter_upwards [indicatorConstLp_coeFn (α := X) (E := ℂ) (p := p) (μ := mu)
      (s := ∅) (hs := MeasurableSet.empty) (hμs := measure_ne_top mu ∅)
      (c := (1 : ℂ)), Lp.coeFn_zero ℂ p mu] with x hx h0
    change ((indicatorLp mu p hp ∅ MeasurableSet.empty : Lp ℂ p mu) : X → ℂ) x =
      (∅ : Set X).indicator (fun _ => (1 : ℂ)) x at hx
    rw [hx, h0]
    simp
  have hm_empty : m ∅ = 0 := by
    rw [hm_meas _ MeasurableSet.empty, hind_empty, map_zero]
  let nu : ComplexMeasure X := {
    measureOf' := m
    empty' := hm_empty
    not_measurable' := fun A hA => hm_nonmeas A hA
    m_iUnion' := by
      intro f hf hdisj
      have hnorm : Summable (fun i => ‖m (f i)‖) := by
        apply summable_of_sum_le (fun i => norm_nonneg _)
        intro s
        simpa only [hm_meas _ (hf _)] using
          (sum_norm_functional_indicator_le mu p hp L s f hf
            (fun i hi j hj hij => hdisj hij))
      apply (hasSum_iff_tendsto_nat_of_summable_norm hnorm).2
      let U : ℕ → Set X := fun n => ⋃ i ∈ Finset.range n, f i
      have hUmeas (n : ℕ) : MeasurableSet (U n) :=
        Finset.measurableSet_biUnion _ fun i _ => hf i
      have hsum (t : Finset ℕ) : ∑ i ∈ t, m (f i) = m (⋃ i ∈ t, f i) := by
        induction t using Finset.induction_on with
        | empty => simpa using hm_empty.symm
        | @insert i t hit ih =>
            rw [Finset.sum_insert hit, ih]
            have hUt : MeasurableSet (⋃ j ∈ t, f j) :=
              Finset.measurableSet_biUnion _ fun j _ => hf j
            have hdis : Disjoint (f i) (⋃ j ∈ t, f j) := by
              rw [Set.disjoint_iUnion_right]
              intro j
              rw [Set.disjoint_iUnion_right]
              intro hj
              exact hdisj (fun hij => hit (hij ▸ hj))
            rw [← hm_add _ _ (hf i) hUt hdis]
            congr 1
            ext x
            simp
      have htail : Filter.Tendsto (fun n => mu (⋃ i ∈ Set.Ici n, f i))
          Filter.atTop (𝓝 0) :=
        tendsto_measure_biUnion_Ici_zero_of_pairwise_disjoint
          (fun i => (hf i).nullMeasurableSet) hdisj
      have hsymm (n : ℕ) : U n ∆ (⋃ i, f i) = ⋃ i ∈ Set.Ici n, f i := by
        ext x
        simp only [U, Set.mem_symmDiff, mem_iUnion, Finset.mem_range, Set.mem_Ici]
        constructor
        · rintro (⟨⟨i, hi, hxi⟩, hnot⟩ | ⟨⟨i, hxi⟩, hnot⟩)
          · exact False.elim (hnot ⟨i, hxi⟩)
          · refine ⟨i, ?_, hxi⟩
            by_contra hin
            exact hnot ⟨i, Nat.lt_of_not_ge hin, hxi⟩
        · rintro ⟨i, hin, hxi⟩
          exact Or.inr ⟨⟨i, hxi⟩, fun hmem => by
            rcases hmem with ⟨j, hjn, hxj⟩
            have hij : i ≠ j := fun hij => by omega
            exact Set.disjoint_left.1 (hdisj hij) hxi hxj⟩
      have hindTend : Filter.Tendsto
          (fun n => indicatorLp mu p hp (U n) (hUmeas n)) Filter.atTop
          (𝓝 (indicatorLp mu p hp (⋃ i, f i) (MeasurableSet.iUnion hf))) := by
        apply tendsto_indicatorConstLp_set hpTop
        simpa only [hsymm] using htail
      have hmTend : Filter.Tendsto (fun n => m (U n)) Filter.atTop
          (𝓝 (m (⋃ i, f i))) := by
        convert L.continuous.continuousAt.tendsto.comp hindTend using 1
        · funext n
          exact hm_meas _ (hUmeas n)
        · rw [hm_meas _ (MeasurableSet.iUnion hf)]
      simpa only [hsum (Finset.range _), U] using hmTend
  }
  have hnu_meas (A : Set X) (hA : MeasurableSet A) :
      nu A = L (indicatorLp mu p hp A hA) := hm_meas A hA
  have hvar : nu.variation Set.univ < ∞ := by
    let B : ℝ := ‖L‖ * (mu Set.univ ^ (p.toReal)⁻¹).toReal
    have hBnonneg : 0 ≤ B := mul_nonneg (norm_nonneg L) ENNReal.toReal_nonneg
    have hle : nu.variation Set.univ ≤ ENNReal.ofReal B := by
      simp only [VectorMeasure.variation_apply, preVariation,
        VectorMeasure.ennrealToMeasure_apply MeasurableSet.univ, ennrealPreVariation_apply,
        preVariationFun, MeasurableSet.univ, dite_true, iSup_le_iff]
      intro P
      have hreal := sum_norm_functional_indicator_le mu p hp L P.parts
        (fun E : Subtype MeasurableSet => (E : Set X))
        (fun E => E.property) (by
          intro E hE F hF hEF
          exact (disjoint_subtype_iff (fun _ _ hs ht => hs.inter ht) _).1
            (P.disjoint hE hF hEF))
      have hreal' :
          ∑ E ∈ P.parts, ‖nu (E : Set X)‖ ≤ B := by
        calc
          ∑ E ∈ P.parts, ‖nu (E : Set X)‖ =
              ∑ E ∈ P.parts, ‖L (indicatorLp mu p hp E E.property)‖ := by
                apply Finset.sum_congr rfl
                intro E hE
                rw [hnu_meas]
          _ ≤ B := hreal
      calc
        ∑ E ∈ P.parts, ‖nu (E : Set X)‖ₑ =
            ENNReal.ofReal (∑ E ∈ P.parts, ‖nu (E : Set X)‖) := by
              rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => norm_nonneg _)]
              apply Finset.sum_congr rfl
              intro E hE
              simp only [ofReal_norm]
        _ ≤ ENNReal.ofReal B := ENNReal.ofReal_le_ofReal hreal'
    exact hle.trans_lt ENNReal.ofReal_lt_top
  letI : IsFiniteMeasure nu.variation := ⟨hvar⟩
  have hAC : nu ≪ᵥ mu.toENNRealVectorMeasure := by
    intro A hmuA
    by_cases hA : MeasurableSet A
    · rw [Measure.toENNRealVectorMeasure_apply_measurable hA] at hmuA
      have hmuA' : mu A = 0 := by simpa using hmuA
      have hnot : ∀ᵐ x ∂mu, x ∉ A := by
        rw [ae_iff]
        simpa using hmuA'
      rw [hnu_meas A hA]
      have hzero : indicatorLp mu p hp A hA = 0 := by
        apply Lp.ext
        filter_upwards [indicatorConstLp_coeFn (α := X) (E := ℂ) (p := p) (μ := mu)
          (s := A) (hs := hA) (hμs := measure_ne_top mu A) (c := (1 : ℂ)),
          hnot, Lp.coeFn_zero ℂ p mu]
            with x hx hnot h0
        change ((indicatorLp mu p hp A hA : Lp ℂ p mu) : X → ℂ) x =
          A.indicator (fun _ => (1 : ℂ)) x at hx
        rw [hx, h0]
        simp [hnot]
      rw [hzero, map_zero]
    · exact nu.not_measurable hA
  exact ⟨nu, inferInstance, hAC, hnu_meas⟩

/- Proof idea: store the one chosen unconjugated kernel together
with exactly its measurability, integrability, and indicator identity. -/
structure LpRNKernelData {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [IsFiniteMeasure mu] (p : ENNReal) (hp : 1 ≤ p)
    (L : letI : Fact (1 ≤ p) := ⟨hp⟩; Lp ℂ p mu →L[ℂ] ℂ) where
  kernel : X → ℂ
  aestronglyMeasurable_kernel : AEStronglyMeasurable kernel mu
  integrable_kernel : Integrable kernel mu
  indicator_formula : ∀ A : Set X, ∀ hA : MeasurableSet A,
    L (indicatorLp mu p hp A hA) =
      ∫ x, A.indicator (fun _ => (1 : ℂ)) x * kernel x ∂mu

private theorem complexMeasure_apply_eq_setIntegral_rnDeriv
    {X : Type*} [MeasurableSpace X] (mu : Measure X) [SigmaFinite mu]
    (nu : ComplexMeasure X) (hnu : nu ≪ᵥ mu.toENNRealVectorMeasure)
    (A : Set X) (hA : MeasurableSet A) :
    nu A = ∫ x in A, nu.rnDeriv mu x ∂mu := by
  have hac := (ComplexMeasure.absolutelyContinuous_ennreal_iff nu
    mu.toENNRealVectorMeasure).1 hnu
  have hre := SignedMeasure.withDensityᵥ_rnDeriv_eq nu.re mu hac.1
  have him := SignedMeasure.withDensityᵥ_rnDeriv_eq nu.im mu hac.2
  have hreA := congrArg (fun s : SignedMeasure X => s A) hre
  have himA := congrArg (fun s : SignedMeasure X => s A) him
  apply Complex.ext
  · rw [← RCLike.re_eq_complex_re,
      ← @integral_re X _ (mu.restrict A) ℂ _ _
        (nu.integrable_rnDeriv mu).integrableOn,
      RCLike.re_eq_complex_re]
    rw [withDensityᵥ_apply (SignedMeasure.integrable_rnDeriv nu.re mu) hA] at hreA
    simpa [ComplexMeasure.rnDeriv] using hreA.symm
  · rw [← RCLike.im_eq_complex_im,
      ← @integral_im X _ (mu.restrict A) ℂ _ _
        (nu.integrable_rnDeriv mu).integrableOn,
      RCLike.im_eq_complex_im]
    rw [withDensityᵥ_apply (SignedMeasure.integrable_rnDeriv nu.im mu) hA] at himA
    simpa [ComplexMeasure.rnDeriv] using himA.symm

/- Proof idea: construct the complex measure from `exists_complexMeasure_of_Lp_functional`, apply complex (or
real/imaginary signed) Radon--Nikodym, and fill `LpRNKernelData`. -/
theorem exists_LpRNKernelData {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [SigmaFinite mu] [IsFiniteMeasure mu]
    (p : ENNReal) (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (L : letI : Fact (1 ≤ p) := ⟨hp⟩; Lp ℂ p mu →L[ℂ] ℂ) :
    Nonempty (LpRNKernelData mu p hp L) := by
  rcases exists_complexMeasure_of_Lp_functional mu p hp hpTop L with
    ⟨nu, _hnuFinite, hnuAC, hnu⟩
  refine ⟨{
    kernel := nu.rnDeriv mu
    aestronglyMeasurable_kernel := (nu.integrable_rnDeriv mu).1
    integrable_kernel := nu.integrable_rnDeriv mu
    indicator_formula := ?_
  }⟩
  intro A hA
  rw [← hnu A hA, complexMeasure_apply_eq_setIntegral_rnDeriv mu nu hnuAC A hA]
  rw [← integral_indicator hA]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ A <;> simp [hx]

/- Proof idea: decompose the ordinary measurable finite-range function
as a finite complex linear combination of its measurable fibers. -/
theorem lp_functional_eq_integral_simple {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [IsFiniteMeasure mu] (p : ENNReal) (hp : 1 ≤ p)
    (L : letI : Fact (1 ≤ p) := ⟨hp⟩; Lp ℂ p mu →L[ℂ] ℂ)
    (rn : LpRNKernelData mu p hp L)
    (v : X → ℂ) (hv : Measurable v) (hvRange : Set.Finite (Set.range v))
    (hvLp : MemLp v p mu) :
    L (hvLp.toLp v) = ∫ x, v x * rn.kernel x ∂mu := by
  classical
  letI : Fact (1 ≤ p) := ⟨hp⟩
  let sf : SimpleFunc X ℂ :=
    ⟨v, fun z => (measurableSet_singleton z).preimage hv, hvRange⟩
  let sfMem (f : SimpleFunc X ℂ) : MemLp f p mu :=
    f.memLp_of_isFiniteMeasure p mu
  have hsf : ∀ f : SimpleFunc X ℂ,
      L ((sfMem f).toLp f) = ∫ x, f x * rn.kernel x ∂mu := by
    apply SimpleFunc.induction
    · intro c A hA
      let fA := SimpleFunc.piecewise A hA (SimpleFunc.const X c) (SimpleFunc.const X 0)
      have htoLp : (sfMem fA).toLp fA =
          c • indicatorLp mu p hp A hA := by
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (sfMem fA),
          Lp.coeFn_smul c (indicatorLp mu p hp A hA),
          (indicatorConstLp_coeFn (α := X) (E := ℂ) (p := p) (μ := mu)
            (s := A) (hs := hA) (hμs := measure_ne_top mu A) (c := (1 : ℂ)))]
            with x hxsf hxsmul hxind
        change ((indicatorLp mu p hp A hA : Lp ℂ p mu) : X → ℂ) x =
          A.indicator (fun _ => (1 : ℂ)) x at hxind
        rw [hxsf, hxsmul]
        change fA x = c * ((indicatorLp mu p hp A hA : Lp ℂ p mu) : X → ℂ) x
        rw [hxind]
        by_cases hx : x ∈ A <;> simp [fA, hx]
      rw [htoLp, map_smul, rn.indicator_formula A hA]
      change c * (∫ x, A.indicator (fun _ => (1 : ℂ)) x * rn.kernel x ∂mu) = _
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : x ∈ A <;> simp [hx]
    · intro f g _hfg hff hgg
      have hfMem := sfMem f
      have hgMem := sfMem g
      have hfgMem := sfMem (f + g)
      obtain ⟨Cf, hCf⟩ := f.exists_forall_norm_le
      obtain ⟨Cg, hCg⟩ := g.exists_forall_norm_le
      have hfInt : Integrable (fun x => f x * rn.kernel x) mu :=
        (ContinuousLinearMap.mul ℂ ℂ).integrable_of_bilin_of_bdd_left Cf
          f.aestronglyMeasurable (Filter.Eventually.of_forall hCf) rn.integrable_kernel
      have hgInt : Integrable (fun x => g x * rn.kernel x) mu :=
        (ContinuousLinearMap.mul ℂ ℂ).integrable_of_bilin_of_bdd_left Cg
          g.aestronglyMeasurable (Filter.Eventually.of_forall hCg) rn.integrable_kernel
      rw [SimpleFunc.coe_add] at hfgMem
      rw [show hfgMem.toLp (f + g) = hfMem.toLp f + hgMem.toLp g by
        simpa only [SimpleFunc.coe_add] using (MemLp.toLp_add hfMem hgMem)]
      rw [map_add, hff, hgg]
      rw [← integral_add hfInt hgInt]
      apply integral_congr_ae
      filter_upwards with x
      simp [SimpleFunc.coe_add, add_mul]
  have hsf_sf := hsf sf
  change L ((sfMem sf).toLp v) = _ at hsf_sf
  have hto : (sfMem sf).toLp v = hvLp.toLp v := by
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall fun _ => rfl
  rw [hto] at hsf_sf
  exact hsf_sf

private theorem lp_functional_eq_integral_of_ae_bound_of_ne_top
    {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [IsFiniteMeasure mu] (p : ENNReal) (hp : 1 ≤ p)
    (hpTop : p ≠ ∞)
    (L : letI : Fact (1 ≤ p) := ⟨hp⟩; Lp ℂ p mu →L[ℂ] ℂ)
    (rn : LpRNKernelData mu p hp L)
    (v : X → ℂ) (hv : AEStronglyMeasurable v mu) (hvLp : MemLp v p mu)
    (C0 : ℝ) (_hC0 : 0 ≤ C0) (hbound : ∀ᵐ x ∂mu, ‖v x‖ ≤ C0) :
    L (hvLp.toLp v) = ∫ x, v x * rn.kernel x ∂mu := by
  letI : Fact (1 ≤ p) := ⟨hp⟩
  let w : X → ℂ := hv.mk v
  have hw : StronglyMeasurable w := hv.stronglyMeasurable_mk
  have hwEq : v =ᵐ[mu] w := hv.ae_eq_mk
  have hwBound : ∀ᵐ x ∂mu, ‖w x‖ ≤ C0 := by
    filter_upwards [hbound, hwEq] with x hx hxw
    simpa [← hxw] using hx
  have hwLp : MemLp w p mu := (memLp_congr_ae hwEq).mp hvLp
  let s : ℕ → SimpleFunc X ℂ := fun n =>
    SimpleFunc.approxOn w hw.measurable (Set.range w ∪ {0}) 0 (by simp) n
  have hsMeas (n : ℕ) : AEStronglyMeasurable (s n : X → ℂ) mu :=
    (s n).aestronglyMeasurable
  have hsLp (n : ℕ) : MemLp (s n : X → ℂ) p mu :=
    (s n).memLp_of_isFiniteMeasure p mu
  have hsBound (n : ℕ) : ∀ x, ‖s n x‖ ≤ ‖w x‖ + ‖w x‖ := by
    intro x
    exact SimpleFunc.norm_approxOn_zero_le hw.measurable (by simp) x n
  have hsTend : ∀ᵐ x ∂mu,
      Filter.Tendsto (fun n => s n x) Filter.atTop (𝓝 (w x)) :=
    Filter.Eventually.of_forall fun x =>
      SimpleFunc.tendsto_approxOn hw.measurable (by simp)
        (subset_closure (by simp))
  have hsNormTend : Filter.Tendsto
      (fun n => eLpNorm ((s n : X → ℂ) - w) p mu) Filter.atTop (𝓝 0) := by
    apply SimpleFunc.tendsto_approxOn_Lp_eLpNorm hw.measurable (by simp) hpTop
    · exact Filter.Eventually.of_forall fun x => subset_closure (by simp)
    · simpa using hwLp.2
  have hsLpTend : Filter.Tendsto
      (fun n => (hsLp n).toLp (s n : X → ℂ)) Filter.atTop
      (𝓝 (hwLp.toLp w)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun n => (s n : X → ℂ)) hsLp w hwLp).2 hsNormTend
  have hLTend : Filter.Tendsto
      (fun n => L ((hsLp n).toLp (s n : X → ℂ))) Filter.atTop
      (𝓝 (L (hwLp.toLp w))) :=
    L.continuous.continuousAt.tendsto.comp hsLpTend
  have hpairMeas (n : ℕ) : AEStronglyMeasurable
      (fun x => s n x * rn.kernel x) mu :=
    (ContinuousLinearMap.mul ℂ ℂ).aestronglyMeasurable_comp₂
      (s n).aestronglyMeasurable rn.aestronglyMeasurable_kernel
  have hpairBound (n : ℕ) : ∀ᵐ x ∂mu,
      ‖s n x * rn.kernel x‖ ≤ (2 * C0) * ‖rn.kernel x‖ := by
    filter_upwards [hwBound] with x hx
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    calc
      ‖s n x‖ ≤ ‖w x‖ + ‖w x‖ := hsBound n x
      _ ≤ C0 + C0 := add_le_add hx hx
      _ = 2 * C0 := by ring
  have hboundInt : Integrable (fun x => (2 * C0) * ‖rn.kernel x‖) mu :=
    rn.integrable_kernel.norm.const_mul (2 * C0)
  have hpairTend : ∀ᵐ x ∂mu,
      Filter.Tendsto (fun n => s n x * rn.kernel x) Filter.atTop
      (𝓝 (w x * rn.kernel x)) := by
    filter_upwards [hsTend] with x hx
    exact hx.mul_const _
  have hIntTend : Filter.Tendsto
      (fun n => ∫ x, s n x * rn.kernel x ∂mu) Filter.atTop
      (𝓝 (∫ x, w x * rn.kernel x ∂mu)) :=
    MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun x => (2 * C0) * ‖rn.kernel x‖) hpairMeas hboundInt hpairBound hpairTend
  have hseq : (fun n => L ((hsLp n).toLp (s n : X → ℂ))) =
      fun n => ∫ x, s n x * rn.kernel x ∂mu := by
    funext n
    exact lp_functional_eq_integral_simple mu p hp L rn (s n)
      (s n).measurable (s n).finite_range (hsLp n)
  have hlim : L (hwLp.toLp w) =
      ∫ x, w x * rn.kernel x ∂mu := by
    exact tendsto_nhds_unique hLTend (hseq ▸ hIntTend)
  calc
    L (hvLp.toLp v) = L (hwLp.toLp w) := by
      congr 1
      exact MemLp.toLp_congr hvLp hwLp hwEq
    _ = ∫ x, w x * rn.kernel x ∂mu := hlim
    _ = ∫ x, v x * rn.kernel x ∂mu := by
      apply integral_congr_ae
      filter_upwards [hwEq] with x hx
      rw [hx]

private theorem exists_simpleFunc_norm_sub_lt_of_measurable_bound
    {X : Type*} [MeasurableSpace X]
    (w : X → ℂ) (hw : Measurable w) (C0 : ℝ) (hC0 : 0 ≤ C0)
    (hwBound : ∀ x, ‖w x‖ ≤ C0) {eps : ℝ} (heps : 0 < eps) :
    ∃ sf : SimpleFunc X ℂ, ∀ x, ‖sf x - w x‖ < eps := by
  classical
  let s : Set ℂ := Metric.closedBall 0 C0
  have hsCompact : IsCompact s := isCompact_closedBall 0 C0
  have hzero : (0 : ℂ) ∈ s := by simpa [s] using hC0
  letI : Nonempty s := ⟨⟨0, hzero⟩⟩
  let e : ℕ → ℂ := fun n => ((denseSeq s n : s) : ℂ)
  have hclosure : s ⊆ closure (Set.range e) := by
    intro y hy
    have hy' : y ∈ closure (Set.range ((↑) ∘ denseSeq s)) := by
      rw [← @Subtype.range_coe _ s, ← image_univ,
        ← (denseRange_denseSeq s).closure_eq] at hy
      simpa only [Set.range_comp] using
        image_closure_subset_closure_image continuous_subtype_val hy
    simpa [e, Function.comp_def] using hy'
  have hcover : s ⊆ ⋃ n, Metric.ball (e n) eps := by
    intro y hy
    have hycl := hclosure hy
    rw [Metric.mem_closure_iff] at hycl
    obtain ⟨z, ⟨n, rfl⟩, hzy⟩ := hycl eps heps
    exact mem_iUnion.2 ⟨n, by simpa [dist_comm] using hzy⟩
  obtain ⟨t, ht⟩ := hsCompact.elim_finite_subcover
    (fun n => Metric.ball (e n) eps) (fun _ => Metric.isOpen_ball) hcover
  let N : ℕ := t.sup id
  let sf : SimpleFunc X ℂ := (SimpleFunc.nearestPt e N).comp w hw
  refine ⟨sf, fun x => ?_⟩
  have hwMem : w x ∈ s := by simpa [s, Metric.mem_closedBall] using hwBound x
  obtain ⟨n, hnT, hnBall⟩ : ∃ n ∈ t, w x ∈ Metric.ball (e n) eps := by
    simpa only [mem_iUnion, exists_prop] using ht hwMem
  have hnN : n ≤ N := Finset.le_sup (f := id) hnT
  have hnear := SimpleFunc.edist_nearestPt_le e (w x) hnN
  have hdist : dist (SimpleFunc.nearestPt e N (w x)) (w x) < eps := by
    have hnear' : ENNReal.ofReal (dist (SimpleFunc.nearestPt e N (w x)) (w x)) ≤
        ENNReal.ofReal (dist (e n) (w x)) := by
      simpa only [edist_dist] using hnear
    have hn' : ENNReal.ofReal (dist (e n) (w x)) < ENNReal.ofReal eps :=
      (ENNReal.ofReal_lt_ofReal_iff heps).2 (by
        simpa [Metric.mem_ball, dist_comm] using hnBall)
    exact (ENNReal.ofReal_lt_ofReal_iff heps).1 (hnear'.trans_lt hn')
  simpa [sf, SimpleFunc.coe_comp, dist_eq_norm] using hdist

private theorem lp_functional_eq_integral_of_ae_bound_top
    {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [IsFiniteMeasure mu]
    (L : Lp ℂ ∞ mu →L[ℂ] ℂ)
    (rn : LpRNKernelData mu ∞ le_top L)
    (v : X → ℂ) (hv : AEStronglyMeasurable v mu) (hvLp : MemLp v ∞ mu)
    (C0 : ℝ) (hC0 : 0 ≤ C0) (hbound : ∀ᵐ x ∂mu, ‖v x‖ ≤ C0) :
    L (hvLp.toLp v) = ∫ x, v x * rn.kernel x ∂mu := by
  classical
  let k : X → ℂ := hv.mk v
  have hkMeas : Measurable k := hv.measurable_mk
  have hkEq : v =ᵐ[mu] k := hv.ae_eq_mk
  have hkBound : ∀ᵐ x ∂mu, ‖k x‖ ≤ C0 := by
    filter_upwards [hbound, hkEq] with x hx hxk
    simpa [← hxk] using hx
  let E : Set X := {x | ‖k x‖ ≤ C0}
  have hE : MeasurableSet E := measurableSet_Iic.preimage hkMeas.norm
  let w : X → ℂ := E.indicator k
  have hwMeas : Measurable w := hkMeas.indicator hE
  have hwEq : v =ᵐ[mu] w := by
    filter_upwards [hkEq, hkBound] with x hxk hx
    rw [hxk]
    simp [w, E, hx]
  have hwBound : ∀ x, ‖w x‖ ≤ C0 := by
    intro x
    by_cases hx : x ∈ E
    · have hx' : ‖k x‖ ≤ C0 := by simpa [E] using hx
      simpa [w, hx] using hx'
    · simpa [w, hx] using hC0
  have hwLp : MemLp w ∞ mu := (memLp_congr_ae hwEq).mp hvLp
  have hex : ∀ n : ℕ, ∃ sf : SimpleFunc X ℂ,
      ∀ x, ‖sf x - w x‖ < 1 / (n + 1 : ℝ) := by
    intro n
    exact exists_simpleFunc_norm_sub_lt_of_measurable_bound w hwMeas C0 hC0 hwBound
      (by positivity)
  choose sf hsf using hex
  have hsfLp (n : ℕ) : MemLp (sf n : X → ℂ) ∞ mu :=
    (sf n).memLp_of_isFiniteMeasure ∞ mu
  have hepsTend : Filter.Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ))
      Filter.atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hdist (n : ℕ) : dist ((hsfLp n).toLp (sf n : X → ℂ)) (hwLp.toLp w) ≤
      1 / (n + 1 : ℝ) := by
    rw [Lp.dist_edist, Lp.edist_toLp_toLp]
    have heLp : eLpNorm ((sf n : X → ℂ) - w) ∞ mu ≤
        ENNReal.ofReal (1 / (n + 1 : ℝ)) := by
      simpa [eLpNorm] using eLpNormEssSup_le_of_ae_bound
        (show ∀ᵐ x ∂mu, ‖(((sf n : X → ℂ) - w) x)‖ ≤ 1 / (n + 1 : ℝ) from
          Filter.Eventually.of_forall fun x => by
            simpa only [Pi.sub_apply] using le_of_lt (hsf n x))
    calc
      (eLpNorm ((sf n : X → ℂ) - w) ∞ mu).toReal ≤
          (ENNReal.ofReal (1 / (n + 1 : ℝ))).toReal :=
        ENNReal.toReal_mono (by simp) heLp
      _ = 1 / (n + 1 : ℝ) := ENNReal.toReal_ofReal (by positivity)
  have hsfLpTend : Filter.Tendsto
      (fun n => (hsfLp n).toLp (sf n : X → ℂ)) Filter.atTop
      (𝓝 (hwLp.toLp w)) := by
    apply Metric.tendsto_atTop.2
    intro eps heps
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hepsTend eps heps
    refine ⟨N, fun n hn => ?_⟩
    have hN' := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)] at hN'
    exact (hdist n).trans_lt hN'
  have hLTend : Filter.Tendsto
      (fun n => L ((hsfLp n).toLp (sf n : X → ℂ))) Filter.atTop
      (𝓝 (L (hwLp.toLp w))) :=
    L.continuous.continuousAt.tendsto.comp hsfLpTend
  have hsfBound (n : ℕ) (x : X) : ‖sf n x‖ ≤ C0 + 1 := by
    calc
      ‖sf n x‖ = ‖(sf n x - w x) + w x‖ := by ring_nf
      _ ≤ ‖sf n x - w x‖ + ‖w x‖ := norm_add_le _ _
      _ ≤ (1 / (n + 1 : ℝ)) + C0 :=
        add_le_add (le_of_lt (hsf n x)) (hwBound x)
      _ ≤ 1 + C0 := by
        have heps_le_one : 1 / (n + 1 : ℝ) ≤ 1 := by
          rw [div_le_one (by positivity)]
          norm_num
        exact add_le_add heps_le_one le_rfl
      _ = C0 + 1 := by ring
  have hpairMeas (n : ℕ) : AEStronglyMeasurable
      (fun x => sf n x * rn.kernel x) mu :=
    (ContinuousLinearMap.mul ℂ ℂ).aestronglyMeasurable_comp₂
      (sf n).aestronglyMeasurable rn.aestronglyMeasurable_kernel
  have hpairBound (n : ℕ) : ∀ᵐ x ∂mu,
      ‖sf n x * rn.kernel x‖ ≤ (C0 + 1) * ‖rn.kernel x‖ :=
    Filter.Eventually.of_forall fun x => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hsfBound n x) (norm_nonneg _)
  have hboundInt : Integrable (fun x => (C0 + 1) * ‖rn.kernel x‖) mu :=
    rn.integrable_kernel.norm.const_mul (C0 + 1)
  have hsfTend : ∀ᵐ x ∂mu,
      Filter.Tendsto (fun n => sf n x) Filter.atTop (𝓝 (w x)) := by
    filter_upwards with x
    apply Metric.tendsto_atTop.2
    intro eps heps
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hepsTend eps heps
    refine ⟨N, fun n hn => ?_⟩
    have hN' := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)] at hN'
    simpa [dist_eq_norm] using (hsf n x).trans hN'
  have hpairTend : ∀ᵐ x ∂mu,
      Filter.Tendsto (fun n => sf n x * rn.kernel x) Filter.atTop
        (𝓝 (w x * rn.kernel x)) := by
    filter_upwards [hsfTend] with x hx
    exact hx.mul_const _
  have hIntTend : Filter.Tendsto
      (fun n => ∫ x, sf n x * rn.kernel x ∂mu) Filter.atTop
      (𝓝 (∫ x, w x * rn.kernel x ∂mu)) :=
    MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun x => (C0 + 1) * ‖rn.kernel x‖)
      hpairMeas hboundInt hpairBound hpairTend
  have hseq : (fun n => L ((hsfLp n).toLp (sf n : X → ℂ))) =
      fun n => ∫ x, sf n x * rn.kernel x ∂mu := by
    funext n
    exact lp_functional_eq_integral_simple mu ∞ le_top L rn (sf n)
      (sf n).measurable (sf n).finite_range (hsfLp n)
  have hlim : L (hwLp.toLp w) = ∫ x, w x * rn.kernel x ∂mu :=
    tendsto_nhds_unique hLTend (hseq ▸ hIntTend)
  calc
    L (hvLp.toLp v) = L (hwLp.toLp w) := by
      congr 1
      exact MemLp.toLp_congr hvLp hwLp hwEq
    _ = ∫ x, w x * rn.kernel x ∂mu := hlim
    _ = ∫ x, v x * rn.kernel x ∂mu := by
      apply integral_congr_ae
      filter_upwards [hwEq] with x hx
      rw [hx]

/- Proof idea: approximate by uniformly bounded measurable finite-range
functions and pass both sides to the limit using only finite measure and
`rn.integrable_kernel`. -/
theorem lp_functional_eq_integral_of_ae_bound {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [IsFiniteMeasure mu] (p : ENNReal) (hp : 1 ≤ p)
    (L : letI : Fact (1 ≤ p) := ⟨hp⟩; Lp ℂ p mu →L[ℂ] ℂ)
    (rn : LpRNKernelData mu p hp L)
    (v : X → ℂ) (hv : AEStronglyMeasurable v mu) (hvLp : MemLp v p mu)
    (C0 : ℝ) (hC0 : 0 ≤ C0) (hbound : ∀ᵐ x ∂mu, ‖v x‖ ≤ C0) :
    L (hvLp.toLp v) = ∫ x, v x * rn.kernel x ∂mu := by
  by_cases hpTop : p = ∞
  · subst p
    exact lp_functional_eq_integral_of_ae_bound_top mu L rn v hv hvLp C0 hC0 hbound
  · exact lp_functional_eq_integral_of_ae_bound_of_ne_top
      mu p hp hpTop L rn v hv hvLp C0 hC0 hbound

/- Proof idea: test against bounded phase-power truncations, derive uniform bounds,
and pass to the monotone limit using Holder-conjugate arithmetic. -/
theorem rnKernel_memLp_conjExponent_of_one_lt {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [IsFiniteMeasure mu] (p : ENNReal) (hp : 1 ≤ p)
    (hpOne : 1 < p) (hpTop : p ≠ ∞)
    (L : letI : Fact (1 ≤ p) := ⟨hp⟩; Lp ℂ p mu →L[ℂ] ℂ)
    (rn : LpRNKernelData mu p hp L) :
    MemLp rn.kernel (ENNReal.conjExponent p) mu ∧
      eLpNorm rn.kernel (ENNReal.conjExponent p) mu ≤ ENNReal.ofReal ‖L‖ := by
  let q := ENNReal.conjExponent p
  letI : Fact (1 ≤ p) := ⟨hp⟩
  letI hpq : p.HolderConjugate q := ENNReal.HolderConjugate.conjExponent hp
  have hpReal : 1 < p.toReal := by
    simpa using ENNReal.toReal_strict_mono hpTop hpOne
  have hpqReal : p.toReal.HolderConjugate q.toReal :=
    ENNReal.HolderConjugate.toReal hpReal
  have hqTop : q ≠ ∞ :=
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt q p).2 hpOne).ne
  have hqZero : q ≠ 0 := (ENNReal.HolderConjugate.pos q p).ne'
  have hqRealPos : 0 < q.toReal := ENNReal.toReal_pos hqZero hqTop
  have hrPos : 0 < q.toReal - 1 := sub_pos.mpr hpqReal.symm.lt
  have hExpReal : p.toReal * (q.toReal - 1) = q.toReal := by
    rw [mul_comm]
    exact hpqReal.symm.sub_one_mul_conj
  have hExp : p * ENNReal.ofReal (q.toReal - 1) = q := by
    calc
      p * ENNReal.ofReal (q.toReal - 1) =
          ENNReal.ofReal p.toReal * ENNReal.ofReal (q.toReal - 1) := by
        rw [ENNReal.ofReal_toReal hpTop]
      _ = ENNReal.ofReal (p.toReal * (q.toReal - 1)) := by
        rw [ENNReal.ofReal_mul (ENNReal.toReal_nonneg)]
      _ = ENNReal.ofReal q.toReal := by rw [hExpReal]
      _ = q := ENNReal.ofReal_toReal hqTop
  let k : X → ℂ := rn.aestronglyMeasurable_kernel.mk rn.kernel
  have hkMeas : Measurable k := rn.aestronglyMeasurable_kernel.measurable_mk
  have hkEq : rn.kernel =ᵐ[mu] k := rn.aestronglyMeasurable_kernel.ae_eq_mk
  have hkInt : Integrable k mu := rn.integrable_kernel.congr hkEq
  let a : ℕ → X → ℝ := fun n x => min ‖k x‖ (n : ℝ)
  have haMeas (n : ℕ) : Measurable (a n) := hkMeas.norm.min measurable_const
  have haNonneg (n : ℕ) (x : X) : 0 ≤ a n x := by
    exact le_min (norm_nonneg _) (Nat.cast_nonneg n)
  have haNorm (n : ℕ) (x : X) : ‖a n x‖ = a n x :=
    Real.norm_of_nonneg (haNonneg n x)
  have haLeKernel (n : ℕ) (x : X) : a n x ≤ ‖k x‖ := min_le_left _ _
  have haBound (n : ℕ) (x : X) : a n x ≤ n := min_le_right _ _
  have haLp (n : ℕ) : MemLp (a n) q mu :=
    MemLp.of_bound (haMeas n).aestronglyMeasurable n
      (Filter.Eventually.of_forall fun x => by simpa [haNorm] using haBound n x)
  have haTend : ∀ᵐ x ∂mu,
      Filter.Tendsto (fun n => a n x) Filter.atTop (𝓝 ‖k x‖) := by
    filter_upwards with x
    apply tendsto_nhds_of_eventually_eq
    obtain ⟨N, hN⟩ := exists_nat_ge ‖k x‖
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    simp [a, min_eq_left (hN.trans (Nat.cast_le.mpr hn))]
  have haNormBound (n : ℕ) : eLpNorm (a n) q mu ≤ ENNReal.ofReal ‖L‖ := by
    let test : X → ℂ := fun x =>
      dualPhase (k x) * (((a n x) ^ (q.toReal - 1) : ℝ) : ℂ)
    have htestMeas : AEStronglyMeasurable test mu := by
      apply Measurable.aestronglyMeasurable
      exact (measurable_dualPhase.comp hkMeas).mul
        (Complex.measurable_ofReal.comp
          ((Real.continuous_rpow_const hrPos.le).measurable.comp (haMeas n)))
    have htestNorm (x : X) : ‖test x‖ = (a n x) ^ (q.toReal - 1) := by
      by_cases hk0 : k x = 0
      · have ha0 : a n x = 0 := by simp [a, hk0]
        simp [test, hk0, ha0, Real.zero_rpow hrPos.ne']
      · have hphase : ‖dualPhase (k x)‖ = 1 := by
          simp [dualPhase, norm_inv, hk0]
        dsimp only [test]
        rw [norm_mul, hphase, one_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (haNonneg n x) _)]
    have htestBound : ∀ᵐ x ∂mu, ‖test x‖ ≤ (n : ℝ) ^ (q.toReal - 1) :=
      Filter.Eventually.of_forall fun x => by
        rw [htestNorm]
        exact Real.rpow_le_rpow (haNonneg n x) (haBound n x) hrPos.le
    have htestLp : MemLp test p mu :=
      MemLp.of_bound htestMeas ((n : ℝ) ^ (q.toReal - 1)) htestBound
    have hformula := lp_functional_eq_integral_of_ae_bound mu p hp L rn test
      htestMeas htestLp ((n : ℝ) ^ (q.toReal - 1))
      (Real.rpow_nonneg (Nat.cast_nonneg n) _) htestBound
    have hpairAE : (fun x => test x * rn.kernel x) =ᵐ[mu]
        fun x => ((‖k x‖ * (a n x) ^ (q.toReal - 1) : ℝ) : ℂ) := by
      filter_upwards [hkEq] with x hxk
      rw [hxk]
      by_cases hk0 : k x = 0
      · simp [test, hk0]
      · dsimp only [test]
        calc
          (dualPhase (k x) * ↑((a n x) ^ (q.toReal - 1))) * k x =
              (dualPhase (k x) * k x) * ↑((a n x) ^ (q.toReal - 1)) := by ring
          _ = ↑‖k x‖ * ↑((a n x) ^ (q.toReal - 1)) := by
            rw [dualPhase_mul (k x) hk0]
          _ = ↑(‖k x‖ * (a n x) ^ (q.toReal - 1)) := by push_cast; ring
    have hrightInt : Integrable (fun x => ‖k x‖ * (a n x) ^ (q.toReal - 1)) mu := by
      have hpowMeas : AEStronglyMeasurable
          (fun x => (a n x) ^ (q.toReal - 1)) mu := by
        apply Measurable.aestronglyMeasurable
        fun_prop
      have hpowInt : Integrable
          (fun x => (a n x) ^ (q.toReal - 1) * ‖k x‖) mu :=
        (ContinuousLinearMap.mul ℝ ℝ).integrable_of_bilin_of_bdd_left
          ((n : ℝ) ^ (q.toReal - 1)) hpowMeas
          (Filter.Eventually.of_forall fun x => by
            rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (haNonneg n x) _)]
            exact Real.rpow_le_rpow (haNonneg n x) (haBound n x) hrPos.le)
          hkInt.norm
      exact hpowInt.congr (Filter.Eventually.of_forall fun x => by
        dsimp only
        rw [mul_comm])
    have hformula' : L (htestLp.toLp test) =
        ((∫ x, ‖k x‖ * (a n x) ^ (q.toReal - 1) ∂mu : ℝ) : ℂ) := by
      rw [hformula]
      calc
        (∫ x, test x * rn.kernel x ∂mu) =
            ∫ x, ((‖k x‖ * (a n x) ^ (q.toReal - 1) : ℝ) : ℂ) ∂mu :=
          integral_congr_ae hpairAE
        _ = ((∫ x, ‖k x‖ * (a n x) ^ (q.toReal - 1) ∂mu : ℝ) : ℂ) :=
          integral_complex_ofReal
    have haPowInt : Integrable (fun x => (a n x) ^ q.toReal) mu :=
      (haLp n).integrable_norm_rpow hqZero hqTop |>.congr
        (Filter.Eventually.of_forall fun x => by
          exact congrArg (fun t : ℝ => t ^ q.toReal) (haNorm n x))
    have hpowPoint (x : X) : (a n x) ^ q.toReal ≤
        ‖k x‖ * (a n x) ^ (q.toReal - 1) := by
      by_cases ha0 : a n x = 0
      · simp [ha0, Real.zero_rpow hqRealPos.ne', Real.zero_rpow hrPos.ne']
      · have hapos : 0 < a n x := lt_of_le_of_ne (haNonneg n x) (Ne.symm ha0)
        calc
          (a n x) ^ q.toReal = (a n x) ^ (1 + (q.toReal - 1)) := by
            congr 1
            all_goals ring
          _ = a n x * (a n x) ^ (q.toReal - 1) := by
            rw [Real.rpow_add hapos, Real.rpow_one]
          _ ≤ ‖k x‖ * (a n x) ^ (q.toReal - 1) :=
            mul_le_mul_of_nonneg_right (haLeKernel n x)
              (Real.rpow_nonneg (haNonneg n x) _)
    have hlower : (∫ x, (a n x) ^ q.toReal ∂mu) ≤
        ∫ x, ‖k x‖ * (a n x) ^ (q.toReal - 1) ∂mu :=
      integral_mono haPowInt hrightInt hpowPoint
    have hrightNonneg : 0 ≤ ∫ x, ‖k x‖ * (a n x) ^ (q.toReal - 1) ∂mu :=
      integral_nonneg fun x => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (haNonneg n x) _)
    have hupper : (∫ x, ‖k x‖ * (a n x) ^ (q.toReal - 1) ∂mu) ≤
        ‖L‖ * (eLpNorm (a n) q mu).toReal ^ (q.toReal - 1) := by
      have hop := L.le_opNorm (htestLp.toLp test)
      rw [hformula', Lp.norm_toLp] at hop
      have htestELp : eLpNorm test p mu =
          eLpNorm (a n) q mu ^ (q.toReal - 1) := by
        calc
          eLpNorm test p mu = eLpNorm (fun x => ‖a n x‖ ^ (q.toReal - 1)) p mu := by
            apply eLpNorm_congr_norm_ae
            exact Filter.Eventually.of_forall fun x => by
              rw [htestNorm, Real.norm_eq_abs,
                abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), haNorm]
          _ = eLpNorm (a n) (p * ENNReal.ofReal (q.toReal - 1)) mu ^
                (q.toReal - 1) := eLpNorm_norm_rpow (a n) hrPos
          _ = eLpNorm (a n) q mu ^ (q.toReal - 1) := by rw [hExp]
      rw [htestELp, ← ENNReal.toReal_rpow] at hop
      simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hrightNonneg] using hop
    let A : ℝ := (eLpNorm (a n) q mu).toReal
    have hA_nonneg : 0 ≤ A := ENNReal.toReal_nonneg
    have hAq : (∫ x, (a n x) ^ q.toReal ∂mu) = A ^ q.toReal := by
      have hJnonneg : 0 ≤ ∫ x, (a n x) ^ q.toReal ∂mu :=
        integral_nonneg fun x => Real.rpow_nonneg (haNonneg n x) _
      have hENN : ENNReal.ofReal (∫ x, (a n x) ^ q.toReal ∂mu) =
          eLpNorm (a n) q mu ^ q.toReal := by
        rw [ofReal_integral_eq_lintegral_ofReal haPowInt
          (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (haNonneg n x) _)]
        calc
          (∫⁻ x, ENNReal.ofReal ((a n x) ^ q.toReal) ∂mu) =
              ∫⁻ x, ‖a n x‖ₑ ^ q.toReal ∂mu := by
            apply lintegral_congr
            intro x
            rw [Real.enorm_eq_ofReal (haNonneg n x)]
            simpa using
              (ENNReal.ofReal_rpow_of_nonneg (haNonneg n x) hqRealPos.le).symm
          _ = eLpNorm' (a n) q.toReal mu ^ q.toReal :=
            lintegral_rpow_enorm_eq_rpow_eLpNorm' hqRealPos
          _ = eLpNorm (a n) q mu ^ q.toReal := by
            rw [eLpNorm_eq_eLpNorm' hqZero hqTop]
      have hreal := congrArg ENNReal.toReal hENN
      simpa [ENNReal.toReal_ofReal hJnonneg, A, ENNReal.toReal_rpow] using hreal
    have hApow : A ^ q.toReal ≤ ‖L‖ * A ^ (q.toReal - 1) := by
      rw [← hAq]
      exact hlower.trans hupper
    have hAle : A ≤ ‖L‖ := by
      by_cases hA0 : A = 0
      · simp [hA0]
      · have hApos : 0 < A := lt_of_le_of_ne hA_nonneg (Ne.symm hA0)
        have hfactor : A ^ q.toReal = A * A ^ (q.toReal - 1) := by
          calc
            A ^ q.toReal = A ^ (1 + (q.toReal - 1)) := by
              congr 1
              all_goals ring
            _ = A * A ^ (q.toReal - 1) := by
              rw [Real.rpow_add hApos, Real.rpow_one]
        rw [hfactor] at hApow
        exact le_of_mul_le_mul_right hApow (Real.rpow_pos_of_pos hApos _)
    rw [← ENNReal.ofReal_toReal (haLp n).2.ne]
    exact ENNReal.ofReal_le_ofReal hAle
  have hkNormBound : eLpNorm (fun x => ‖k x‖) q mu ≤ ENNReal.ofReal ‖L‖ :=
    Lp.eLpNorm_le_of_ae_tendsto (Filter.Eventually.of_forall haNormBound)
      (fun n => (haMeas n).aestronglyMeasurable) haTend
  have hkBound : eLpNorm k q mu ≤ ENNReal.ofReal ‖L‖ := by
    simpa using hkNormBound
  have hkernelBound : eLpNorm rn.kernel q mu ≤ ENNReal.ofReal ‖L‖ := by
    rw [eLpNorm_congr_ae hkEq]
    exact hkBound
  exact ⟨⟨rn.aestronglyMeasurable_kernel,
    hkernelBound.trans_lt ENNReal.ofReal_lt_top⟩, hkernelBound⟩

/- Proof idea: use bounded conjugate-phase indicators of rational superlevel sets,
prove their measures vanish, and obtain the essential bound and top membership. -/
theorem rnKernel_memLp_top_of_p_eq_one {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [IsFiniteMeasure mu] (p : ENNReal) (hp : 1 ≤ p)
    (L : letI : Fact (1 ≤ p) := ⟨hp⟩; Lp ℂ p mu →L[ℂ] ℂ)
    (rn : LpRNKernelData mu p hp L)
    (hpOne : p = 1) :
    MemLp rn.kernel ∞ mu ∧ ∀ᵐ x ∂mu, ‖rn.kernel x‖ ≤ ‖L‖ := by
  subst p
  let k : X → ℂ := rn.aestronglyMeasurable_kernel.mk rn.kernel
  have hkMeas : Measurable k := rn.aestronglyMeasurable_kernel.measurable_mk
  have hkEq : rn.kernel =ᵐ[mu] k := rn.aestronglyMeasurable_kernel.ae_eq_mk
  have hkInt : Integrable k mu := rn.integrable_kernel.congr hkEq
  have hnull : mu {x | ‖k x‖ > ‖L‖} = 0 := by
    let E : ℕ → Set X := fun n => {x | ‖L‖ + 1 / (n + 1 : ℝ) < ‖k x‖}
    have hset : {x | ‖k x‖ > ‖L‖} = ⋃ n, E n := by
      ext x
      simp only [mem_iUnion, mem_setOf_eq]
      constructor
      · intro hx
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hx)
        refine ⟨n, ?_⟩
        dsimp only [E]
        calc
          ‖L‖ + 1 / (n + 1 : ℝ) < ‖L‖ + (‖k x‖ - ‖L‖) := by
            simpa [add_comm] using add_lt_add_left hn ‖L‖
          _ = ‖k x‖ := by ring
      · rintro ⟨n, hn⟩
        exact lt_of_le_of_lt (le_add_of_nonneg_right
          (show 0 ≤ (1 / (n + 1 : ℝ)) by positivity)) hn
    rw [hset]
    apply measure_iUnion_null
    intro n
    dsimp only [E]
    let eps : ℝ := 1 / (n + 1 : ℝ)
    let E : Set X := {x | ‖L‖ + eps < ‖k x‖}
    have heps : 0 < eps := by positivity
    have hE : MeasurableSet E := measurableSet_Ioi.preimage hkMeas.norm
    by_contra hEnull
    have hEreal : 0 < mu.real E := by
      rw [measureReal_def]
      exact ENNReal.toReal_pos hEnull (measure_ne_top mu E)
    let test : X → ℂ := E.indicator (fun x => dualPhase (k x))
    have htestMeas : AEStronglyMeasurable test mu :=
      ((measurable_dualPhase.comp hkMeas).aestronglyMeasurable.indicator hE)
    have htestBound : ∀ᵐ x ∂mu, ‖test x‖ ≤ 1 :=
      Filter.Eventually.of_forall fun x => by
        by_cases hx : x ∈ E
        · simpa [test, hx] using norm_dualPhase_le_one (k x)
        · simp [test, hx]
    have htestLp : MemLp test 1 mu := MemLp.of_bound htestMeas 1 htestBound
    have hformula := lp_functional_eq_integral_of_ae_bound mu 1 le_rfl L rn
      test htestMeas htestLp 1 zero_le_one htestBound
    have hpairAE : (fun x => test x * rn.kernel x) =ᵐ[mu]
        fun x => E.indicator (fun x => (‖k x‖ : ℂ)) x := by
      filter_upwards [hkEq] with x hxk
      by_cases hx : x ∈ E
      · have hk0 : k x ≠ 0 := by
          intro hkzero
          have : ‖L‖ + eps < 0 := by simpa [E, hkzero] using hx
          linarith [norm_nonneg L, heps]
        simp [test, hx, hxk, dualPhase_mul (k x) hk0]
      · simp [test, hx]
    have hformula' : L (htestLp.toLp test) =
        ((∫ x in E, ‖k x‖ ∂mu : ℝ) : ℂ) := by
      rw [hformula]
      calc
        (∫ x, test x * rn.kernel x ∂mu) =
            ∫ x, E.indicator (fun x => (‖k x‖ : ℂ)) x ∂mu :=
          integral_congr_ae hpairAE
        _ = ∫ x in E, (‖k x‖ : ℂ) ∂mu := integral_indicator hE
        _ = ((∫ x in E, ‖k x‖ ∂mu : ℝ) : ℂ) := integral_complex_ofReal
    have htestNorm : ‖htestLp.toLp test‖ ≤ mu.real E := by
      rw [Lp.norm_toLp, eLpNorm_one_eq_lintegral_enorm]
      have hlin : (∫⁻ x, ‖test x‖ₑ ∂mu) ≤ mu E := by
        calc
          (∫⁻ x, ‖test x‖ₑ ∂mu) ≤ ∫⁻ x, E.indicator (fun _ => (1 : ENNReal)) x ∂mu := by
            apply lintegral_mono
            intro x
            by_cases hx : x ∈ E
            · simpa [test, hx, enorm_eq_nnnorm] using
                ENNReal.coe_le_coe.mpr (norm_dualPhase_le_one (k x))
            · simp [test, hx]
          _ = mu E := by simp [lintegral_indicator, hE]
      rw [measureReal_def]
      exact ENNReal.toReal_mono (measure_ne_top mu E) hlin
    have hupperNorm : ‖L (htestLp.toLp test)‖ ≤ ‖L‖ * mu.real E :=
      (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left htestNorm (norm_nonneg L))
    have hIntNonneg : 0 ≤ ∫ x in E, ‖k x‖ ∂mu :=
      integral_nonneg fun _ => norm_nonneg _
    have hupper : (∫ x in E, ‖k x‖ ∂mu : ℝ) ≤ ‖L‖ * mu.real E := by
      rw [hformula'] at hupperNorm
      simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hIntNonneg] using hupperNorm
    have hlower : (‖L‖ + eps) * mu.real E ≤ ∫ x in E, ‖k x‖ ∂mu := by
      have hconstInt : IntegrableOn (fun _ : X => ‖L‖ + eps) E mu := integrableOn_const
      have hnormInt : IntegrableOn (fun x => ‖k x‖) E mu := hkInt.norm.integrableOn
      have hmono : (fun _ : X => ‖L‖ + eps) ≤ᵐ[mu.restrict E] fun x => ‖k x‖ := by
        filter_upwards [ae_restrict_mem hE] with x hx
        exact le_of_lt hx
      have hle := integral_mono_ae hconstInt hnormInt hmono
      simpa [Measure.restrict_apply_univ, hE, integral_const, mul_comm] using hle
    nlinarith
  have hkBound : ∀ᵐ x ∂mu, ‖k x‖ ≤ ‖L‖ := by
    rw [ae_iff]
    simpa only [not_le] using hnull
  have hkernelBound : ∀ᵐ x ∂mu, ‖rn.kernel x‖ ≤ ‖L‖ := by
    filter_upwards [hkEq, hkBound] with x hxk hx
    simpa [hxk] using hx
  exact ⟨memLp_top_of_bound rn.aestronglyMeasurable_kernel ‖L‖ hkernelBound,
    hkernelBound⟩

/- Proof idea: split `p = 1` from `1 < p`, normalize the
conjugate exponent at the endpoint, and invoke the corresponding estimate. -/
theorem rnKernel_memLp_conjExponent {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [IsFiniteMeasure mu] (p : ENNReal) (hp : 1 ≤ p)
    (hpTop : p ≠ ∞)
    (L : letI : Fact (1 ≤ p) := ⟨hp⟩; Lp ℂ p mu →L[ℂ] ℂ)
    (rn : LpRNKernelData mu p hp L) :
    MemLp rn.kernel (ENNReal.conjExponent p) mu := by
  by_cases hpOne : p = 1
  · have htop :=
      (rnKernel_memLp_top_of_p_eq_one mu p hp L rn hpOne).1
    simpa [hpOne, ENNReal.conjExponent] using htop
  · have hpOne' : 1 < p := lt_of_le_of_ne hp (Ne.symm hpOne)
    exact (rnKernel_memLp_conjExponent_of_one_lt mu p hp hpOne' hpTop L rn).1

/- Proof idea: compare `L` with Mathlib's continuous `Lp` pairing and use equality
on the dense set of measurable finite-range classes. -/
theorem lp_functional_eq_integral_kernel {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [IsFiniteMeasure mu] (p : ENNReal) (hp : 1 ≤ p)
    (hpTop : p ≠ ∞)
    (L : letI : Fact (1 ≤ p) := ⟨hp⟩; Lp ℂ p mu →L[ℂ] ℂ)
    (rn : LpRNKernelData mu p hp L)
    (hgq : MemLp rn.kernel (ENNReal.conjExponent p) mu) (h : Lp ℂ p mu) :
    L h = ∫ x, (h : X → ℂ) x * rn.kernel x ∂mu := by
  let q := ENNReal.conjExponent p
  letI hpFact : Fact (1 ≤ p) := ⟨hp⟩
  letI hpq : p.HolderConjugate q := ENNReal.HolderConjugate.conjExponent hp
  letI hqFact : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  let g : Lp ℂ q mu := hgq.toLp rn.kernel
  let P : Lp ℂ p mu →L[ℂ] ℂ :=
    ((ContinuousLinearMap.mul ℂ ℂ).lpPairing mu p q).flip g
  have hLP : L = P := by
    have hEqOn : Set.EqOn (L : Lp ℂ p mu → ℂ) P
        (Set.range (Subtype.val : Lp.simpleFunc ℂ p mu → Lp ℂ p mu)) := by
      rintro y ⟨s, rfl⟩
      let v : X → ℂ := Lp.simpleFunc.toSimpleFunc s
      have hv : Measurable v := Lp.simpleFunc.measurable s
      have hvRange : Set.Finite (Set.range v) :=
        (Lp.simpleFunc.toSimpleFunc s).finite_range
      have hvLp : MemLp v p mu := Lp.simpleFunc.memLp s
      rw [← Lp.simpleFunc.toLp_toSimpleFunc s]
      rw [lp_functional_eq_integral_simple mu p hp L rn v hv hvRange hvLp]
      rw [show P (hvLp.toLp v) =
          ∫ x, ((hvLp.toLp v : Lp ℂ p mu) : X → ℂ) x * (g : X → ℂ) x ∂mu by
        simpa [P] using
          (ContinuousLinearMap.lpPairing_eq_integral
            (ContinuousLinearMap.mul ℂ ℂ)
            (hvLp.toLp v) g)]
      apply integral_congr_ae
      filter_upwards [hvLp.coeFn_toLp, hgq.coeFn_toLp] with x hxv hxg
      change (g : X → ℂ) x = rn.kernel x at hxg
      rw [hxv, hxg]
    have hfun : (L : Lp ℂ p mu → ℂ) = P :=
      L.continuous.ext_on (Lp.simpleFunc.denseRange hpTop) P.continuous hEqOn
    exact ContinuousLinearMap.ext fun x => congrFun hfun x
  calc
    L h = P h := DFunLike.congr_fun hLP h
    _ = ∫ x, (h : X → ℂ) x * (g : X → ℂ) x ∂mu := by
      simpa [P] using
        (ContinuousLinearMap.lpPairing_eq_integral
          (ContinuousLinearMap.mul ℂ ℂ) h g)
    _ = ∫ x, (h : X → ℂ) x * rn.kernel x ∂mu := by
      apply integral_congr_ae
      filter_upwards [hgq.coeFn_toLp] with x hxg
      change (g : X → ℂ) x = rn.kernel x at hxg
      rw [hxg]

/- Proof idea: store exactly the unconjugated kernel, its strong measurability and
conjugate-exponent membership, and the all-`Lp` representation formula. -/
structure LpKernelRepresentation {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (p : ENNReal) (hp : 1 ≤ p)
    (L : letI : Fact (1 ≤ p) := ⟨hp⟩; Lp ℂ p mu →L[ℂ] ℂ) where
  kernel : X → ℂ
  aestronglyMeasurable_kernel : AEStronglyMeasurable kernel mu
  memLp_kernel : MemLp kernel (ENNReal.conjExponent p) mu
  formula : ∀ h : Lp ℂ p mu,
    L h = ∫ x, (h : X → ℂ) x * kernel x ∂mu

/- Proof idea: choose `exists_LpRNKernelData`'s RN kernel, prove
membership and the full formula using `rnKernel_memLp_conjExponent` and `lp_functional_eq_integral_kernel`, and fill `LpKernelRepresentation`. -/
theorem exists_LpKernelRepresentation {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [SigmaFinite mu] [IsFiniteMeasure mu]
    (p : ENNReal) (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (L : letI : Fact (1 ≤ p) := ⟨hp⟩; Lp ℂ p mu →L[ℂ] ℂ) :
    Nonempty (LpKernelRepresentation mu p hp L) := by
  letI : Fact (1 ≤ p) := ⟨hp⟩
  let rn := (exists_LpRNKernelData mu p hp hpTop L).some
  have hgq : MemLp rn.kernel (ENNReal.conjExponent p) mu :=
    rnKernel_memLp_conjExponent mu p hp hpTop L rn
  exact ⟨{
    kernel := rn.kernel
    aestronglyMeasurable_kernel := rn.aestronglyMeasurable_kernel
    memLp_kernel := hgq
    formula := fun h => lp_functional_eq_integral_kernel mu p hp hpTop L rn hgq h
  }⟩

end Theorem12.Generic
