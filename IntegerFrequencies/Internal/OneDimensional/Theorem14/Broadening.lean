import Theorem14.Definitions
import Theorem14.Window
import Theorem14.FejerKernel
import Theorem14.FejerApproximation
import Theorem14.FourierSynthesis
import Theorem14.WeightedOrbitSummability

/-! # Theorem 1.4: canonical broadening and support -/

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace Theorem14.Internal

/- Proof idea: prove coefficient norm summability, then use the exact Fourier-series HasSum. -/
lemma fourierSynthesis_windowTranslate
    (epsilon : ℝ) (he0 : 0 < epsilon) (he1 : epsilon < 1)
    (a : AddCircle (1 : ℝ)) :
    fourierSynthesis (fun k : ℤ => fourier (-k) a * windowCoeff epsilon k) =
      tentWindowTranslate epsilon he0 he1 a := by
  /- Proof idea: `summable_windowCoeff_and_tsum_norm` and character norm one give summability of the modulated coefficient norms.
  `fourierCoeff_tentWindowTranslate` rewrites them as the actual coefficients of the continuous translate. Convert norm
  summability with `summable_norm_iff.mp`, apply `hasSum_fourier_series_of_summable`, and use
  `HasSum.tsum_eq` plus the transparent synthesis definition. This is the sole route; Fourier
  uniqueness and alternate direct-series routes are not used. -/
  have hc : Summable (fun k : ℤ =>
      ‖fourier (-k) a * windowCoeff epsilon k‖) := by
    simpa [norm_mul, fourier_apply] using
      (summable_windowCoeff_and_tsum_norm epsilon he0 he1).1
  have hcoeff : ∀ k : ℤ,
      fourierCoeff (tentWindowTranslate epsilon he0 he1 a) k =
        fourier (-k) a * windowCoeff epsilon k :=
    fourierCoeff_tentWindowTranslate epsilon he0 he1 a
  rw [fourierSynthesis]
  calc
    (∑' k : ℤ, (fourier (-k) a * windowCoeff epsilon k) •
        (fourier k : C(AddCircle (1 : ℝ), ℂ))) =
        ∑' k : ℤ, fourierCoeff (tentWindowTranslate epsilon he0 he1 a) k •
          (fourier k : C(AddCircle (1 : ℝ), ℂ)) := by
            apply tsum_congr
            intro k
            rw [hcoeff k]
    _ = tentWindowTranslate epsilon he0 he1 a := by
      apply HasSum.tsum_eq
      apply hasSum_fourier_series_of_summable
      apply summable_norm_iff.mp
      simpa only [hcoeff] using hc

/- Proof idea: expand only the finite Fejer sum and rewrite each inner synthesis by `fourierSynthesis_windowTranslate`. -/
private theorem broadenedFunction_fejerMean_eq_translateSum
    (epsilon alpha : ℝ) (he0 : 0 < epsilon) (he1 : epsilon < 1)
    (f : AddCircle (1 : ℝ) → ℂ) (N : ℕ) (x : AddCircle (1 : ℝ)) :
    broadenedFunction epsilon alpha (fejerMean N f) x =
      ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        ((fejerMultiplier N n : ℂ) * fourierCoeff f n * fourier n x) •
          tentWindowTranslate epsilon he0 he1
            ((((n : ℤ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ)) := by
  /- Proof idea: Expand the literal finite `fejerMean`. Rewrite each orbit value by character multiplicativity
  as a finite sum over `n`; its `k`-sequence is `fourier (-k) ((((n:Real)*alpha):Real):AddCircle
  1) * windowCoeff epsilon k`. Use finite-sum linearity under `summable_windowCoeff_and_tsum_norm`'s summability and
  rewrite every inner synthesis with `fourierSynthesis_windowTranslate`. No two infinite sums are interchanged. -/
  classical
  let s : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)
  let a : ℤ → AddCircle (1 : ℝ) := fun n =>
    ((((n : ℤ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ))
  let A : ℤ → ℂ := fun n =>
    (fejerMultiplier N n : ℂ) * fourierCoeff f n * fourier n x
  have hphase (n k : ℤ) :
      fourier n
          (x - ((((k : ℤ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ))) =
        fourier n x * fourier (-k) (a n) := by
    calc
      fourier n
          (x - ((((k : ℤ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ))) =
          fourier n x *
            fourier n
              (-((((k : ℤ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ))) := by
        simp only [sub_eq_add_neg, fourier_apply, zsmul_add,
          AddCircle.toCircle_add, Circle.coe_mul]
      _ = fourier n x * fourier (-k) (a n) := by
        congr 1
        rw [show a n =
          ((((n : ℤ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ)) by rfl]
        rw [← AddCircle.coe_neg]
        rw [fourier_coe_apply, fourier_coe_apply]
        congr 1
        push_cast
        ring
  have hcoeff (k : ℤ) :
      weightedOrbitCoeff epsilon alpha (fejerMean N f) x k =
        ∑ n ∈ s, A n *
          (fourier (-k) (a n) * windowCoeff epsilon k) := by
    rw [weightedOrbitCoeff, fejerMean]
    simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [hphase n k]
    simp only [A, a]
    ring
  have hbase (n : ℤ) : Summable (fun k : ℤ =>
      (fourier (-k) (a n) * windowCoeff epsilon k) •
        (fourier k : C(AddCircle (1 : ℝ), ℂ))) := by
    apply Summable.of_norm
    simpa [norm_smul, fourier_norm, norm_mul, fourier_apply] using
      (summable_windowCoeff_and_tsum_norm epsilon he0 he1).1
  have hterms : ∀ n ∈ s, Summable (fun k : ℤ =>
      A n • ((fourier (-k) (a n) * windowCoeff epsilon k) •
        (fourier k : C(AddCircle (1 : ℝ), ℂ)))) := by
    intro n hn
    exact (hbase n).const_smul (A n)
  rw [broadenedFunction, fourierSynthesis]
  calc
    (∑' k : ℤ, weightedOrbitCoeff epsilon alpha (fejerMean N f) x k •
        (fourier k : C(AddCircle (1 : ℝ), ℂ))) =
        ∑' k : ℤ, ∑ n ∈ s,
          A n • ((fourier (-k) (a n) * windowCoeff epsilon k) •
            (fourier k : C(AddCircle (1 : ℝ), ℂ))) := by
              apply tsum_congr
              intro k
              rw [hcoeff k]
              calc
                (∑ n ∈ s, A n *
                    (fourier (-k) (a n) * windowCoeff epsilon k)) •
                    (fourier k : C(AddCircle (1 : ℝ), ℂ)) =
                    ∑ n ∈ s,
                      (A n * (fourier (-k) (a n) *
                        windowCoeff epsilon k)) •
                        (fourier k : C(AddCircle (1 : ℝ), ℂ)) :=
                  Finset.sum_smul (R := ℂ)
                    (M := C(AddCircle (1 : ℝ), ℂ))
                    (f := fun n => A n *
                      (fourier (-k) (a n) * windowCoeff epsilon k))
                    (s := s) (x := (fourier k : C(AddCircle (1 : ℝ), ℂ)))
                _ = ∑ n ∈ s,
                    A n • ((fourier (-k) (a n) * windowCoeff epsilon k) •
                      (fourier k : C(AddCircle (1 : ℝ), ℂ))) := by
                  apply Finset.sum_congr rfl
                  intro n hn
                  rw [mul_smul]
    _ = ∑ n ∈ s, ∑' k : ℤ,
          A n • ((fourier (-k) (a n) * windowCoeff epsilon k) •
            (fourier k : C(AddCircle (1 : ℝ), ℂ))) :=
      Summable.tsum_finsetSum hterms
    _ = ∑ n ∈ s, A n • ∑' k : ℤ,
          (fourier (-k) (a n) * windowCoeff epsilon k) •
            (fourier k : C(AddCircle (1 : ℝ), ℂ)) := by
              apply Finset.sum_congr rfl
              intro n hn
              exact (hbase n).tsum_const_smul (A n)
    _ = ∑ n ∈ s,
          A n • tentWindowTranslate epsilon he0 he1 (a n) := by
              apply Finset.sum_congr rfl
              intro n hn
              change A n • fourierSynthesis
                (fun k : ℤ =>
                  fourier (-k) (a n) * windowCoeff epsilon k) =
                A n • tentWindowTranslate epsilon he0 he1 (a n)
              rw [fourierSynthesis_windowTranslate epsilon he0 he1 (a n)]
    _ = ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        ((fejerMultiplier N n : ℂ) * fourierCoeff f n * fourier n x) •
          tentWindowTranslate epsilon he0 he1
            ((((n : ℤ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ)) := by
      rfl

/- Proof idea: delete selected terms and prove literal no-wrap support for the others. -/
private lemma supported_broadenedFunction_fejerMean
    {alpha v epsilon : ℝ} {f : AddCircle (1 : ℝ) → ℂ}
    (hv0 : 0 < v) (hv1 : v < 1)
    (he0 : 0 < epsilon) (hev : epsilon < v)
    (hzero : ∀ n ∈ integerFrequencyIndexSet alpha v, fourierCoeff f n = 0)
    (N : ℕ) (x : AddCircle (1 : ℝ)) :
    SupportedInInitialArc
      (broadenedFunction epsilon alpha (fejerMean N f) x)
      (1 - v + epsilon) := by
  /- Proof idea: Selected finite terms vanish by `hzero`. A nonselected integer has fractional part `<1-v`;
  translating the literal `[0,epsilon]` tent remains in `[0,1-v+epsilon]` without wrap because
  `epsilon<v`. Prove the representative no-wrap equality explicitly, not merely modulo one. -/
  have he1 : epsilon < 1 := lt_trans hev hv1
  intro t ht
  rw [broadenedFunction_fejerMean_eq_translateSum
    epsilon alpha he0 he1 f N x]
  simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply]
  apply Finset.sum_eq_zero
  intro n hn
  by_cases hselected : n ∈ integerFrequencyIndexSet alpha v
  · simp [hzero n hselected]
  · have hfractLt : Int.fract ((n : ℝ) * alpha) < 1 - v := by
      by_contra hnot
      apply hselected
      exact ⟨le_of_not_gt hnot, Int.fract_lt_one _⟩
    let a : AddCircle (1 : ℝ) :=
      ((((n : ℤ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ))
    let u : ℝ := Theorem12.Generic.unitRep (t - a)
    let r : ℝ := Int.fract ((n : ℝ) * alpha)
    change r < 1 - v at hfractLt
    have hr0 : 0 ≤ r := Int.fract_nonneg _
    have htranslate : tentWindowTranslate epsilon he0 he1 a t = 0 := by
      change tentWindow epsilon (t - a) = 0
      apply (tentWindow_formula_and_support epsilon he0 he1).2
      intro hu
      change u ∈ Set.Icc (0 : ℝ) epsilon at hu
      have haRep : Theorem12.Generic.unitRep a = r := by
        simp only [a, r, Theorem12.Generic.unitRep_coe_eq_fract]
      have ha : a = ((r : ℝ) : AddCircle (1 : ℝ)) := by
        rw [← haRep]
        exact (Theorem12.Generic.coe_unitRep a).symm
      have hta :
          t - a = ((u : ℝ) : AddCircle (1 : ℝ)) := by
        exact (Theorem12.Generic.coe_unitRep (t - a)).symm
      have htCoe : t = ((u + r : ℝ) : AddCircle (1 : ℝ)) := by
        calc
          t = (t - a) + a := by abel
          _ = ((u : ℝ) : AddCircle (1 : ℝ)) +
              ((r : ℝ) : AddCircle (1 : ℝ)) := by rw [hta, ha]
          _ = ((u + r : ℝ) : AddCircle (1 : ℝ)) := by
            rw [AddCircle.coe_add]
      have hurIco : u + r ∈ Set.Ico (0 : ℝ) 1 := by
        constructor
        · exact add_nonneg hu.1 hr0
        · linarith [hu.2, hfractLt, hev]
      have htRep : Theorem12.Generic.unitRep t = u + r := by
        rw [htCoe, Theorem12.Generic.unitRep_coe_eq_fract,
          Int.fract_eq_self.mpr hurIco]
      apply ht
      rw [htRep]
      constructor
      · exact hurIco.1
      · linarith [hu.2, hfractLt]
    change ((fejerMultiplier N n : ℂ) * fourierCoeff f n * fourier n x) •
      tentWindowTranslate epsilon he0 he1 a t = 0
    rw [htranslate]
    simp

/- Proof idea: choose one approximation, use one good event, and pass pointwise support through uniform convergence. -/
theorem broadening_ae
    {alpha v epsilon : ℝ} {f : AddCircle (1 : ℝ) → ℂ}
    (hf : Integrable f AddCircle.haarAddCircle)
    (hv0 : 0 < v) (hv1 : v < 1)
    (he0 : 0 < epsilon) (hev : epsilon < v)
    (hzero : ∀ n ∈ integerFrequencyIndexSet alpha v, fourierCoeff f n = 0) :
    ∀ᵐ x ∂AddCircle.haarAddCircle,
      BroadeningData epsilon alpha v f x := by
  /- Proof idea: Choose one Fejer approximation and restrict to `weightedApproximationAt_ae`'s good event. Every stage has
  literal initial-arc support by `supported_broadenedFunction_fejerMean`. The nonnegative `summable_errorNorm` terms tend to
  zero only after their genuine stagewise sums are available; `norm_fourierSynthesis_sub_le` then gives uniform
  convergence to the canonical target synthesis. Pass literal zeros through the uniform limit
  and fill coefficient equality with `fourierCoeff_fourierSynthesis`. -/
  have he1 : epsilon < 1 := lt_trans hev hv1
  obtain ⟨A⟩ := exists_fejerApproximation hf
  filter_upwards [weightedApproximationAt_ae hf A he0 he1] with x hx
  let G : ℕ → C(AddCircle (1 : ℝ), ℂ) := fun j =>
    broadenedFunction epsilon alpha (fejerMean (A.index j) f) x
  let G0 : C(AddCircle (1 : ℝ), ℂ) :=
    broadenedFunction epsilon alpha f x
  let E : ℕ → ℝ := fun j => ∑' k : ℤ,
    ‖weightedOrbitCoeff epsilon alpha
      (fun y => fejerMean (A.index j) f y - f y) x k‖
  have hcoeffSub (j : ℕ) (k : ℤ) :
      weightedOrbitCoeff epsilon alpha (fejerMean (A.index j) f) x k -
          weightedOrbitCoeff epsilon alpha f x k =
        weightedOrbitCoeff epsilon alpha
          (fun y => fejerMean (A.index j) f y - f y) x k := by
    unfold weightedOrbitCoeff
    ring
  have hdiffSummable (j : ℕ) : Summable (fun k : ℤ =>
      ‖weightedOrbitCoeff epsilon alpha (fejerMean (A.index j) f) x k -
        weightedOrbitCoeff epsilon alpha f x k‖) := by
    simpa only [hcoeffSub j] using hx.errorSummable j
  have hbound (j : ℕ) : ‖G j - G0‖ ≤ E j := by
    dsimp only [G, G0, E]
    change
      ‖fourierSynthesis
          (weightedOrbitCoeff epsilon alpha (fejerMean (A.index j) f) x) -
        fourierSynthesis (weightedOrbitCoeff epsilon alpha f x)‖ ≤ _
    calc
      ‖fourierSynthesis
          (weightedOrbitCoeff epsilon alpha (fejerMean (A.index j) f) x) -
          fourierSynthesis (weightedOrbitCoeff epsilon alpha f x)‖ ≤
          ∑' k : ℤ,
            ‖weightedOrbitCoeff epsilon alpha
                (fejerMean (A.index j) f) x k -
              weightedOrbitCoeff epsilon alpha f x k‖ :=
        norm_fourierSynthesis_sub_le
          (hx.stageSummable j) hx.targetSummable (hdiffSummable j)
      _ = ∑' k : ℤ,
          ‖weightedOrbitCoeff epsilon alpha
            (fun y => fejerMean (A.index j) f y - f y) x k‖ := by
        apply tsum_congr
        intro k
        rw [hcoeffSub j k]
  have hEtend : Tendsto E atTop (𝓝 0) := by
    exact hx.summable_errorNorm.tendsto_atTop_zero
  have hnormTend : Tendsto (fun j => ‖G j - G0‖) atTop (𝓝 0) :=
    squeeze_zero'
      (Filter.Eventually.of_forall fun j => norm_nonneg (G j - G0))
      (Filter.Eventually.of_forall hbound) hEtend
  have hGtend : Tendsto G atTop (𝓝 G0) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr hnormTend
  have hstageSupport (j : ℕ) :
      SupportedInInitialArc (G j) (1 - v + epsilon) := by
    dsimp only [G]
    exact supported_broadenedFunction_fejerMean
      hv0 hv1 he0 hev hzero (A.index j) x
  have htargetSupport :
      SupportedInInitialArc G0 (1 - v + epsilon) := by
    intro t ht
    have hstageZero (j : ℕ) : G j t = 0 := hstageSupport j t ht
    have hevalTend : Tendsto (fun j => G j t) atTop (𝓝 (G0 t)) :=
      ((continuous_eval_const t).tendsto G0).comp hGtend
    have hzeroTend : Tendsto (fun j => G j t) atTop (𝓝 0) := by
      have hseq : (fun j => G j t) = (fun _ : ℕ => (0 : ℂ)) := by
        funext j
        exact hstageZero j
      rw [hseq]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique hevalTend hzeroTend
  refine
    { coeffSummable := hx.targetSummable
      coeff_eq := ?_
      supported := ?_ }
  · intro k
    simpa only [broadenedFunction] using
      fourierCoeff_fourierSynthesis hx.targetSummable k
  · exact htargetSupport

end Theorem14.Internal
