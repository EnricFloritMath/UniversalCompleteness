import Theorem12.Definitions
import Theorem12.GenericAuxiliary
import Mathlib.Analysis.Fourier.AddCircle

/-!
# Theorem 1.4: definitions

Transparent definitions and proposition structures are centralized here.
The continuity field packages the triangular window.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace Theorem14

/- Proof idea: literal source selection. -/
def integerFrequencyIndexSet (alpha v : ℝ) : Set ℤ :=
  {n | Int.fract ((n : ℝ) * alpha) ∈ Set.Ico (1 - v) 1}

/- Proof idea: injective integer-cast image. -/
def integerFrequencySet (alpha v : ℝ) : Set ℝ :=
  (fun n : ℤ => (n : ℝ)) '' integerFrequencyIndexSet alpha v

/- Proof idea: literal restricted-L1 predicate. -/
def UniversalL1UniquenessBelow (Lambda : Set ℝ) (v : ℝ) : Prop :=
  ∀ (S : Set ℝ), MeasurableSet S → S ⊆ Set.Icc (0 : ℝ) 1 →
    volume S < ENNReal.ofReal v →
      ∀ (f : ℝ → ℂ), Integrable f (volume.restrict S) →
        (∀ xi ∈ Lambda, Theorem12.fourierSampleOn S f xi = 0) →
          f =ᵐ[volume.restrict S] (fun _ => 0)

namespace Internal

/- Proof idea: unfold image membership. -/
theorem intCast_mem_integerFrequencySet_iff
    (alpha v : ℝ) (n : ℤ) :
    (n : ℝ) ∈ integerFrequencySet alpha v ↔
      n ∈ integerFrequencyIndexSet alpha v := by
  /- Proof idea: Unfold `integerFrequencySet`. In the forward direction, extract its integer
  witness and use injectivity of the cast `ℤ → ℝ` to identify that witness
  with `n`. In reverse, use `n` itself as the image witness. No irrationality
  or range hypothesis on `v` may enter this coercion bridge. -/
  constructor
  · rintro ⟨m, hm, hmn⟩
    have hmn' : m = n := Int.cast_injective hmn
    simpa only [hmn'] using hm
  · intro hn
    exact ⟨n, hn, rfl⟩

/- Proof idea: finite inclusive count. -/
noncomputable def symmetricFourierZeroCount
    (g : AddCircle (1 : ℝ) → ℂ) (N : ℕ) : ℕ :=
  ((Finset.Icc (-(N : ℤ)) (N : ℤ)).filter fun k => fourierCoeff g k = 0).card

/- Proof idea: literal pointwise initial-arc support. -/
def SupportedInInitialArc (g : AddCircle (1 : ℝ) → ℂ) (L : ℝ) : Prop :=
  ∀ x, Theorem12.Generic.unitRep x ∉ Set.Icc (0 : ℝ) L → g x = 0

/- Proof idea: remove only endpoint one. -/
def normalizedCarrier (S : Set ℝ) : Set ℝ := S ∩ Set.Ico 0 1

/- Proof idea: literal zero extension. -/
noncomputable def realZeroExtension (S : Set ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  (normalizedCarrier S).indicator f

/- Proof idea: pull zero extension to AddCircle. -/
noncomputable def circleRepresentative
    (S : Set ℝ) (f : ℝ → ℂ) : AddCircle (1 : ℝ) → ℂ :=
  realZeroExtension S f ∘ Theorem12.Generic.unitRep

/- Proof idea: literal forward average. -/
def rotationAverage (alpha : ℝ) (phi : AddCircle (1 : ℝ) → ℂ)
    (N : ℕ) (x : AddCircle (1 : ℝ)) : ℂ :=
  (N : ℂ)⁻¹ * ∑ k ∈ Finset.range N,
    phi (x + ((((k : ℕ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ)))

/- Proof idea: literal representative preimage. -/
def circleInterval (a b : ℝ) : Set (AddCircle (1 : ℝ)) :=
  Theorem12.Generic.unitRep ⁻¹' Set.Ico a b

/- Proof idea: filtered finite range. -/
noncomputable def intervalVisitCount (alpha a b : ℝ) (N : ℕ)
    (x : AddCircle (1 : ℝ)) : ℕ := by
  classical
  exact ((Finset.range N).filter fun k =>
    x + ((((k : ℕ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ)) ∈ circleInterval a b).card

/- Proof idea: quantitative sandwich package. -/
structure IntervalIndicatorSandwich (a b eta : ℝ) where
  lower : C(AddCircle (1 : ℝ), ℝ)
  upper : C(AddCircle (1 : ℝ), ℝ)
  lower_nonneg : ∀ x, 0 ≤ lower x
  lower_le : ∀ x,
    lower x ≤ (circleInterval a b).indicator (fun _ => (1 : ℝ)) x
  le_upper : ∀ x,
    (circleInterval a b).indicator (fun _ => (1 : ℝ)) x ≤ upper x
  upper_le_one : ∀ x, upper x ≤ 1
  integral_lower : b - a - eta ≤
    ∫ x, lower x ∂AddCircle.haarAddCircle
  integral_upper : (∫ x, upper x ∂AddCircle.haarAddCircle) ≤ b - a + eta

/- Proof idea: literal half-open block count. -/
noncomputable def integerBlockCount (A : Set ℤ) (M : ℤ) (N : ℕ) : ℕ :=
  by
    classical
    exact ((Finset.Ico M (M + (N : ℤ))).filter fun n => n ∈ A).card

/- Proof idea: explicit uniform-in-origin predicate. -/
def HasUniformBlockDensity (A : Set ℤ) (D : ℝ) : Prop :=
  ∀ epsilon > 0, ∃ N0 : ℕ, ∀ N ≥ N0, 0 < N → ∀ M : ℤ,
    |(integerBlockCount A M N : ℝ) / (N : ℝ) - D| < epsilon

/- Proof idea: exact closed-interval block length. -/
def realIntervalBlockLength (x R : ℝ) : ℕ :=
  Int.toNat (Int.floor (x + R) - Int.ceil x + 1)

/- Proof idea: literal half-width box. -/
noncomputable def boxWindow (epsilon : ℝ) (x : AddCircle (1 : ℝ)) : ℂ :=
  if Theorem12.Generic.unitRep x ∈ Set.Icc 0 (epsilon / 2) then 1 else 0

/- Proof idea: literal Haar convolution. -/
noncomputable def tentWindow (epsilon : ℝ) (x : AddCircle (1 : ℝ)) : ℂ :=
  ∫ y, boxWindow epsilon y * boxWindow epsilon (x - y)
    ∂AddCircle.haarAddCircle

/- Proof idea: calculate the convolution on the three literal representative intervals. -/
theorem tentWindow_formula_and_support
    (epsilon : ℝ) (he0 : 0 < epsilon) (he1 : epsilon < 1) :
    (∀ x : AddCircle (1 : ℝ),
      let t := Theorem12.Generic.unitRep x
      tentWindow epsilon x =
        if t ≤ epsilon / 2 then (t : ℂ)
        else if t ≤ epsilon then ((epsilon - t : ℝ) : ℂ) else 0) ∧
      SupportedInInitialArc (tentWindow epsilon) epsilon := by
  /- Proof idea: Rewrite the Haar convolution as the measure of the intersection of its two
  half-width interval constraints. Compute the length separately for
  `t ≤ epsilon / 2`, `epsilon / 2 ≤ t ≤ epsilon`, and `epsilon < t`, using
  `0 < epsilon < 1` to exclude hidden wraparound. Check the literal values at
  `t = 0`, `epsilon / 2`, `epsilon`, and at the AddCircle seam. The resulting
  formula gives pointwise support in the initial arc `[0, epsilon]`. -/
  have hformula : ∀ x : AddCircle (1 : ℝ),
      let t := Theorem12.Generic.unitRep x
      tentWindow epsilon x =
        if t ≤ epsilon / 2 then (t : ℂ)
        else if t ≤ epsilon then ((epsilon - t : ℝ) : ℂ) else 0 := by
    intro x
    let a : ℝ := epsilon / 2
    let t : ℝ := Theorem12.Generic.unitRep x
    have haHalf : a < 1 / 2 := by dsimp [a]; linarith
    have ht : t ∈ Set.Ico (0 : ℝ) 1 := Theorem12.Generic.unitRep_mem_Ico x
    let carrier : Set (AddCircle (1 : ℝ)) :=
      {y | Theorem12.Generic.unitRep y ∈ Set.Icc 0 a ∧
        Theorem12.Generic.unitRep (x - y) ∈ Set.Icc 0 a}
    let target : Set (AddCircle (1 : ℝ)) :=
      Theorem12.Generic.unitRep ⁻¹'
        Set.Icc (max 0 (t - a)) (min a t)
    have hcarrier : carrier = target := by
      ext y
      let u : ℝ := Theorem12.Generic.unitRep y
      have hu : u ∈ Set.Ico (0 : ℝ) 1 := Theorem12.Generic.unitRep_mem_Ico y
      have hxy :
          Theorem12.Generic.unitRep (x - y) = Int.fract (t - u) := by
        have hsub : x - y = (((t - u : ℝ) : ℝ) : AddCircle (1 : ℝ)) := by
          rw [show x = ((t : ℝ) : AddCircle (1 : ℝ)) by
            exact (Theorem12.Generic.coe_unitRep x).symm]
          rw [show y = ((u : ℝ) : AddCircle (1 : ℝ)) by
            exact (Theorem12.Generic.coe_unitRep y).symm]
          rfl
        rw [hsub, Theorem12.Generic.unitRep_coe_eq_fract]
      have hfract_of_le (hut : u ≤ t) : Int.fract (t - u) = t - u := by
        exact Int.fract_eq_self.mpr
          ⟨sub_nonneg.mpr hut, lt_of_le_of_lt (sub_le_self t hu.1) ht.2⟩
      have hfract_of_gt (htu : t < u) : Int.fract (t - u) = t - u + 1 := by
        rw [← Int.fract_add_one]
        exact Int.fract_eq_self.mpr ⟨by linarith [hu.2, ht.1], by linarith⟩
      change ((u ∈ Set.Icc 0 a ∧
          Theorem12.Generic.unitRep (x - y) ∈ Set.Icc 0 a) ↔
        u ∈ Set.Icc (max 0 (t - a)) (min a t))
      rw [hxy]
      constructor
      · rintro ⟨⟨hu0, hua⟩, ⟨_, hfractUpper⟩⟩
        by_cases hut : u ≤ t
        · rw [hfract_of_le hut] at hfractUpper
          exact ⟨max_le hu0 (by linarith), le_min hua hut⟩
        · have htu : t < u := lt_of_not_ge hut
          rw [hfract_of_gt htu] at hfractUpper
          have hwrapLower : 1 - a ≤ t - u + 1 := by
            linarith [ht.1, hua]
          exfalso
          linarith [hwrapLower, haHalf]
      · rintro ⟨hlower, hupper⟩
        have hu0 : 0 ≤ u := le_trans (le_max_left 0 (t - a)) hlower
        have hua : u ≤ a := le_trans hupper (min_le_left a t)
        have hut : u ≤ t := le_trans hupper (min_le_right a t)
        have htua : t - u ≤ a := by
          have : t - a ≤ u := le_trans (le_max_right 0 (t - a)) hlower
          linarith
        rw [hfract_of_le hut]
        exact ⟨⟨hu0, hua⟩, ⟨sub_nonneg.mpr hut, htua⟩⟩
    have hintegrand :
        (fun y : AddCircle (1 : ℝ) =>
          boxWindow epsilon y * boxWindow epsilon (x - y)) =
          carrier.indicator (fun _ => (1 : ℂ)) := by
      funext y
      simp only [boxWindow]
      change
        (if Theorem12.Generic.unitRep y ∈ Set.Icc 0 a then 1 else 0) *
            (if Theorem12.Generic.unitRep (x - y) ∈ Set.Icc 0 a then 1 else 0) =
          carrier.indicator (fun _ => (1 : ℂ)) y
      by_cases hy : Theorem12.Generic.unitRep y ∈ Set.Icc 0 a
      · by_cases hxy : Theorem12.Generic.unitRep (x - y) ∈ Set.Icc 0 a
        · have hmem : y ∈ carrier := ⟨hy, hxy⟩
          rw [Set.indicator_of_mem hmem]
          simp [hy, hxy]
        · have hnotMem : y ∉ carrier := by
            intro hmem
            exact hxy hmem.2
          rw [Set.indicator_of_notMem hnotMem]
          simp [hy, hxy]
      · have hnotMem : y ∉ carrier := by
          intro hmem
          exact hy hmem.1
        rw [Set.indicator_of_notMem hnotMem]
        simp [hy]
    have hunitMeas : Measurable Theorem12.Generic.unitRep :=
      (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable.subtype_val
    have htargetMeas : MeasurableSet target := by
      exact measurableSet_Icc.preimage hunitMeas
    have hintegral :
        tentWindow epsilon x =
          ((AddCircle.haarAddCircle.real target : ℝ) : ℂ) := by
      rw [tentWindow, hintegrand, hcarrier]
      simpa using
        (MeasureTheory.integral_indicator_const
          (μ := AddCircle.haarAddCircle) (1 : ℂ) htargetMeas)
    have hsubset :
        Set.Icc (max 0 (t - a)) (min a t) ⊆ Set.Ico (0 : ℝ) 1 := by
      intro z hz
      exact
        ⟨le_trans (le_max_left 0 (t - a)) hz.1,
          lt_of_le_of_lt hz.2 (lt_of_le_of_lt (min_le_right a t) ht.2)⟩
    have hmeasure :
        AddCircle.haarAddCircle target =
          volume (Set.Icc (max 0 (t - a)) (min a t)) := by
      have h := Theorem12.Generic.measure_unitRep_preimage
        (Set.Icc (max 0 (t - a)) (min a t)) measurableSet_Icc
      rw [Set.inter_eq_left.mpr hsubset] at h
      exact h
    have hmeasureReal :
        AddCircle.haarAddCircle.real target =
          max (min a t - max 0 (t - a)) 0 := by
      calc
        AddCircle.haarAddCircle.real target =
            volume.real (Set.Icc (max 0 (t - a)) (min a t)) := by
              exact congrArg ENNReal.toReal hmeasure
        _ = max (min a t - max 0 (t - a)) 0 := Real.volume_real_Icc
    have hlength :
        max (min a t - max 0 (t - a)) 0 =
          if t ≤ epsilon / 2 then t
          else if t ≤ epsilon then epsilon - t else 0 := by
      by_cases hta : t ≤ a
      · rw [if_pos (by simpa [a] using hta)]
        rw [min_eq_right hta, max_eq_left (sub_nonpos.mpr hta)]
        simpa using max_eq_left ht.1
      · rw [if_neg (by simpa [a] using hta)]
        have hat : a ≤ t := le_of_not_ge hta
        have hta0 : 0 ≤ t - a := sub_nonneg.mpr hat
        rw [min_eq_left hat, max_eq_right hta0]
        have hrewrite : a - (t - a) = epsilon - t := by
          dsimp [a]
          ring
        rw [hrewrite]
        by_cases hte : t ≤ epsilon
        · rw [if_pos hte, max_eq_left (sub_nonneg.mpr hte)]
        · rw [if_neg hte, max_eq_right]
          exact sub_nonpos.mpr (le_of_not_ge hte)
    rw [hintegral, hmeasureReal, hlength]
    simp only [t]
    split_ifs <;> rfl
  refine ⟨hformula, ?_⟩
  intro x hx
  have ht := Theorem12.Generic.unitRep_mem_Ico x
  have hnot : ¬ Theorem12.Generic.unitRep x ≤ epsilon := by
    intro hle
    exact hx ⟨ht.1, hle⟩
  have hnotHalf : ¬ Theorem12.Generic.unitRep x ≤ epsilon / 2 := by
    intro hle
    exact hnot (hle.trans (by linarith))
  rw [hformula x]
  simp [hnot, hnotHalf]

/- Proof idea: package the literal tent function.
The continuity field supplies the proof that the triangular window is continuous. -/
private noncomputable def tentWindowContinuous (epsilon : ℝ)
    (he0 : 0 < epsilon) (he1 : epsilon < 1) : C(AddCircle (1 : ℝ), ℂ) :=
  { toFun := tentWindow epsilon
    continuous_toFun := by
      /- Proof idea: Consume `tentWindow_formula_and_support` rather than treating
      `unitRep` as globally continuous. Prove continuity on the three exact
      formula pieces, show the adjacent formulas agree at `epsilon / 2` and
      `epsilon`, and verify the quotient seam `0 = 1`, where both limiting
      values are zero. Package the resulting continuous function with the
      literal coercion `tentWindow epsilon`. -/
      let raw : ℝ → ℂ := fun t =>
        ((max 0 (min t (epsilon - t)) : ℝ) : ℂ)
      have hraw_cont : Continuous raw := by
        apply Complex.continuous_ofReal.comp
        exact continuous_const.max
          (continuous_id.min (continuous_const.sub continuous_id))
      have hraw_zero : raw 0 = raw 1 := by
        have he0' : 0 ≤ epsilon := he0.le
        have he1' : epsilon - 1 ≤ 0 := sub_nonpos.mpr he1.le
        dsimp [raw]
        simp only [sub_zero]
        rw [min_eq_left he0']
        simp only [max_self]
        rw [min_eq_right (by linarith)]
        rw [max_eq_left he1']
      have hlift : Continuous (AddCircle.liftIco (1 : ℝ) 0 raw) :=
        AddCircle.liftIco_zero_continuous hraw_zero hraw_cont.continuousOn
      have hformula := (tentWindow_formula_and_support epsilon he0 he1).1
      have heq : tentWindow epsilon = AddCircle.liftIco (1 : ℝ) 0 raw := by
        funext x
        have hx : Theorem12.Generic.unitRep x ∈ Set.Ico (0 : ℝ) 1 :=
          Theorem12.Generic.unitRep_mem_Ico x
        have hlift_apply :
            AddCircle.liftIco (1 : ℝ) 0 raw x =
              raw (Theorem12.Generic.unitRep x) := by
          calc
            AddCircle.liftIco (1 : ℝ) 0 raw x =
                AddCircle.liftIco (1 : ℝ) 0 raw
                  (((Theorem12.Generic.unitRep x : ℝ) : ℝ) :
                    AddCircle (1 : ℝ)) := by
                      exact congrArg _ (Theorem12.Generic.coe_unitRep x).symm
            _ = raw (Theorem12.Generic.unitRep x) :=
              AddCircle.liftIco_zero_coe_apply hx
        rw [hformula x, hlift_apply]
        dsimp only [raw]
        by_cases hhalf : Theorem12.Generic.unitRep x ≤ epsilon / 2
        · rw [if_pos hhalf]
          rw [min_eq_left (by linarith), max_eq_right hx.1]
        · rw [if_neg hhalf]
          by_cases heps : Theorem12.Generic.unitRep x ≤ epsilon
          · rw [if_pos heps]
            rw [min_eq_right (by linarith)]
            rw [max_eq_right (sub_nonneg.mpr heps)]
          · rw [if_neg heps]
            rw [min_eq_right (by linarith)]
            rw [max_eq_left (sub_nonpos.mpr (le_of_not_ge heps))]
            norm_num
      rw [heq]
      exact hlift }

/- Proof idea: literal Fourier coefficient. -/
def windowCoeff (epsilon : ℝ) (k : ℤ) : ℂ :=
  fourierCoeff (tentWindow epsilon) k

/- Proof idea: continuous translate t ↦ W(t-a). -/
noncomputable def tentWindowTranslate (epsilon : ℝ)
    (he0 : 0 < epsilon) (he1 : epsilon < 1) (a : AddCircle (1 : ℝ)) :
    C(AddCircle (1 : ℝ), ℂ) :=
  { toFun := fun t => tentWindow epsilon (t - a)
    continuous_toFun := (tentWindowContinuous epsilon he0 he1).continuous.comp
      (continuous_id.sub continuous_const) }

/- Proof idea: literal Fejer multiplier. -/
def fejerMultiplier (N : ℕ) (n : ℤ) : ℝ :=
  if |n| ≤ (N : ℤ) then 1 - (|n| : ℝ) / ((N : ℝ) + 1) else 0

/- Proof idea: literal finite mean. -/
noncomputable def fejerMean (N : ℕ) (f : AddCircle (1 : ℝ) → ℂ) :
    C(AddCircle (1 : ℝ), ℂ) :=
  ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
    ((fejerMultiplier N n : ℂ) * fourierCoeff f n) •
      (fourier n : C(AddCircle (1 : ℝ), ℂ))

/- Proof idea: normalized squared character sum. -/
def fejerKernel (N : ℕ) (x : AddCircle (1 : ℝ)) : ℝ :=
  ‖∑ k ∈ Finset.range (N + 1), fourier (k : ℤ) x‖ ^ 2 / ((N : ℝ) + 1)

/- Proof idea: literal convolution f(x-y). -/
noncomputable def fejerConvolution (N : ℕ)
    (f : AddCircle (1 : ℝ) → ℂ) (x : AddCircle (1 : ℝ)) : ℂ :=
  ∫ y, (fejerKernel N y : ℂ) * f (x - y) ∂AddCircle.haarAddCircle

/- Proof idea: retain only the consumed error series. -/
structure FejerApproximation (f : AddCircle (1 : ℝ) → ℂ) where
  index : ℕ → ℕ
  summable_error : Summable (fun j =>
    ∫ x, ‖fejerMean (index j) f x - f x‖ ∂AddCircle.haarAddCircle)

/- Proof idea: canonical Banach-space tsum. -/
noncomputable def fourierSynthesis (c : ℤ → ℂ) : C(AddCircle (1 : ℝ), ℂ) :=
  ∑' k : ℤ, c k • (fourier k : C(AddCircle (1 : ℝ), ℂ))

/- Proof idea: literal weighted negative orbit coefficient. -/
def weightedOrbitCoeff (epsilon alpha : ℝ)
    (f : AddCircle (1 : ℝ) → ℂ) (x : AddCircle (1 : ℝ)) (k : ℤ) : ℂ :=
  windowCoeff epsilon k *
    f (x - ((((k : ℤ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ)))

/- Proof idea: unrestricted ENNReal norm sum. -/
def weightedOrbitENNRealMass (epsilon alpha : ℝ)
    (f : AddCircle (1 : ℝ) → ℂ) (x : AddCircle (1 : ℝ)) : ENNReal :=
  ∑' k : ℤ, (‖weightedOrbitCoeff epsilon alpha f x k‖₊ : ENNReal)

/- Proof idea: exact summability package. -/
structure WeightedApproximationAt (epsilon alpha : ℝ)
    (f : AddCircle (1 : ℝ) → ℂ) (A : FejerApproximation f)
    (x : AddCircle (1 : ℝ)) : Prop where
  targetSummable : Summable (fun k : ℤ => ‖weightedOrbitCoeff epsilon alpha f x k‖)
  stageSummable : ∀ j, Summable (fun k : ℤ =>
    ‖weightedOrbitCoeff epsilon alpha (fejerMean (A.index j) f) x k‖)
  errorSummable : ∀ j, Summable (fun k : ℤ =>
    ‖weightedOrbitCoeff epsilon alpha
      (fun y => fejerMean (A.index j) f y - f y) x k‖)
  summable_errorNorm : Summable (fun j => ∑' k : ℤ,
    ‖weightedOrbitCoeff epsilon alpha
      (fun y => fejerMean (A.index j) f y - f y) x k‖)

/- Proof idea: transparent composition. -/
noncomputable def broadenedFunction (epsilon alpha : ℝ)
    (f : AddCircle (1 : ℝ) → ℂ) (x : AddCircle (1 : ℝ)) :
    C(AddCircle (1 : ℝ), ℂ) :=
  fourierSynthesis (weightedOrbitCoeff epsilon alpha f x)

/- Proof idea: canonical invariant package. -/
structure BroadeningData (epsilon alpha v : ℝ)
    (f : AddCircle (1 : ℝ) → ℂ) (x : AddCircle (1 : ℝ)) : Prop where
  coeffSummable : Summable (fun k : ℤ => ‖weightedOrbitCoeff epsilon alpha f x k‖)
  coeff_eq : ∀ k : ℤ,
    fourierCoeff (broadenedFunction epsilon alpha f x) k =
      weightedOrbitCoeff epsilon alpha f x k
  supported : SupportedInInitialArc (broadenedFunction epsilon alpha f x)
    (1 - v + epsilon)

/- Proof idea: literal negative-sign integral. -/
noncomputable def fourierLaplace
    (g : AddCircle (1 : ℝ) → ℂ) (z : ℂ) : ℂ :=
  ∫ x, g x * Complex.exp
    (-2 * Real.pi * Complex.I * z * (Theorem12.Generic.unitRep x : ℂ))
      ∂AddCircle.haarAddCircle

/- Proof idea: literal derivative integrand. -/
def fourierLaplaceDerivIntegrand
    (g : AddCircle (1 : ℝ) → ℂ) (z : ℂ) (x : AddCircle (1 : ℝ)) : ℂ :=
  g x * (-2 * Real.pi * Complex.I * (Theorem12.Generic.unitRep x : ℂ)) *
    Complex.exp
      (-2 * Real.pi * Complex.I * z * (Theorem12.Generic.unitRep x : ℂ))

/- Proof idea: transparent real integer translation. -/
def shiftedFourierLaplace
    (g : AddCircle (1 : ℝ) → ℂ) (m : ℤ) (z : ℂ) : ℂ :=
  fourierLaplace g (z + (m : ℂ))

/- Proof idea: retain one witness. -/
structure EntireCountingData (F : ℂ → ℂ) where
  data : Theorem12.Generic.MeromorphicCountingData F
  order_nonneg : ∀ z, 0 ≤ data.order z
  poleCount_eq_zero : ∀ R, Theorem12.Generic.poleCount data R = 0

/- Proof idea: one radius in each open annulus. -/
structure CleanRadii (F : ℂ → ℂ) where
  radius : ℕ → ℝ
  lower : ∀ j : ℕ, (j : ℝ) + 1 < radius j
  upper : ∀ j : ℕ, radius j < (j : ℝ) + 2
  clean : ∀ (j : ℕ) (z : ℂ), ‖z‖ = radius j → AnalyticAt ℂ F z ∧ F z ≠ 0

/- Proof idea: literal inclusive 2N+1 normalization. -/
def HasEventuallySymmetricFourierZeroDensity
    (g : AddCircle (1 : ℝ) → ℂ) (sigma : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop,
    sigma * (2 * (N : ℝ) + 1) ≤ (symmetricFourierZeroCount g N : ℝ)

/- Proof idea: literal preimage carrier. -/
def circleCarrier (S : Set ℝ) : Set (AddCircle (1 : ℝ)) :=
  Theorem12.Generic.unitRep ⁻¹' normalizedCarrier S

/- Proof idea: literal half of strict measure gap. -/
def broadeningWidth (v : ℝ) (S : Set ℝ) : ℝ :=
  (v - (volume S).toReal) / 2

end Internal

/- Proof idea: proposition structure with no hidden assumptions. -/
structure Theorem14Conclusion (alpha v : ℝ) : Prop where
  uniformDensity :
    Theorem12.HasUniformDensity (integerFrequencySet alpha v) v
  universalL1 :
    UniversalL1UniquenessBelow (integerFrequencySet alpha v) v
  completeLp :
    ∀ (S : Set ℝ) (hSmeas : MeasurableSet S)
      (hSunit : S ⊆ Set.Icc (0 : ℝ) 1)
      (hSlt : volume S < ENNReal.ofReal v)
      (p : ENNReal) (hp : 1 ≤ p) (hpTop : p ≠ ∞),
      Theorem12.ExponentialCompleteInLp
        (integerFrequencySet alpha v) S hSmeas p hp
        (ne_of_lt (hSlt.trans_le le_top))

end Theorem14
