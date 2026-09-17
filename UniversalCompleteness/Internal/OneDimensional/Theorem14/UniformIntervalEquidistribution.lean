import Theorem14.RotationAverages

/-! # Theorem 1.4: uniform interval equidistribution -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal Topology BigOperators

namespace Theorem14.Internal

private lemma measure_circleInterval
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    AddCircle.haarAddCircle (circleInterval a b) = ENNReal.ofReal (b - a) := by
  have _hba : 0 ≤ b - a := sub_nonneg.mpr hab
  rw [circleInterval, Theorem12.Generic.measure_unitRep_preimage
    (Set.Ico a b) measurableSet_Ico]
  rw [inter_eq_left.mpr]
  · exact Real.volume_Ico
  · intro x hx
    exact ⟨ha.trans hx.1, hx.2.trans_le hb⟩

private lemma frontier_circleInterval_subset_endpoints
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    frontier (circleInterval a b) ⊆
      ({(a : AddCircle (1 : ℝ)), (b : AddCircle (1 : ℝ))} :
        Set (AddCircle (1 : ℝ))) := by
  have _hba : 0 ≤ b - a := sub_nonneg.mpr hab
  let q : ℝ → AddCircle (1 : ℝ) := fun t => (t : AddCircle (1 : ℝ))
  have hEclosed : IsClosed (q '' Set.Icc a b) := by
    exact (isCompact_Icc.image (AddCircle.continuous_mk' (1 : ℝ))).isClosed
  have hEsub : circleInterval a b ⊆ q '' Set.Icc a b := by
    intro x hx
    refine ⟨Theorem12.Generic.unitRep x, ?_, ?_⟩
    · exact ⟨hx.1, hx.2.le⟩
    · exact Theorem12.Generic.coe_unitRep x
  have hopen : IsOpen (q '' Set.Ioo a b) := by
    exact QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  have hopenSub : q '' Set.Ioo a b ⊆ circleInterval a b := by
    rintro x ⟨y, hy, rfl⟩
    change Theorem12.Generic.unitRep (y : AddCircle (1 : ℝ)) ∈ Set.Ico a b
    have hy01 : y ∈ Set.Ico (0 : ℝ) 1 :=
      ⟨(ha.trans_lt hy.1).le, hy.2.trans_le hb⟩
    rw [Theorem12.Generic.unitRep_coe_eq_fract, Int.fract_eq_self.2 hy01]
    exact ⟨hy.1.le, hy.2⟩
  intro x hx
  have hxclosed : x ∈ q '' Set.Icc a b :=
    closure_minimal hEsub hEclosed hx.1
  obtain ⟨y, hy, rfl⟩ := hxclosed
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  by_contra hend
  push Not at hend
  have hya : y ≠ a := fun h => hend.1 (congrArg q h)
  have hyb : y ≠ b := fun h => hend.2 (congrArg q h)
  have hyopen : y ∈ Set.Ioo a b :=
    ⟨hy.1.lt_of_ne (Ne.symm hya), hy.2.lt_of_ne hyb⟩
  have himage : (y : AddCircle (1 : ℝ)) ∈ q '' Set.Ioo a b :=
    ⟨y, hyopen, rfl⟩
  exact hx.2 (interior_maximal hopenSub hopen himage)

private lemma haar_singleton_null (x : AddCircle (1 : ℝ)) :
    AddCircle.haarAddCircle ({x} : Set (AddCircle (1 : ℝ))) = 0 := by
  have hset : ({x} : Set (AddCircle (1 : ℝ))) =
      Theorem12.Generic.unitRep ⁻¹'
        ({Theorem12.Generic.unitRep x} : Set ℝ) := by
    ext y
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    constructor
    · rintro rfl
      rfl
    · intro h
      rw [← Theorem12.Generic.coe_unitRep y,
        ← Theorem12.Generic.coe_unitRep x, h]
  rw [hset, Theorem12.Generic.measure_unitRep_preimage
    ({Theorem12.Generic.unitRep x} : Set ℝ)
      (measurableSet_singleton (Theorem12.Generic.unitRep x))]
  exact measure_mono_null inter_subset_left (by simp)

private lemma uniform_rotationAverage_continuous_real
    (alpha : ℝ) (hAlpha : Irrational alpha)
    (f : C(AddCircle (1 : ℝ), ℝ)) :
    ∀ epsilon > 0, ∃ N0 : ℕ, ∀ N ≥ N0, 0 < N →
      ∀ x : AddCircle (1 : ℝ),
        |(N : ℝ)⁻¹ * ∑ k ∈ Finset.range N,
            f (x + ((((k : ℕ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ))) -
          ∫ y, f y ∂AddCircle.haarAddCircle| < epsilon := by
  let fC : C(AddCircle (1 : ℝ), ℂ) :=
    ⟨fun x => (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
  intro epsilon hepsilon
  obtain ⟨N0, hN0⟩ :=
    uniform_rotationAverage_continuous alpha hAlpha fC epsilon hepsilon
  refine ⟨N0, ?_⟩
  intro N hNN0 hN x
  have hx := hN0 N hNN0 hN x
  have hcast : rotationAverage alpha fC N x -
        ∫ y, fC y ∂AddCircle.haarAddCircle =
      (((N : ℝ)⁻¹ * ∑ k ∈ Finset.range N,
            f (x + ((((k : ℕ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ))) -
          ∫ y, f y ∂AddCircle.haarAddCircle : ℝ) : ℂ) := by
    rw [rotationAverage]
    change (N : ℂ)⁻¹ * ∑ k ∈ Finset.range N,
        (f (x + ((((k : ℕ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ))) : ℂ) -
          ∫ y, (f y : ℂ) ∂AddCircle.haarAddCircle = _
    rw [integral_complex_ofReal]
    push_cast
    rfl
  rw [hcast, Complex.norm_real, Real.norm_eq_abs] at hx
  exact hx

private lemma intervalVisitCount_cast_eq_indicator_sum
    (alpha a b : ℝ) (N : ℕ) (x : AddCircle (1 : ℝ)) :
    (intervalVisitCount alpha a b N x : ℝ) =
      ∑ k ∈ Finset.range N,
        (circleInterval a b).indicator (fun _ => (1 : ℝ))
          (x + ((((k : ℕ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ))) := by
  classical
  simp [intervalVisitCount, Set.indicator, Finset.sum_boole]

/- Proof idea: include the two coerced endpoints, explicitly treating b=1 as circle zero. -/
private lemma intervalBoundary_null
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    AddCircle.haarAddCircle (frontier (circleInterval a b)) = 0 := by
  /- Proof idea: Split first on `a=b` and `(a,b)=(0,1)`, where the interval is respectively empty and all of
  `AddCircle 1`. In every remaining case prove the quotient-safe inclusion `frontier
  (circleInterval a b) ⊆ ({((a:Real):AddCircle 1), ((b:Real):AddCircle 1)} : Set (AddCircle 1))`
  by showing membership is locally constant away from the two coerced endpoints. At `b=1`, the
  second endpoint is circle zero even though `unitRep ⁻¹' {1}` is empty. Finish by measure
  monotonicity and nullity of a union of two singletons. -/
  apply measure_mono_null (frontier_circleInterval_subset_endpoints ha hab hb)
  exact measure_union_null (haar_singleton_null _) (haar_singleton_null _)

/- Proof idea: handle empty/full cases, otherwise choose compact/open approximants. -/
private theorem exists_intervalIndicatorSandwich
    {a b eta : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (heta : 0 < eta) :
    Nonempty (IntervalIndicatorSandwich a b eta) := by
  /- Proof idea: Treat empty/full intervals directly. Otherwise choose a compact core in the interior and an
  open enlargement of the closure whose lost/added measures are each below `eta`; apply Urysohn
  to the relevant disjoint closed sets and integrate the pointwise bounds. This is the sole
  route. -/
  let E : Set (AddCircle (1 : ℝ)) := circleInterval a b
  let δ : ℕ → ℝ := fun n => (1 : ℝ) / (n + 1)
  have hδpos : ∀ n, 0 < δ n := fun n => by
    dsimp [δ]
    positivity
  have hδlim : Filter.Tendsto δ Filter.atTop (nhds 0) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hnull : AddCircle.haarAddCircle (frontier E) = 0 := by
    exact intervalBoundary_null ha hab hb
  have hmeasure : AddCircle.haarAddCircle E = ENNReal.ofReal (b - a) := by
    exact measure_circleInterval ha hab hb
  have hrealClosure : AddCircle.haarAddCircle.real (closure E) = b - a := by
    rw [Measure.real_def, measure_closure_of_null_frontier hnull, hmeasure,
      ENNReal.toReal_ofReal]
    linarith
  have hrealInterior : AddCircle.haarAddCircle.real (interior E) = b - a := by
    rw [Measure.real_def, measure_interior_of_null_frontier hnull, hmeasure,
      ENNReal.toReal_ofReal]
    linarith
  have hrealCompl : AddCircle.haarAddCircle.real (interior E)ᶜ = 1 - (b - a) := by
    rw [measureReal_compl isOpen_interior.measurableSet, probReal_univ,
      hrealInterior]
  have htUpper := tendsto_integral_thickenedIndicator_of_isClosed
    (F := closure E) (δs := δ)
    (AddCircle.haarAddCircle : Measure (AddCircle (1 : ℝ)))
    isClosed_closure hδpos hδlim
  obtain ⟨nU, hnU⟩ := Metric.tendsto_atTop.1 htUpper eta heta
  have htCompl := tendsto_integral_thickenedIndicator_of_isClosed
    (F := (interior E)ᶜ) (δs := δ)
    (AddCircle.haarAddCircle : Measure (AddCircle (1 : ℝ)))
    (isClosed_compl_iff.mpr isOpen_interior) hδpos hδlim
  obtain ⟨nL, hnL⟩ := Metric.tendsto_atTop.1 htCompl eta heta
  let uNN := thickenedIndicator (hδpos nU) (closure E)
  let cNN := thickenedIndicator (hδpos nL) (interior E)ᶜ
  let upper : C(AddCircle (1 : ℝ), ℝ) :=
    ⟨fun x => (uNN x : ℝ), NNReal.continuous_coe.comp uNN.continuous⟩
  let lower : C(AddCircle (1 : ℝ), ℝ) :=
    1 - ⟨fun x => (cNN x : ℝ), NNReal.continuous_coe.comp cNN.continuous⟩
  refine ⟨⟨lower, upper, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro x
    dsimp [lower, cNN]
    exact sub_nonneg.mpr (by
      exact_mod_cast thickenedIndicator_le_one (hδpos nL) (interior E)ᶜ x)
  · intro x
    by_cases hx : x ∈ E
    · rw [show circleInterval a b = E from rfl]
      simp only [indicator_of_mem hx]
      dsimp [lower, cNN]
      have hc0 : (0 : ℝ) ≤
          (thickenedIndicator (hδpos nL) (interior E)ᶜ x : ℝ) := by
        positivity
      linarith
    · have hxint : x ∉ interior E := fun h => hx (interior_subset h)
      have hxc : x ∈ (interior E)ᶜ := hxint
      have hcOne : cNN x = 1 := le_antisymm
        (thickenedIndicator_le_one (hδpos nL) (interior E)ᶜ x)
        (one_le_thickenedIndicator_apply _ (hδpos nL) hxc)
      rw [show circleInterval a b = E from rfl]
      simp only [indicator_of_notMem hx]
      simp [lower, hcOne]
  · intro x
    by_cases hx : x ∈ E
    · have hxu : x ∈ closure E := subset_closure hx
      have huOne : uNN x = 1 := le_antisymm
        (thickenedIndicator_le_one (hδpos nU) (closure E) x)
        (one_le_thickenedIndicator_apply _ (hδpos nU) hxu)
      rw [show circleInterval a b = E from rfl]
      simp only [indicator_of_mem hx]
      simp [upper, huOne]
    · rw [show circleInterval a b = E from rfl]
      simp only [indicator_of_notMem hx]
      simp [upper]
  · intro x
    dsimp [upper, uNN]
    exact_mod_cast thickenedIndicator_le_one (hδpos nU) (closure E) x
  · have hcloseL := hnL nL le_rfl
    rw [hrealCompl, Real.dist_eq] at hcloseL
    have hcInt : Integrable (fun x => (cNN x : ℝ)) AddCircle.haarAddCircle := by
      exact integrable_thickenedIndicator (interior E)ᶜ (hδpos nL)
    have hlowerInt : (∫ x, lower x ∂AddCircle.haarAddCircle) =
        1 - ∫ x, (cNN x : ℝ) ∂AddCircle.haarAddCircle := by
      change (∫ x, 1 - (cNN x : ℝ) ∂AddCircle.haarAddCircle) = _
      rw [integral_sub (integrable_const _) hcInt]
      simp
    rw [hlowerInt]
    change b - a - eta ≤ 1 - ∫ x,
      ((thickenedIndicator (hδpos nL) (interior E)ᶜ) x : ℝ)
        ∂AddCircle.haarAddCircle
    rw [abs_lt] at hcloseL
    linarith
  · have hcloseU := hnU nU le_rfl
    rw [hrealClosure, Real.dist_eq, abs_lt] at hcloseU
    change (∫ x,
      ((thickenedIndicator (hδpos nU) (closure E)) x : ℝ)
        ∂AddCircle.haarAddCircle) ≤ b - a + eta
    linarith

/- Proof idea: apply the quantitative sandwich and squeeze the literal Ico count. -/
theorem uniform_intervalVisitCount
    (alpha : ℝ) (hAlpha : Irrational alpha)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    ∀ epsilon > 0, ∃ N0 : ℕ, ∀ N ≥ N0, 0 < N →
      ∀ x : AddCircle (1 : ℝ),
        |(intervalVisitCount alpha a b N x : ℝ) / (N : ℝ) - (b - a)| < epsilon := by
  /- Proof idea: Choose the sandwich at error `epsilon/4`; apply uniform continuous rotation convergence to the
  complex casts of lower/upper; identify the indicator sum with `intervalVisitCount` and squeeze. -/
  intro epsilon hepsilon
  have hepsilon4 : 0 < epsilon / 4 := by linarith
  obtain ⟨s⟩ := exists_intervalIndicatorSandwich ha hab hb hepsilon4
  obtain ⟨NL, hNL⟩ :=
    uniform_rotationAverage_continuous_real alpha hAlpha s.lower
      (epsilon / 4) hepsilon4
  obtain ⟨NU, hNU⟩ :=
    uniform_rotationAverage_continuous_real alpha hAlpha s.upper
      (epsilon / 4) hepsilon4
  refine ⟨max NL NU, ?_⟩
  intro N hNmax hN x
  have hNNL : NL ≤ N := (le_max_left NL NU).trans hNmax
  have hNNU : NU ≤ N := (le_max_right NL NU).trans hNmax
  have hL := hNL N hNNL hN x
  have hU := hNU N hNNU hN x
  rw [abs_lt] at hL hU
  have hsumL :
      (∑ k ∈ Finset.range N,
          s.lower (x + ((((k : ℕ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ)))) ≤
        ∑ k ∈ Finset.range N,
          (circleInterval a b).indicator (fun _ => (1 : ℝ))
            (x + ((((k : ℕ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ))) := by
    exact Finset.sum_le_sum fun k hk => s.lower_le _
  have hsumU :
      (∑ k ∈ Finset.range N,
          (circleInterval a b).indicator (fun _ => (1 : ℝ))
            (x + ((((k : ℕ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ))) ≤
        ∑ k ∈ Finset.range N,
          s.upper (x + ((((k : ℕ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ)))) := by
    exact Finset.sum_le_sum fun k hk => s.le_upper _
  have hNinv : 0 ≤ (N : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg N)
  have hcount := intervalVisitCount_cast_eq_indicator_sum alpha a b N x
  have havgL :
      (N : ℝ)⁻¹ * ∑ k ∈ Finset.range N,
          s.lower (x + ((((k : ℕ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ))) ≤
        (intervalVisitCount alpha a b N x : ℝ) / (N : ℝ) := by
    calc
      _ ≤ (N : ℝ)⁻¹ * ∑ k ∈ Finset.range N,
          (circleInterval a b).indicator (fun _ => (1 : ℝ))
            (x + ((((k : ℕ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ))) :=
        mul_le_mul_of_nonneg_left hsumL hNinv
      _ = (N : ℝ)⁻¹ * (intervalVisitCount alpha a b N x : ℝ) := by
        rw [hcount]
      _ = _ := by rw [div_eq_mul_inv, mul_comm]
  have havgU :
      (intervalVisitCount alpha a b N x : ℝ) / (N : ℝ) ≤
        (N : ℝ)⁻¹ * ∑ k ∈ Finset.range N,
          s.upper (x + ((((k : ℕ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ))) := by
    calc
      _ = (N : ℝ)⁻¹ * (intervalVisitCount alpha a b N x : ℝ) := by
        rw [div_eq_mul_inv, mul_comm]
      _ = (N : ℝ)⁻¹ * ∑ k ∈ Finset.range N,
          (circleInterval a b).indicator (fun _ => (1 : ℝ))
            (x + ((((k : ℕ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ))) := by
        rw [hcount]
      _ ≤ _ := mul_le_mul_of_nonneg_left hsumU hNinv
  rw [abs_lt]
  constructor <;> linarith [s.integral_lower, s.integral_upper]

end Theorem14.Internal
