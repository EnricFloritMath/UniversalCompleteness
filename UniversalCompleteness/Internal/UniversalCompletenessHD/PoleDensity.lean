import UniversalCompletenessHD.FourierZeros

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace UniversalCompletenessHD.Internal

/- Proof idea: prove measurability termwise for translated measurable support indicators,
then use measurability of a countable ENNReal `tsum`. -/
theorem aemeasurable_multiplicityENNHD {d : Nat} {alpha beta : RealVec d}
    {S : Set (RealVec d)} {f : RealVec d → Complex}
    (data : PositiveInputDataHD alpha beta S f) :
    AEMeasurable (multiplicityENNHD data) volume := by
  unfold multiplicityENNHD
  apply AEMeasurable.tsum
  intro j
  apply Measurable.aemeasurable
  exact measurable_const.indicator
    ((measurableSet_cubeSliceSupport data j).preimage
      (measurable_id.sub measurable_const))

/- Proof idea: apply Tonelli to the nonnegative layer sum, translate every support
indicator by Haar invariance, and identify the resulting layer-measure sum. -/
theorem lintegral_multiplicityENNHD {d : Nat} {alpha beta : RealVec d}
    {S : Set (RealVec d)} {f : RealVec d → Complex}
    (data : PositiveInputDataHD alpha beta S f) :
    (∫⁻ y : Torus d, multiplicityENNHD data y ∂volume) = supportMassENNHD data := by
  classical
  let mu : Measure (Torus d) := volume
  letI : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
  let nu : Measure (Torus d) := volume
  have hmunu : mu = nu := by
    dsimp [mu, nu]
    change Measure.pi
        (fun _ : Fin d ↦ @volume UnitAddCircle (AddCircle.measureSpace 1)) =
      Measure.pi (fun _ : Fin d ↦ AddCircle.haarAddCircle)
    congr 1
    funext i
    change ENNReal.ofReal 1 • Measure.addHaarMeasure ⊤ =
      Measure.addHaarMeasure ⊤
    simp
  change (∫⁻ y : Torus d, (∑' j : IntVec d,
      (cubeSliceSupport data j).indicator (fun _ ↦ (1 : ENNReal))
        (y - floorBetaDot beta j • alphaTorusHD alpha)) ∂mu) =
    ∑' j : IntVec d, nu (cubeSliceSupport data j)
  rw [hmunu]
  rw [lintegral_tsum]
  · congr 1
    funext j
    let a : Torus d := floorBetaDot beta j • alphaTorusHD alpha
    let g : Torus d → ENNReal :=
      (cubeSliceSupport data j).indicator (fun _ ↦ (1 : ENNReal))
    calc
      (∫⁻ y : Torus d,
          (cubeSliceSupport data j).indicator (fun _ ↦ (1 : ENNReal))
            (y - floorBetaDot beta j • alphaTorusHD alpha) ∂nu) =
          ∫⁻ y : Torus d, g (y - a) ∂nu := by rfl
      _ = ∫⁻ y : Torus d, g y ∂nu := by
        simpa [nu] using
          (measurePreserving_torus_sub (d := d) a).lintegral_comp
            (measurable_const.indicator (measurableSet_cubeSliceSupport data j))
      _ = nu (cubeSliceSupport data j) := by
        simpa [g, Set.indicator] using
          (lintegral_indicator_one (μ := nu)
            (measurableSet_cubeSliceSupport data j))
  · intro j
    exact (measurable_const.indicator
      ((measurableSet_cubeSliceSupport data j).preimage
        (measurable_id.sub measurable_const))).aemeasurable

/- Proof idea: finite support mass and `lintegral_multiplicityENNHD` imply that the nonnegative
multiplicity function is finite almost everywhere. -/
theorem multiplicityENNHD_lt_top_ae {d : Nat} {alpha beta : RealVec d}
    {S : Set (RealVec d)} {f : RealVec d → Complex}
    (data : PositiveInputDataHD alpha beta S f) (hSlt : volume S < 1) :
    ∀ᵐ y : Torus d ∂volume, multiplicityENNHD data y < ∞ := by
  apply ae_lt_top' (aemeasurable_multiplicityENNHD data)
  rw [lintegral_multiplicityENNHD]
  exact (supportMassENNHD_lt_one data (by simpa using hSlt)).2

/- Proof idea: convert the finite-a.e. ENNReal function to Real and use the exact
lintegral identity; retain both integrability and integral equality. -/
theorem integrable_multiplicityHD {d : Nat} {alpha beta : RealVec d}
    {S : Set (RealVec d)} {f : RealVec d → Complex}
    (data : PositiveInputDataHD alpha beta S f) (hSlt : volume S < 1) :
    Integrable (multiplicityHD data) volume ∧
      (∫ y : Torus d, multiplicityHD data y ∂volume) = supportMassHD data := by
  have hfinite : (∫⁻ y : Torus d, multiplicityENNHD data y ∂volume) ≠ ∞ := by
    rw [lintegral_multiplicityENNHD]
    exact (supportMassENNHD_lt_one data (by simpa using hSlt)).2
  constructor
  · exact integrable_toReal_of_lintegral_ne_top
      (aemeasurable_multiplicityENNHD data) hfinite
  · rw [show multiplicityHD data = fun y => (multiplicityENNHD data y).toReal from rfl,
      integral_toReal (aemeasurable_multiplicityENNHD data)
        (multiplicityENNHD_lt_top_ae data hSlt),
      lintegral_multiplicityENNHD]
    rfl

/- Proof idea: specialize the proved higher-dimensional two-sided Birkhoff theorem to
`multiplicityHD`, preserving the source orbit sign and denominator `2*N+1`. -/
theorem multiplicity_twoSided_average_aeHD (P : Params)
    {S : Set (RealVec P.d)} {f : RealVec P.d → Complex}
    (data : PositiveInputDataHD P.alpha P.beta S f) (hSlt : volume S < 1) :
    ∀ᵐ x : Torus P.d ∂volume,
      Tendsto
        (fun N : Nat =>
          (2 * (N : Real) + 1)⁻¹ *
            ∑ q ∈ Finset.Icc (-(N : Int)) (N : Int),
              multiplicityHD data (x - q • alphaTorusHD P.alpha))
        atTop (nhds (supportMassHD data)) := by
  let mu : Measure (Torus P.d) := volume
  letI : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
  let nu : Measure (Torus P.d) := volume
  have hmunu : mu = nu := by
    dsimp [mu, nu]
    change Measure.pi
        (fun _ : Fin P.d ↦ @volume UnitAddCircle (AddCircle.measureSpace 1)) =
      Measure.pi (fun _ : Fin P.d ↦ AddCircle.haarAddCircle)
    congr 1
    funext i
    change ENNReal.ofReal 1 • Measure.addHaarMeasure ⊤ =
      Measure.addHaarMeasure ⊤
    simp
  have hint : Integrable (multiplicityHD data) nu := by
    rw [← hmunu]
    exact (integrable_multiplicityHD data hSlt).1
  have hmean : (∫ y : Torus P.d, multiplicityHD data y ∂nu) =
      supportMassHD data := by
    rw [← hmunu]
    exact (integrable_multiplicityHD data hSlt).2
  have h := twoSided_average_torusTranslation P.alpha_independent
    (multiplicityHD data) hint
  change ∀ᵐ x : Torus P.d ∂nu,
    Tendsto
      (fun N : Nat => (2 * (N : Real) + 1)⁻¹ *
        ∑ q ∈ Finset.Icc (-(N : Int)) (N : Int),
          multiplicityHD data (x - q • alphaTorusHD P.alpha))
      atTop (nhds (∫ y : Torus P.d, multiplicityHD data y ∂nu)) at h
  change ∀ᵐ x : Torus P.d ∂mu,
    Tendsto
      (fun N : Nat => (2 * (N : Real) + 1)⁻¹ *
        ∑ q ∈ Finset.Icc (-(N : Int)) (N : Int),
          multiplicityHD data (x - q • alphaTorusHD P.alpha))
      atTop (nhds (supportMassHD data))
  rw [hmunu]
  simpa [hmean] using h

/- Proof idea: biject active layers in the fixed q-fibre with the nonzero translated
slice indicators, proving fibre finiteness before taking `Set.ncard`. -/
theorem activeFiberCount_eq_multiplicityHD (P : Params)
    {S : Set (RealVec P.d)} {f : RealVec P.d → Complex}
    (data : PositiveInputDataHD P.alpha P.beta S f) (x : Torus P.d) (q : Int)
    (hxBad : x ∉ sineBadHD P.alpha P.beta)
    (hfinite : multiplicityENNHD data (x - q • alphaTorusHD P.alpha) < ∞) :
    Set.Finite {a : ActiveIndexHD data x | a.1.2 = q} ∧
      (({a : ActiveIndexHD data x | a.1.2 = q}.ncard : Nat) : Real) =
        multiplicityHD data (x - q • alphaTorusHD P.alpha) := by
  classical
  let Q : IntVec P.d → Prop := fun j =>
    uCoordHD P.alpha P.beta x j q ∈ cubeSliceSupport data j
  have hcoord : ∀ j : IntVec P.d,
      x - q • alphaTorusHD P.alpha -
          floorBetaDot P.beta j • alphaTorusHD P.alpha =
        uCoordHD P.alpha P.beta x j q := by
    intro j
    rw [uCoordHD_translate]
    unfold ellIndexHD
    rw [add_smul]
    abel
  have hmult : multiplicityENNHD data
      (x - q • alphaTorusHD P.alpha) =
      ∑' j : IntVec P.d, if Q j then 1 else 0 := by
    unfold multiplicityENNHD
    congr 1
    funext j
    rw [hcoord]
    by_cases hj : Q j <;> simp [Q, hj]
  have hsum_ne : (∑' j : IntVec P.d,
      if Q j then (1 : ENNReal) else 0) ≠ ∞ := by
    rw [← hmult]
    exact hfinite.ne
  have hQ : Set.Finite {j : IntVec P.d | Q j} := by
    have hlev := ENNReal.finite_const_le_of_tsum_ne_top hsum_ne
      (ε := (1 : ENNReal)) one_ne_zero
    convert hlev using 1
    ext j
    by_cases hj : Q j <;> simp [hj]
  let sec : Set (ActiveIndexHD data x) := {a | a.1.2 = q}
  let fstIndex : ActiveIndexHD data x → IntVec P.d := fun a => a.1.1
  have hmaps : Set.MapsTo fstIndex sec {j : IntVec P.d | Q j} := by
    intro a ha
    have hres := a.2
    have hq : a.1.2 = q := ha
    rw [hq] at hres
    exact (residueCoordHD_ne_zero_iff data x hxBad a.1.1 q).mp hres
  have hinj : Set.InjOn fstIndex sec := by
    intro a ha b hb hab
    apply Subtype.ext
    apply Prod.ext
    · exact hab
    · exact ha.trans hb.symm
  have hactive : Set.Finite {a : ActiveIndexHD data x | a.1.2 = q} := by
    exact Set.Finite.of_injOn hmaps hinj hQ
  refine ⟨hactive, ?_⟩
  have hcardENN : (({a : ActiveIndexHD data x | a.1.2 = q}.ncard : Nat) : ENNReal) =
      multiplicityENNHD data (x - q • alphaTorusHD P.alpha) := by
    rw [hmult, Theorem12.Generic.ennreal_tsum_indicator_eq_ncard Q hQ]
    norm_cast
    apply Set.ncard_congr (fun a _ => fstIndex a)
    · exact hmaps
    · intro a b ha hb hab
      exact hinj ha hb hab
    · intro j hj
      let a : ActiveIndexHD data x :=
        ⟨(j, q), (residueCoordHD_ne_zero_iff data x hxBad j q).mpr hj⟩
      exact ⟨a, rfl, rfl⟩
  unfold multiplicityHD
  rw [← hcardENN]
  simp

/- Proof idea: use `|pole-q| ≤ C_beta` in both directions and decompose the actual
active-pole set into finite, disjoint q-fibres by pole-coordinate injectivity. -/
theorem realPoleCountHD_sandwich (P : Params)
    {S : Set (RealVec P.d)} {f : RealVec P.d → Complex}
    (data : PositiveInputDataHD P.alpha P.beta S f) (x : Torus P.d)
    (point : PoleAveragePointDataHD data x) (R : Real)
    (hR : poleShiftConstantHD P.beta < R) :
    (∑ q ∈
        Finset.Icc (-(Int.floor (R - poleShiftConstantHD P.beta)))
          (Int.floor (R - poleShiftConstantHD P.beta)),
        multiplicityHD data (x - q • alphaTorusHD P.alpha)) ≤
      (realPoleCountHD data x R : Real) ∧
    (realPoleCountHD data x R : Real) ≤
      ∑ q ∈
        Finset.Icc (-(Int.floor (R + poleShiftConstantHD P.beta)))
          (Int.floor (R + poleShiftConstantHD P.beta)),
        multiplicityHD data (x - q • alphaTorusHD P.alpha) := by
  classical
  let window : Real → Finset Int := fun T =>
    Finset.Icc (-(Int.floor T)) (Int.floor T)
  let fiber : Int → Set (ActiveIndexHD data x) := fun q => {a | a.1.2 = q}
  have hfiber (q : Int) : (fiber q).Finite :=
    (activeFiberCount_eq_multiplicityHD P data x q
      point.fourierGood.analytic.offBad (point.orbitFinite q)).1
  have hmult (q : Int) :
      multiplicityHD data (x - q • alphaTorusHD P.alpha) =
        ((fiber q).ncard : Real) := by
    exact (activeFiberCount_eq_multiplicityHD P data x q
      point.fourierGood.analytic.offBad (point.orbitFinite q)).2.symm
  have hdisj : (Set.univ : Set Int).PairwiseDisjoint fiber := by
    intro q _ r _ hqr
    change Disjoint (fiber q) (fiber r)
    rw [Set.disjoint_left]
    intro a haq har
    exact hqr (haq.symm.trans har)
  let activeWindow (T : Real) : Set (ActiveIndexHD data x) :=
    {a | a.1.2 ∈ window T}
  have hactiveWindow (T : Real) : (activeWindow T).Finite := by
    have hfin : (↑(window T) : Set Int).Finite := (window T).finite_toSet
    have hunion : activeWindow T =
        ⋃ q ∈ (↑(window T) : Set Int), fiber q := by
      ext a
      simp [activeWindow, fiber]
    rw [hunion]
    exact hfin.biUnion fun q _ => hfiber q
  have hwindowCard (T : Real) :
      (activeWindow T).ncard = ∑ q ∈ window T, (fiber q).ncard := by
    let fiberFin : Int → Finset (ActiveIndexHD data x) :=
      fun q => (hfiber q).toFinset
    have hpair : (↑(window T) : Set Int).PairwiseDisjoint fiberFin := by
      intro q _ r _ hqr
      simpa [fiberFin] using hdisj (Set.mem_univ q) (Set.mem_univ r) hqr
    have hcoe : (↑((window T).biUnion fiberFin) :
        Set (ActiveIndexHD data x)) = activeWindow T := by
      ext a
      simp [fiberFin, activeWindow, fiber]
    rw [← hcoe, Set.ncard_coe_finset, Finset.card_biUnion hpair]
    apply Finset.sum_congr rfl
    intro q hq
    exact (Set.ncard_eq_toFinset_card (fiber q) (hfiber q)).symm
  let bounded (T : Real) : Set (ActiveIndexHD data x) :=
    {a | poleCoordHD P.alpha P.beta x a.1.1 a.1.2 ∈ Set.Icc (-T) T}
  have hC : 0 ≤ poleShiftConstantHD P.beta := by
    unfold poleShiftConstantHD
    positivity
  have hR0 : 0 ≤ R := hC.trans hR.le
  have hboundedFinite : (bounded R).Finite := by
    let pole : ActiveIndexHD data x → Real := fun a =>
      poleCoordHD P.alpha P.beta x a.1.1 a.1.2
    have hmaps : Set.MapsTo pole (bounded R)
        (realPoleSetHD data x ∩ Set.Icc (-R) R) := by
      intro a ha
      exact ⟨⟨a, rfl⟩, ha⟩
    have hinj : Set.InjOn pole (bounded R) := by
      intro a _ b _ hab
      apply Subtype.ext
      exact point.fourierGood.analytic.poleInjective hab
    exact Set.Finite.of_injOn hmaps hinj
      (finite_realPoleSetHD_inter_Icc data x point.fourierGood.analytic R hR0)
  have hboundedCard : (bounded R).ncard = realPoleCountHD data x R := by
    unfold realPoleCountHD
    let pole : ActiveIndexHD data x → Real := fun a =>
      poleCoordHD P.alpha P.beta x a.1.1 a.1.2
    apply Set.ncard_congr (fun a _ => pole a)
    · intro a ha
      exact ⟨⟨a, rfl⟩, ha⟩
    · intro a b _ _ hab
      apply Subtype.ext
      exact point.fourierGood.analytic.poleInjective hab
    · intro p hp
      rcases hp.1 with ⟨a, rfl⟩
      exact ⟨a, hp.2, rfl⟩
  have hwindow_iff (T : Real) (q : Int) :
      q ∈ window T ↔ |(q : Real)| ≤ T := by
    simp only [window, Finset.mem_Icc]
    constructor
    · rintro ⟨hqL, hqU⟩
      rw [abs_le]
      constructor
      · have : (-(Int.floor T) : Real) ≤ (q : Real) := by exact_mod_cast hqL
        have hf : (Int.floor T : Real) ≤ T := Int.floor_le T
        linarith
      · exact Int.le_floor.mp hqU
    · intro hq
      rw [abs_le] at hq
      constructor
      · have hceil : Int.ceil (-T) ≤ q := Int.ceil_le.mpr hq.1
        simpa only [Int.ceil_neg] using hceil
      · exact Int.le_floor.mpr hq.2
  have hlower : activeWindow (R - poleShiftConstantHD P.beta) ⊆ bounded R := by
    intro a ha
    have hq : |(a.1.2 : Real)| ≤ R - poleShiftConstantHD P.beta :=
      (hwindow_iff _ _).mp ha
    have hpq := abs_poleCoordHD_sub_q_le
      P.alpha P.beta x a.1.1 a.1.2
    rw [Set.mem_setOf_eq, Set.mem_Icc, ← abs_le]
    calc
      |poleCoordHD P.alpha P.beta x a.1.1 a.1.2| ≤
          |poleCoordHD P.alpha P.beta x a.1.1 a.1.2 - (a.1.2 : Real)| +
            |(a.1.2 : Real)| := by
              simpa only [sub_add_cancel] using
                abs_add_le
                  (poleCoordHD P.alpha P.beta x a.1.1 a.1.2 - (a.1.2 : Real))
                  (a.1.2 : Real)
      _ ≤ poleShiftConstantHD P.beta +
          (R - poleShiftConstantHD P.beta) := add_le_add hpq hq
      _ = R := by ring
  have hupper : bounded R ⊆ activeWindow (R + poleShiftConstantHD P.beta) := by
    intro a ha
    have hp : |poleCoordHD P.alpha P.beta x a.1.1 a.1.2| ≤ R := by
      rw [abs_le]
      exact ha
    have hpq := abs_poleCoordHD_sub_q_le
      P.alpha P.beta x a.1.1 a.1.2
    apply (hwindow_iff _ _).mpr
    calc
      |(a.1.2 : Real)| ≤
          |(a.1.2 : Real) - poleCoordHD P.alpha P.beta x a.1.1 a.1.2| +
            |poleCoordHD P.alpha P.beta x a.1.1 a.1.2| := by
              simpa only [sub_add_cancel] using
                abs_add_le
                  ((a.1.2 : Real) - poleCoordHD P.alpha P.beta x a.1.1 a.1.2)
                  (poleCoordHD P.alpha P.beta x a.1.1 a.1.2)
      _ ≤ poleShiftConstantHD P.beta + R :=
        add_le_add (by simpa [abs_sub_comm] using hpq) hp
      _ = R + poleShiftConstantHD P.beta := add_comm _ _
  change (∑ q ∈ window (R - poleShiftConstantHD P.beta),
      multiplicityHD data (x - q • alphaTorusHD P.alpha)) ≤
      (realPoleCountHD data x R : Real) ∧
    (realPoleCountHD data x R : Real) ≤
      ∑ q ∈ window (R + poleShiftConstantHD P.beta),
        multiplicityHD data (x - q • alphaTorusHD P.alpha)
  constructor
  · simp_rw [hmult]
    norm_cast
    rw [← hwindowCard, ← hboundedCard]
    exact Set.ncard_le_ncard hlower hboundedFinite
  · simp_rw [hmult]
    norm_cast
    rw [← hwindowCard, ← hboundedCard]
    exact Set.ncard_le_ncard hupper
      (hactiveWindow (R + poleShiftConstantHD P.beta))

/- Proof idea: squeeze the pole count between fixed-width shifts of the two-sided
Birkhoff sums and show that all normalization and endpoint errors vanish. -/
theorem realPoleCountHD_density_nat (P : Params)
    {S : Set (RealVec P.d)} {f : RealVec P.d → Complex}
    (data : PositiveInputDataHD P.alpha P.beta S f) (x : Torus P.d)
    (point : PoleAveragePointDataHD data x) :
    Tendsto
      (fun N : Nat => (realPoleCountHD data x (N : Real) : Real) / (2 * (N : Real)))
      atTop (nhds (supportMassHD data)) := by
  let C : Real := poleShiftConstantHD P.beta
  have hC : 0 ≤ C := by
    dsimp only [C, poleShiftConstantHD]
    positivity
  let Km : Nat := ⌈C⌉₊
  let Kp : Nat := ⌊C⌋₊
  let sum : Nat → Real := fun N =>
    ∑ q ∈ Finset.Icc (-(N : Int)) (N : Int),
      multiplicityHD data (x - q • alphaTorusHD P.alpha)
  let avg : Nat → Real := fun N => (2 * (N : Real) + 1)⁻¹ * sum N
  have havg : Tendsto avg atTop (nhds (supportMassHD data)) :=
    point.averageTendsto
  have hsubTop : Tendsto (fun N : Nat => N - Km) atTop atTop := by
    apply tendsto_atTop.2
    intro M
    filter_upwards [eventually_ge_atTop (M + Km)] with N hN
    omega
  have haddTop : Tendsto (fun N : Nat => N + Kp) atTop atTop :=
    tendsto_add_atTop_nat Kp
  have hinv : Tendsto (fun N : Nat => ((N : Real))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_nhds_zero_nat
  let lowerRatio : Nat → Real := fun N =>
    (2 * ((N - Km : Nat) : Real) + 1) / (2 * (N : Real))
  let upperRatio : Nat → Real := fun N =>
    (2 * ((N + Kp : Nat) : Real) + 1) / (2 * (N : Real))
  have hlowerRatio : Tendsto lowerRatio atTop (nhds 1) := by
    have hlim : Tendsto
        (fun N : Nat => 1 - (((Km : Real) - 1 / 2) * ((N : Real))⁻¹))
        atTop (nhds 1) := by
      simpa using tendsto_const_nhds.sub (tendsto_const_nhds.mul hinv)
    apply hlim.congr'
    filter_upwards [eventually_ge_atTop Km, eventually_gt_atTop 0] with N hNK hN
    simp only [lowerRatio]
    have hN0 : (N : Real) ≠ 0 := by positivity
    rw [Nat.cast_sub hNK]
    field_simp
    ring
  have hupperRatio : Tendsto upperRatio atTop (nhds 1) := by
    have hlim : Tendsto
        (fun N : Nat => 1 + (((Kp : Real) + 1 / 2) * ((N : Real))⁻¹))
        atTop (nhds 1) := by
      simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul hinv)
    apply hlim.congr'
    filter_upwards [eventually_gt_atTop 0] with N hN
    simp only [upperRatio]
    have hN0 : (N : Real) ≠ 0 := by positivity
    norm_num only [Nat.cast_add]
    field_simp
    ring
  let lower : Nat → Real := fun N => lowerRatio N * avg (N - Km)
  let upper : Nat → Real := fun N => upperRatio N * avg (N + Kp)
  have hlower : Tendsto lower atTop (nhds (supportMassHD data)) := by
    simpa [lower] using hlowerRatio.mul (havg.comp hsubTop)
  have hupper : Tendsto upper atTop (nhds (supportMassHD data)) := by
    simpa [upper] using hupperRatio.mul (havg.comp haddTop)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · filter_upwards [eventually_ge_atTop (Km + 1)] with N hN
    have hCN : C < (N : Real) := by
      have hCceil : C ≤ (Km : Real) := by
        dsimp only [Km]
        exact Nat.le_ceil C
      have hKN : (Km : Real) < (N : Real) := by exact_mod_cast (by omega : Km < N)
      exact hCceil.trans_lt hKN
    have hsand := (realPoleCountHD_sandwich P data x point (N : Real)
      (by simpa only [C] using hCN)).1
    have hiw :
        Finset.Icc (-(Int.floor ((N : Real) - C)))
            (Int.floor ((N : Real) - C)) =
          Finset.Icc (-((N - Km : Nat) : Int)) ((N - Km : Nat) : Int) := by
      have hNK : Km ≤ N := by omega
      have hfloor : Int.floor ((N : Real) - C) = ((N - Km : Nat) : Int) := by
        change Int.floor (((N : Int) : Real) + -C) = ((N - Km : Nat) : Int)
        rw [Int.floor_intCast_add, Int.floor_neg]
        rw [← Int.natCast_ceil_eq_ceil hC]
        omega
      rw [hfloor]
    rw [hiw] at hsand
    have hfactor : lower N =
        (∑ q ∈ Finset.Icc (-((N - Km : Nat) : Int)) ((N - Km : Nat) : Int),
          multiplicityHD data (x - q • alphaTorusHD P.alpha)) /
            (2 * (N : Real)) := by
      simp only [lower, lowerRatio, avg, sum]
      have hm : (2 * ((N - Km : Nat) : Real) + 1) ≠ 0 := by positivity
      have hden : (2 * (N : Real)) ≠ 0 := by
        have : 0 < N := by omega
        positivity
      field_simp
    rw [hfactor]
    exact div_le_div_of_nonneg_right hsand (by positivity)
  · filter_upwards [eventually_ge_atTop (Km + 1)] with N hN
    have hCN : C < (N : Real) := by
      have hCceil : C ≤ (Km : Real) := by
        dsimp only [Km]
        exact Nat.le_ceil C
      have hKN : (Km : Real) < (N : Real) := by exact_mod_cast (by omega : Km < N)
      exact hCceil.trans_lt hKN
    have hsand := (realPoleCountHD_sandwich P data x point (N : Real)
      (by simpa only [C] using hCN)).2
    have hiw :
        Finset.Icc (-(Int.floor ((N : Real) + C)))
            (Int.floor ((N : Real) + C)) =
          Finset.Icc (-((N + Kp : Nat) : Int)) ((N + Kp : Nat) : Int) := by
      have hfloor : Int.floor ((N : Real) + C) = ((N + Kp : Nat) : Int) := by
        change Int.floor (((N : Int) : Real) + C) = ((N + Kp : Nat) : Int)
        rw [Int.floor_intCast_add]
        rw [← Int.natCast_floor_eq_floor hC]
        norm_cast
      rw [hfloor]
    rw [hiw] at hsand
    have hfactor :
        (∑ q ∈ Finset.Icc (-((N + Kp : Nat) : Int)) ((N + Kp : Nat) : Int),
          multiplicityHD data (x - q • alphaTorusHD P.alpha)) /
            (2 * (N : Real)) = upper N := by
      simp only [upper, upperRatio, avg, sum]
      have hm : (2 * ((N + Kp : Nat) : Real) + 1) ≠ 0 := by positivity
      have hden : (2 * (N : Real)) ≠ 0 := by
        have : 0 < N := by omega
        positivity
      field_simp
    rw [← hfactor]
    exact div_le_div_of_nonneg_right hsand (by positivity)

/- Proof idea: squeeze the monotone real-radius count between its natural floor and ceiling
radii, with the normalizations tending to one. -/
theorem realPoleCountHD_density (P : Params)
    {S : Set (RealVec P.d)} {f : RealVec P.d → Complex}
    (data : PositiveInputDataHD P.alpha P.beta S f) (x : Torus P.d)
    (point : PoleAveragePointDataHD data x) :
    Tendsto
      (fun R : Real => (realPoleCountHD data x R : Real) / (2 * R))
      atTop (nhds (supportMassHD data)) := by
  have hnat := realPoleCountHD_density_nat P data x point
  let natNorm : Nat → Real := fun N =>
    (realPoleCountHD data x (N : Real) : Real) / (2 * (N : Real))
  have hnat' : Tendsto natNorm atTop (nhds (supportMassHD data)) := hnat
  let lower : Real → Real := fun R => natNorm ⌊R⌋₊ * ((⌊R⌋₊ : Real) / R)
  let upper : Real → Real := fun R => natNorm ⌈R⌉₊ * ((⌈R⌉₊ : Real) / R)
  have hlower : Tendsto lower atTop (nhds (supportMassHD data)) := by
    simpa [lower] using
      (hnat'.comp (tendsto_nat_floor_atTop :
        Tendsto (fun R : Real => ⌊R⌋₊) atTop atTop)).mul
        (tendsto_nat_floor_div_atTop :
          Tendsto (fun R : Real => (⌊R⌋₊ : Real) / R) atTop (nhds 1))
  have hupper : Tendsto upper atTop (nhds (supportMassHD data)) := by
    simpa [upper] using
      (hnat'.comp (tendsto_nat_ceil_atTop :
        Tendsto (fun R : Real => ⌈R⌉₊) atTop atTop)).mul
        (tendsto_nat_ceil_div_atTop :
          Tendsto (fun R : Real => (⌈R⌉₊ : Real) / R) atTop (nhds 1))
  have hcountMono {r t : Real} (hr : 0 ≤ r) (hrt : r ≤ t) :
      realPoleCountHD data x r ≤ realPoleCountHD data x t := by
    unfold realPoleCountHD
    apply Set.ncard_le_ncard
    · rintro p ⟨hpPole, hpL, hpU⟩
      exact ⟨hpPole, by constructor <;> linarith⟩
    · exact finite_realPoleSetHD_inter_Icc data x
        point.fourierGood.analytic t (hr.trans hrt)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · filter_upwards [eventually_gt_atTop (1 : Real)] with R hR
    have hR0 : 0 < R := lt_trans zero_lt_one hR
    have hfloorPos : 0 < ⌊R⌋₊ := Nat.floor_pos.mpr hR.le
    have hfloorR : (⌊R⌋₊ : Real) ≤ R := Nat.floor_le hR0.le
    have hc : realPoleCountHD data x (⌊R⌋₊ : Real) ≤ realPoleCountHD data x R :=
      hcountMono (Nat.cast_nonneg _) hfloorR
    have heq : lower R =
        (realPoleCountHD data x (⌊R⌋₊ : Real) : Real) / (2 * R) := by
      simp only [lower, natNorm]
      have hf : (⌊R⌋₊ : Real) ≠ 0 := by positivity
      field_simp
    rw [heq]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hc) (by positivity)
  · filter_upwards [eventually_gt_atTop (1 : Real)] with R hR
    have hR0 : 0 < R := lt_trans zero_lt_one hR
    have hceilPos : 0 < ⌈R⌉₊ := Nat.ceil_pos.mpr hR0
    have hRceil : R ≤ (⌈R⌉₊ : Real) := Nat.le_ceil R
    have hc : realPoleCountHD data x R ≤ realPoleCountHD data x (⌈R⌉₊ : Real) :=
      hcountMono hR0.le hRceil
    have heq :
        (realPoleCountHD data x (⌈R⌉₊ : Real) : Real) / (2 * R) = upper R := by
      simp only [upper, natNorm]
      have hf : (⌈R⌉₊ : Real) ≠ 0 := by positivity
      field_simp
    rw [← heq]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hc) (by positivity)

/- Proof idea: use `Complex.norm_real` and the exact real-cast membership equivalence to
identify the finite complex open-ball pole set with the real open interval pole set. -/
theorem complexOpenPoleCountHD_eq_realOpen {d : Nat} {alpha beta : RealVec d}
    {S : Set (RealVec d)} {f : RealVec d → Complex}
    (data : PositiveInputDataHD alpha beta S f) (x : Torus d)
    (hx : AnalyticParameterHD data x) (R : Real) (hR : 0 < R) :
    complexOpenPoleCountHD data x R =
      (realPoleSetHD data x ∩ Set.Ioo (-R) R).ncard := by
  have hset : complexPoleSetHD data x ∩ Metric.ball 0 R =
      Complex.ofReal '' (realPoleSetHD data x ∩ Set.Ioo (-R) R) := by
    ext z
    constructor
    · rintro ⟨⟨p, hp, rfl⟩, hpR⟩
      refine ⟨p, ⟨hp, ?_⟩, rfl⟩
      simpa [Metric.mem_ball, abs_lt] using hpR
    · rintro ⟨p, ⟨hp, hpR⟩, rfl⟩
      refine ⟨⟨p, hp, rfl⟩, ?_⟩
      simpa [Metric.mem_ball, abs_lt] using hpR
  rw [complexOpenPoleCountHD, hset]
  exact Set.ncard_image_of_injective _ Complex.ofReal_injective

/- Proof idea: split the finite closed interval into the open interval and its at-most-two
endpoint set; prove both Nat inequalities directly, without truncated subtraction. -/
theorem realClosed_complexOpen_count_error_le_twoHD {d : Nat}
    {alpha beta : RealVec d} {S : Set (RealVec d)} {f : RealVec d → Complex}
    (data : PositiveInputDataHD alpha beta S f) (x : Torus d)
    (hx : AnalyticParameterHD data x) (R : Real) (hR : 0 < R) :
    complexOpenPoleCountHD data x R ≤ realPoleCountHD data x R ∧
      realPoleCountHD data x R ≤ complexOpenPoleCountHD data x R + 2 := by
  let A : Set Real := realPoleSetHD data x ∩ Set.Icc (-R) R
  let B : Set Real := realPoleSetHD data x ∩ Set.Ioo (-R) R
  have hAfin : A.Finite := by
    exact finite_realPoleSetHD_inter_Icc data x hx R hR.le
  have hBA : B ⊆ A := by
    rintro p ⟨hpPole, hpL, hpU⟩
    exact ⟨hpPole, hpL.le, hpU.le⟩
  have hBfin : B.Finite := hAfin.subset hBA
  have hBAcard : B.ncard ≤ A.ncard := Set.ncard_le_ncard hBA hAfin
  have hAsub : A ⊆ B ∪ ({-R, R} : Set Real) := by
    rintro p ⟨hpPole, hpL, hpU⟩
    by_cases hlow : -R < p
    · by_cases hupp : p < R
      · exact Or.inl ⟨hpPole, hlow, hupp⟩
      · right
        have hpR : p = R := le_antisymm hpU (not_lt.mp hupp)
        simp [hpR]
    · right
      have hpR : p = -R := le_antisymm (not_lt.mp hlow) hpL
      simp [hpR]
  have hAcard : A.ncard ≤ B.ncard + 2 := by
    have hpairCard : ({-R, R} : Set Real).ncard ≤ 2 := by
      calc
        ({-R, R} : Set Real).ncard ≤ ({R} : Set Real).ncard + 1 :=
          Set.ncard_insert_le _ _
        _ = 2 := by simp
    calc
      A.ncard ≤ (B ∪ ({-R, R} : Set Real)).ncard :=
        Set.ncard_le_ncard hAsub (hBfin.union (Set.toFinite {-R, R}))
      _ ≤ B.ncard + ({-R, R} : Set Real).ncard := Set.ncard_union_le _ _
      _ ≤ B.ncard + 2 := Nat.add_le_add_left hpairCard _
  rw [complexOpenPoleCountHD_eq_realOpen data x hx R hR]
  change B.ncard ≤ A.ncard ∧ A.ncard ≤ B.ncard + 2
  exact ⟨hBAcard, hAcard⟩

/- Proof idea: compare the real closed and complex open counts by the uniform two-endpoint
error and squeeze after the sole casts from Nat to Real. -/
theorem complexOpenPoleCountHD_density (P : Params)
    {S : Set (RealVec P.d)} {f : RealVec P.d → Complex}
    (data : PositiveInputDataHD P.alpha P.beta S f) (x : Torus P.d)
    (point : PoleAveragePointDataHD data x) :
    Tendsto
      (fun R : Real => (complexOpenPoleCountHD data x R : Real) / (2 * R))
      atTop (nhds (supportMassHD data)) := by
  let a : Real → Real := fun R =>
    (realPoleCountHD data x R : Real) / (2 * R)
  let b : Real → Real := fun R =>
    (complexOpenPoleCountHD data x R : Real) / (2 * R)
  have hbound : ∀ᶠ R : Real in atTop, |b R - a R| ≤ R⁻¹ := by
    filter_upwards [eventually_gt_atTop (0 : Real)] with R hR
    have herr := realClosed_complexOpen_count_error_le_twoHD data x
      point.fourierGood.analytic R hR
    have hdiff : (realPoleCountHD data x R : Real) -
        (complexOpenPoleCountHD data x R : Real) ≤ 2 := by
      have hcast : (realPoleCountHD data x R : Real) ≤
          (complexOpenPoleCountHD data x R : Real) + 2 := by
        exact_mod_cast herr.2
      linarith
    have hnonneg : 0 ≤ (realPoleCountHD data x R : Real) -
        (complexOpenPoleCountHD data x R : Real) := by
      exact sub_nonneg.mpr (by exact_mod_cast herr.1)
    have herrR : |(realPoleCountHD data x R : Real) -
        (complexOpenPoleCountHD data x R : Real)| ≤ (2 : Real) := by
      rw [abs_of_nonneg hnonneg]
      exact hdiff
    have hden : 0 < 2 * R := mul_pos (by norm_num) hR
    calc
      |b R - a R| =
          |(complexOpenPoleCountHD data x R : Real) -
            (realPoleCountHD data x R : Real)| / (2 * R) := by
        simp only [a, b]
        rw [← sub_div, abs_div, abs_of_pos hden]
      _ ≤ 2 / (2 * R) :=
        div_le_div_of_nonneg_right (by simpa [abs_sub_comm] using herrR) hden.le
      _ = R⁻¹ := by field_simp
  have habs : Tendsto (fun R : Real => |b R - a R|) atTop (nhds 0) :=
    squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) hbound
      (tendsto_inv_atTop_zero : Tendsto (fun R : Real => R⁻¹) atTop (nhds 0))
  have hdiff : Tendsto (fun R : Real => b R - a R) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa [Real.norm_eq_abs] using habs
  have ha : Tendsto a atTop (nhds (supportMassHD data)) :=
    realPoleCountHD_density P data x point
  simpa [a, b, sub_add_cancel] using ha.add hdiff

/- Proof idea: intersect the Fourier-good, all-orbit-finite, and Birkhoff-average conull
sets; derive both count-density limits at the same point and build one shared record. -/
theorem poleGoodParameterHD_ae (P : Params)
    {S : Set (RealVec P.d)} {f : RealVec P.d → Complex}
    (data : PositiveInputDataHD P.alpha P.beta S f) (hSlt : volume S < 1) :
    ∀ᵐ x : Torus P.d ∂volume, PoleGoodParameterHD data x := by
  have hfiniteAll : ∀ᵐ x : Torus P.d ∂volume, ∀ q : Int,
      multiplicityENNHD data (uOrbitHD P.alpha x q) < ∞ := by
    apply ae_all_iff.2
    intro q
    let mu : Measure (Torus P.d) := volume
    letI : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
    let nu : Measure (Torus P.d) := volume
    have hmunu : mu = nu := by
      dsimp [mu, nu]
      change Measure.pi
          (fun _ : Fin P.d ↦ @volume UnitAddCircle (AddCircle.measureSpace 1)) =
        Measure.pi (fun _ : Fin P.d ↦ AddCircle.haarAddCircle)
      congr 1
      funext i
      change ENNReal.ofReal 1 • Measure.addHaarMeasure ⊤ =
        Measure.addHaarMeasure ⊤
      simp
    have hfinMu : ∀ᵐ y : Torus P.d ∂mu, multiplicityENNHD data y < ∞ := by
      exact multiplicityENNHD_lt_top_ae data hSlt
    have hfinNu : ∀ᵐ y : Torus P.d ∂nu, multiplicityENNHD data y < ∞ := by
      rw [← hmunu]
      exact hfinMu
    let shift : Torus P.d := q • alphaTorusHD P.alpha
    have hpreNu : ∀ᵐ x : Torus P.d ∂nu,
        multiplicityENNHD data (x - shift) < ∞ := by
      change (fun x : Torus P.d => x - shift) ⁻¹'
        {y | multiplicityENNHD data y < ∞} ∈ ae nu
      have hmp := measurePreserving_torus_sub (d := P.d) shift
      exact hmp.quasiMeasurePreserving.tendsto_ae hfinNu
    change ∀ᵐ x : Torus P.d ∂mu,
      multiplicityENNHD data (uOrbitHD P.alpha x q) < ∞
    rw [hmunu]
    simpa [uOrbitHD, shift] using hpreNu
  filter_upwards [fourierGoodParameterHD_ae P data hSlt,
    multiplicity_twoSided_average_aeHD P data hSlt,
    hfiniteAll] with x hxFourier hxAverage hxFinite
  let point : PoleAveragePointDataHD data x :=
    { fourierGood := hxFourier
      orbitFinite := hxFinite
      averageTendsto := hxAverage }
  exact
    { fourierGood := hxFourier
      orbitFinite := hxFinite
      realPoleDensity := realPoleCountHD_density P data x point
      complexPoleDensity := complexOpenPoleCountHD_density P data x point }

end UniversalCompletenessHD.Internal
