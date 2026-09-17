import UniversalCompletenessHD.PoleDensity
import UniversalCompletenessHD.BoundaryGrowth

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace UniversalCompletenessHD.Internal

/- Proof idea: construct the base counting datum once, obtain the finite positive analytic
order at zero, factor locally, glue the removable quotient, and port the away-zero order
and all-point pole-multiplicity identities from the proved scalar proof. -/
private theorem exists_originNormalizationDataHD (P : Params)
    {S : Set (RealVec P.d)} {f : RealVec P.d → Complex}
    (data : PositiveInputDataHD P.alpha P.beta S f) (x : Torus P.d)
    (hx : FourierGoodParameterHD data x)
    (hactive : Nonempty (ActiveIndexHD data x)) :
    Nonempty (OriginNormalizationDataHD data x) := by
  classical
  let F : Complex → Complex := activeMHD data x
  let base : Theorem12.Generic.MeromorphicCountingData F :=
    Classical.choice (activeMHD_countingData data x hx.analytic hactive)
  have hzeroNotPole : (0 : Complex) ∉ complexPoleSetHD data x := by
    rintro ⟨y, ⟨a, rfl⟩, hy⟩
    apply poleCoordHD_not_int_of_not_sineBad P.alpha P.beta x hx.analytic.offBad
      a.1.1 a.1.2 0
    exact_mod_cast hy
  have hclosedPoleSet : IsClosed (complexPoleSetHD data x) := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro z hz
    let R : Real := ‖z‖ + 1
    have hR : 0 ≤ R := by
      dsimp only [R]
      positivity
    have hzball : z ∈ Metric.ball (0 : Complex) R := by
      simp [Metric.mem_ball, R]
    let poleSet : Set Complex :=
      complexPoleSetHD data x ∩ Metric.closedBall 0 R
    have hpoleSetFinite : poleSet.Finite :=
      finite_complexPoleSetHD_inter_closedBall data x hx.analytic R hR
    have hzP : z ∉ poleSet := fun hzP => hz hzP.1
    have hopen : IsOpen (Metric.ball (0 : Complex) R \ poleSet) :=
      IsOpen.sdiff Metric.isOpen_ball hpoleSetFinite.isClosed
    refine mem_of_superset (hopen.mem_nhds ⟨hzball, hzP⟩) ?_
    intro w hw
    rw [Set.mem_compl_iff]
    intro hwPole
    exact hw.2 ⟨hwPole, Metric.ball_subset_closedBall hw.1⟩
  have hFanalytic : AnalyticAt Complex F 0 := by
    have hmem : (0 : Complex) ∈ Set.univ \ complexPoleSetHD data x :=
      ⟨Set.mem_univ _, hzeroNotPole⟩
    have hopen : IsOpen (Set.univ \ complexPoleSetHD data x) :=
      IsOpen.sdiff isOpen_univ hclosedPoleSet
    have hwithin := analyticOn_activeM_compl_polesHD data x hx.analytic
      (0 : Complex) hmem
    rw [← analyticWithinAt_univ]
    exact hwithin.mono_of_mem_nhdsWithin (by simpa using hopen.mem_nhds hmem)
  have hFzero : F 0 = 0 := activeMHD_zero data x hx.analytic
  have horderFinite : analyticOrderAt F 0 ≠ ⊤ := by
    intro htop
    apply base.order_ne_top 0
    rw [hFanalytic.meromorphicOrderAt_eq, htop]
    simp
  let nu : Nat := analyticOrderNatAt F 0
  have horderNeZero : analyticOrderAt F 0 ≠ 0 :=
    hFanalytic.analyticOrderAt_ne_zero.mpr hFzero
  have hnuNe : nu ≠ 0 := by
    intro hnu
    apply horderNeZero
    have hcast : (nu : ENat) = analyticOrderAt F 0 := ENat.coe_toNat horderFinite
    rw [hnu] at hcast
    simpa using hcast.symm
  have hnuPos : 0 < nu := Nat.pos_of_ne_zero hnuNe
  obtain ⟨G, hGanalytic, hGzero, hfactor⟩ :=
    hFanalytic.analyticOrderAt_ne_top.mp horderFinite
  let N : Complex → Complex := fun z => if z = 0 then G z else F z / z ^ nu
  have hNeqG : N =ᶠ[nhds (0 : Complex)] G := by
    filter_upwards [hfactor] with z hzfactor
    by_cases hz : z = 0
    · simp [N, hz]
    · simp only [N, hz, if_false]
      rw [hzfactor]
      simp only [sub_zero, smul_eq_mul]
      dsimp only [nu]
      field_simp
  have hNanalytic : AnalyticAt Complex N 0 := hGanalytic.congr hNeqG.symm
  have hNzero : N 0 ≠ 0 := by simpa [N] using hGzero
  let Q : Complex → Complex := fun z => F z / z ^ nu
  have hQmeromorphic : MeromorphicOn Q Set.univ := by
    intro z _
    exact (meromorphicOn_activeMHD data x hx.analytic z (Set.mem_univ z)).div
      (analyticAt_id.pow nu).meromorphicAt
  have hNeqQ (z : Complex) : N =ᶠ[nhdsWithin z ({z} : Set Complex)ᶜ] Q := by
    by_cases hz : z = 0
    · subst z
      filter_upwards [self_mem_nhdsWithin] with w hw
      have hw0 : w ≠ 0 := by simpa using hw
      simp [N, Q, hw0]
    · have hzeroCompl : ({0} : Set Complex)ᶜ ∈ nhds z :=
        isOpen_compl_singleton.mem_nhds (by simpa using hz)
      have hzeroCompl' : ({0} : Set Complex)ᶜ ∈ nhdsWithin z ({z} : Set Complex)ᶜ :=
        Filter.Eventually.filter_mono nhdsWithin_le_nhds hzeroCompl
      filter_upwards [hzeroCompl'] with w hw
      have hw0 : w ≠ 0 := by
        change w ≠ 0 at hw
        exact hw
      simp [N, Q, hw0]
  have hNmeromorphic : MeromorphicOn N Set.univ := by
    intro z _
    exact (hQmeromorphic z (Set.mem_univ z)).congr (hNeqQ z).symm
  have hmerOrderEq (z : Complex) (hz : z ≠ 0) :
      meromorphicOrderAt N z = meromorphicOrderAt F z := by
    rw [meromorphicOrderAt_congr (hNeqQ z)]
    change meromorphicOrderAt (F / fun w => w ^ nu) z = meromorphicOrderAt F z
    have hpowAnalytic : AnalyticAt Complex (fun w : Complex => w ^ nu) z :=
      analyticAt_id.pow nu
    have hFmeromorphic : MeromorphicAt F z :=
      meromorphicOn_activeMHD data x hx.analytic z (by simp)
    rw [meromorphicOrderAt_div hFmeromorphic hpowAnalytic.meromorphicAt]
    rw [hpowAnalytic.meromorphicOrderAt_eq,
      (hpowAnalytic.analyticOrderAt_eq_zero).2 (pow_ne_zero nu hz)]
    simp
  let ord : Complex → Int := fun z => if z = 0 then 0 else base.order z
  have hordSpec (z : Complex) :
      ((ord z : Int) : WithTop Int) = meromorphicOrderAt N z := by
    by_cases hz : z = 0
    · subst z
      simp only [ord, if_pos]
      rw [hNanalytic.meromorphicOrderAt_eq,
        (hNanalytic.analyticOrderAt_eq_zero).2 hNzero]
      simp
    · simp only [ord, hz, if_false]
      rw [base.order_spec, hmerOrderEq z hz]
  have hordFinite (R : Real) :
      Set.Finite ({z : Complex | ord z ≠ 0} ∩ Metric.closedBall 0 R) := by
    apply (base.finite_orderSupport_closedBall R).subset
    intro z hz
    refine ⟨?_, hz.2⟩
    intro hbase
    apply hz.1
    simp [ord, hbase]
  let countData : Theorem12.Generic.MeromorphicCountingData N :=
    { meromorphicOn_univ := hNmeromorphic
      order_ne_top := fun z => by rw [← hordSpec z]; exact WithTop.coe_ne_top
      order := ord
      order_spec := hordSpec
      finite_orderSupport_closedBall := hordFinite }
  have horderAway (z : Complex) (hz : z ≠ 0) :
      countData.order z = base.order z := by
    simp [countData, ord, hz]
  have hbaseZeroNonneg : 0 ≤ base.order 0 := by
    have htop : (0 : WithTop Int) ≤ meromorphicOrderAt F 0 :=
      hFanalytic.meromorphicOrderAt_nonneg
    rw [← base.order_spec 0] at htop
    exact_mod_cast htop
  have hbaseZeroPoleMultiplicity : Int.toNat (-base.order 0) = 0 :=
    Int.toNat_eq_zero.mpr (neg_nonpos.mpr hbaseZeroNonneg)
  have hpoleMultiplicity (z : Complex) :
      Int.toNat (-countData.order z) = Int.toNat (-base.order z) := by
    by_cases hz : z = 0
    · subst z
      simp [countData, ord, hbaseZeroPoleMultiplicity]
    · rw [horderAway z hz]
  exact ⟨
    { nu := nu
      nu_pos := hnuPos
      baseCountingData := base
      normalizedM := N
      normalized_eq := by
        intro z hz
        simp [N, F, hz]
      analyticAt_zero := hNanalytic
      value_zero_ne := hNzero
      meromorphicOn_univ := hNmeromorphic
      countingData := countData
      order_eq_away_zero := horderAway
      poleMultiplicity_eq := hpoleMultiplicity }⟩

/- Proof idea: in every `(m+1,m+2)`, avoid the finitely many moduli of divisor points in
the bounded annulus; the interval bounds give positivity and convergence to infinity. -/
private theorem exists_cleanRadiusDataHD {F : Complex → Complex}
    (countData : Theorem12.Generic.MeromorphicCountingData F)
    (hF0analytic : AnalyticAt Complex F 0) (hF0 : F 0 ≠ 0) :
    Nonempty (CleanRadiusDataHD F) := by
  let good : Set Complex := {z | AnalyticAt Complex F z} ∩ {z | F z ≠ 0}
  have _hzeroGood : (0 : Complex) ∈ good := ⟨hF0analytic, hF0⟩
  have hneTop : ∀ z ∈ (Set.univ : Set Complex), meromorphicOrderAt F z ≠ ⊤ := by
    intro z _
    exact countData.order_ne_top z
  have hgoodUniv : good ∈ codiscreteWithin (Set.univ : Set Complex) := by
    apply Filter.inter_mem
    · exact countData.meromorphicOn_univ.analyticAt_mem_codiscreteWithin
    · exact MeromorphicAt.MeromorphicOn.codiscreteWithin_setOf_ne_zero
        countData.meromorphicOn_univ hneTop
  have hfiniteBad (m : Nat) :
      (Metric.closedBall (0 : Complex) ((m : Real) + 2) \ good).Finite := by
    apply (isCompact_closedBall (0 : Complex) ((m : Real) + 2)).finite_sdiff_of_mem_codiscreteWithin
    exact (Filter.codiscreteWithin_mono (Set.subset_univ _)) hgoodUniv
  have hchoose (m : Nat) : ∃ r : Real,
      r ∈ Set.Ioo ((m : Real) + 1) ((m : Real) + 2) ∧
        r ∉ Norm.norm '' (Metric.closedBall (0 : Complex) ((m : Real) + 2) \ good) := by
    let badRadii : Set Real := Norm.norm ''
      (Metric.closedBall (0 : Complex) ((m : Real) + 2) \ good)
    have hbadFinite : badRadii.Finite := (hfiniteBad m).image _
    have hintervalInfinite :
        (Set.Ioo ((m : Real) + 1) ((m : Real) + 2)).Infinite := by
      apply Set.Ioo_infinite
      linarith
    have hdiffInfinite := hintervalInfinite.sdiff hbadFinite
    exact Set.nonempty_def.mp hdiffInfinite.nonempty
  let R : Nat → Real := fun m => Classical.choose (hchoose m)
  have hRspec (m : Nat) :
      R m ∈ Set.Ioo ((m : Real) + 1) ((m : Real) + 2) ∧
        R m ∉ Norm.norm '' (Metric.closedBall (0 : Complex) ((m : Real) + 2) \ good) :=
    Classical.choose_spec (hchoose m)
  refine ⟨{
    R := R
    bounds := fun m => (hRspec m).1
    tendsto_R := ?_
    clean := ?_
  }⟩
  · rw [tendsto_atTop_atTop]
    intro b
    obtain ⟨N : Nat, hN : b < N⟩ := exists_nat_gt b
    refine ⟨N, fun n hn => ?_⟩
    have hNn : (N : Real) ≤ (n : Real) := by exact_mod_cast hn
    have hnR : (n : Real) + 1 < R n := (hRspec n).1.1
    linarith
  · intro m z hz
    have hzBall : z ∈ Metric.closedBall (0 : Complex) ((m : Real) + 2) := by
      rw [Metric.mem_closedBall, dist_zero_right, hz]
      exact (hRspec m).1.2.le
    have hzGood : z ∈ good := by
      by_contra hzNotGood
      apply (hRspec m).2
      exact ⟨z, ⟨hzBall, hzNotGood⟩, hz⟩
    exact hzGood

/- Proof idea: transfer each nonzero integer zero through the away-zero normalization,
count signed integers in the open disk with multiplicity, and absorb the lost origin. -/
private theorem normalized_zeroCount_lowerDensity_oneHD (P : Params)
    {S : Set (RealVec P.d)} {f : RealVec P.d → Complex}
    (data : PositiveInputDataHD P.alpha P.beta S f) (x : Torus P.d)
    (hx : FourierGoodParameterHD data x)
    (normData : OriginNormalizationDataHD data x)
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∀ᶠ r : Real in atTop,
      2 * (1 - epsilon) * r ≤
        (Theorem12.Generic.zeroCount normData.countingData r : Real) := by
  classical
  have hclosedPoleSet : IsClosed (complexPoleSetHD data x) := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro z hz
    let R : Real := ‖z‖ + 1
    have hR : 0 ≤ R := by
      dsimp only [R]
      positivity
    have hzball : z ∈ Metric.ball (0 : Complex) R := by
      simp [Metric.mem_ball, R]
    let poleSet : Set Complex :=
      complexPoleSetHD data x ∩ Metric.closedBall 0 R
    have hpoleSetFinite : poleSet.Finite :=
      finite_complexPoleSetHD_inter_closedBall data x hx.analytic R hR
    have hzP : z ∉ poleSet := fun hzP => hz hzP.1
    have hopen : IsOpen (Metric.ball (0 : Complex) R \ poleSet) :=
      IsOpen.sdiff Metric.isOpen_ball hpoleSetFinite.isClosed
    refine mem_of_superset (hopen.mem_nhds ⟨hzball, hzP⟩) ?_
    intro w hw
    rw [Set.mem_compl_iff]
    intro hwPole
    exact hw.2 ⟨hwPole, Metric.ball_subset_closedBall hw.1⟩
  have hzeroMultiplicity (k : Int) (hk : k ≠ 0) :
      1 ≤ Int.toNat (normData.countingData.order (k : Complex)) := by
    have hkNotPole : (k : Complex) ∉ complexPoleSetHD data x := by
      rintro ⟨y, ⟨a, rfl⟩, hy⟩
      apply poleCoordHD_not_int_of_not_sineBad P.alpha P.beta x
        hx.analytic.offBad a.1.1 a.1.2 k
      exact_mod_cast hy
    have hkMem : (k : Complex) ∈ Set.univ \ complexPoleSetHD data x :=
      ⟨Set.mem_univ _, hkNotPole⟩
    have hopen : IsOpen (Set.univ \ complexPoleSetHD data x) :=
      IsOpen.sdiff isOpen_univ hclosedPoleSet
    have hanWithin := analyticOn_activeM_compl_polesHD data x hx.analytic
      (k : Complex) hkMem
    have han : AnalyticAt Complex (activeMHD data x) (k : Complex) := by
      rw [← analyticWithinAt_univ]
      exact hanWithin.mono_of_mem_nhdsWithin (by simpa using hopen.mem_nhds hkMem)
    have hzero := activeMHD_int_eq_zero P data x hx k
    have hanalyticOrderPos : 0 < analyticOrderAt (activeMHD data x) (k : Complex) :=
      pos_iff_ne_zero.mpr (han.analyticOrderAt_ne_zero.mpr hzero)
    have hmerOrderPos : 0 < meromorphicOrderAt (activeMHD data x) (k : Complex) := by
      rw [han.meromorphicOrderAt_eq]
      have hcastStrict : StrictMono (fun n : Nat => (n : Int)) := by
        intro a b hab
        change (a : Int) < (b : Int)
        omega
      simpa using (ENat.strictMono_map_iff.mpr hcastStrict hanalyticOrderPos)
    have hbaseOrderPos : 0 < normData.baseCountingData.order (k : Complex) := by
      rw [← normData.baseCountingData.order_spec (k : Complex)] at hmerOrderPos
      exact_mod_cast hmerOrderPos
    rw [normData.order_eq_away_zero (k : Complex) (by exact_mod_cast hk)]
    omega
  have hcountLower (r : Real) (hr : 0 < r) (N : Nat) (hNr : (N : Real) < r) :
      2 * N ≤ Theorem12.Generic.zeroCount normData.countingData r := by
    let intEmbedding : Int ↪ Complex :=
      ⟨fun k => (k : Complex), fun a b h => by
        have hab : (a : Real) = (b : Real) := by
          apply Complex.ofReal_injective
          simpa using h
        exact_mod_cast hab⟩
    let K : Finset Int := (Finset.Icc (-(N : Int)) (N : Int)).erase 0
    let Z : Finset Complex := K.map intEmbedding
    let s : Finset Complex :=
      (normData.countingData.finite_orderSupport_closedBall r).toFinset
    have hKcard : K.card = 2 * N := by
      dsimp only [K]
      rw [Finset.card_erase_of_mem (by simp)]
      rw [Int.card_Icc]
      have hnonneg : 0 ≤ (N : Int) + 1 - (-(N : Int)) := by omega
      have htoNat : ((N : Int) + 1 - (-(N : Int))).toNat = 2 * N + 1 := by
        have hcast :
            ((((N : Int) + 1 - (-(N : Int))).toNat : Nat) : Int) =
              (((2 * N + 1 : Nat) : Nat) : Int) := by
          rw [Int.toNat_of_nonneg hnonneg]
          push_cast
          omega
        exact_mod_cast hcast
      rw [htoNat]
      omega
    have hZcard : Z.card = 2 * N := by
      rw [show Z.card = K.card by exact Finset.card_map intEmbedding, hKcard]
    have hZsub : Z ⊆ s := by
      intro z hz
      rcases Finset.mem_map.mp hz with ⟨k, hkK, rfl⟩
      have hkIcc : k ∈ Finset.Icc (-(N : Int)) (N : Int) :=
        (Finset.mem_erase.mp hkK).2
      have hk0 : k ≠ 0 := fun h => (Finset.mem_erase.mp hkK).1 h
      have hmult := hzeroMultiplicity k hk0
      apply (Set.Finite.mem_toFinset _).mpr
      refine ⟨?_, ?_⟩
      · intro horder
        change normData.countingData.order (k : Complex) = 0 at horder
        rw [horder] at hmult
        norm_num at hmult
      · rw [Metric.mem_closedBall, dist_zero_right]
        have hkabs : |k| ≤ (N : Int) := (abs_le).2 (by simpa using hkIcc)
        have hknorm : ‖(k : Complex)‖ ≤ (N : Real) := by
          simpa using (show (|k| : Real) ≤ (N : Real) by exact_mod_cast hkabs)
        exact hknorm.trans hNr.le
    rw [Theorem12.Generic.zeroCount, if_neg (not_le.mpr hr)]
    change 2 * N ≤ ∑ z ∈ s,
      if ‖z‖ < r then Int.toNat (normData.countingData.order z) else 0
    calc
      2 * N = ∑ _z ∈ Z, 1 := by simp [hZcard]
      _ ≤ ∑ z ∈ Z,
          if ‖z‖ < r then Int.toNat (normData.countingData.order z) else 0 := by
        apply Finset.sum_le_sum
        intro z hz
        rcases Finset.mem_map.mp hz with ⟨k, hkK, rfl⟩
        have hkIcc := (Finset.mem_erase.mp hkK).2
        have hk0 : k ≠ 0 := fun h => (Finset.mem_erase.mp hkK).1 h
        rw [if_pos]
        · exact hzeroMultiplicity k hk0
        have hkabs : |k| ≤ (N : Int) := (abs_le).2 (by simpa using hkIcc)
        have hknorm : ‖(k : Complex)‖ ≤ (N : Real) := by
          simpa using (show (|k| : Real) ≤ (N : Real) by exact_mod_cast hkabs)
        exact hknorm.trans_lt hNr
      _ ≤ ∑ z ∈ s,
          if ‖z‖ < r then Int.toNat (normData.countingData.order z) else 0 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hZsub
        intro z hz hzZ
        exact Nat.zero_le _
  by_cases hepsilonLarge : 1 ≤ epsilon
  · filter_upwards [eventually_gt_atTop (0 : Real)] with r hr
    have : 2 * (1 - epsilon) * r ≤ 0 := by nlinarith
    exact this.trans (Nat.cast_nonneg _)
  · have hthreshold : ∀ᶠ r : Real in atTop, max 3 (2 / epsilon) ≤ r :=
      eventually_ge_atTop _
    filter_upwards [hthreshold] with r hr
    have hr3 : 3 ≤ r := (le_max_left _ _).trans hr
    have hrpos : 0 < r := by linarith
    let N : Nat := ⌊r⌋₊ - 1
    have hfloorTwo : 2 ≤ ⌊r⌋₊ := by
      have h2r : (2 : Real) ≤ r := by linarith
      exact Nat.le_floor h2r
    have hNr : (N : Real) < r := by
      dsimp only [N]
      rw [Nat.cast_sub (by omega : 1 ≤ ⌊r⌋₊), Nat.cast_one]
      linarith [Nat.floor_le hrpos.le]
    have hNlower : r - 2 < (N : Real) := by
      dsimp only [N]
      rw [Nat.cast_sub (by omega : 1 ≤ ⌊r⌋₊), Nat.cast_one]
      linarith [Nat.sub_one_lt_floor r]
    have hepsr : 2 ≤ epsilon * r := by
      have hdiv := (le_max_right (3 : Real) (2 / epsilon)).trans hr
      simpa [mul_comm] using (div_le_iff₀ hepsilon).mp hdiv
    have htarget : (1 - epsilon) * r ≤ (N : Real) := by nlinarith
    have hcount := hcountLower r hrpos N hNr
    calc
      2 * (1 - epsilon) * r = 2 * ((1 - epsilon) * r) := by ring
      _ ≤ 2 * (N : Real) := mul_le_mul_of_nonneg_left htarget (by norm_num)
      _ ≤ (Theorem12.Generic.zeroCount normData.countingData r : Real) := by
        exact_mod_cast hcount

/- Proof idea: transfer pole multiplicities to the base counting datum, identify its
negative orders with exactly the simple active poles, and equate the finite disk sums. -/
private theorem poleCount_normalized_eq_complexOpenPoleCountHD (P : Params)
    {S : Set (RealVec P.d)} {f : RealVec P.d → Complex}
    (data : PositiveInputDataHD P.alpha P.beta S f) (x : Torus P.d)
    (hx : FourierGoodParameterHD data x)
    (normData : OriginNormalizationDataHD data x) (r : Real) (hr : 0 < r) :
    Theorem12.Generic.poleCount normData.countingData r =
      complexOpenPoleCountHD data x r := by
  classical
  let poleSet : Set Complex := complexPoleSetHD data x ∩ Metric.ball 0 r
  let s : Finset Complex :=
    (normData.countingData.finite_orderSupport_closedBall r).toFinset
  have hbaseMult (z : Complex) :
      Int.toNat (-normData.baseCountingData.order z) =
        if z ∈ complexPoleSetHD data x then 1 else 0 := by
    by_cases hz : z ∈ complexPoleSetHD data x
    · rw [if_pos hz]
      rcases hz with ⟨y, ⟨a, rfl⟩, rfl⟩
      have hord := normData.baseCountingData.order_spec
        (poleCoordHD P.alpha P.beta x a.1.1 a.1.2 : Complex)
      rw [meromorphicOrderAt_activeM_poleHD data x hx.analytic a] at hord
      have hordInt : normData.baseCountingData.order
          (poleCoordHD P.alpha P.beta x a.1.1 a.1.2 : Complex) = -1 := by
        have hord' :
            ((normData.baseCountingData.order
                (poleCoordHD P.alpha P.beta x a.1.1 a.1.2 : Complex) : Int) :
                WithTop Int) = (((-1 : Int) : Int) : WithTop Int) := by
          simpa using hord
        exact WithTop.coe_eq_coe.mp hord'
      simp [hordInt]
    · rw [if_neg hz]
      have horderNonnegTop : (0 : WithTop Int) ≤
          ((normData.baseCountingData.order z : Int) : WithTop Int) := by
        rw [normData.baseCountingData.order_spec z]
        exact le_of_not_gt ((activeMHD_hasPoleAt_iff data x hx.analytic z).not.mpr hz)
      have horderNonneg : 0 ≤ normData.baseCountingData.order z := by
        exact_mod_cast horderNonnegTop
      exact Int.toNat_eq_zero.mpr (neg_nonpos.mpr horderNonneg)
  have hmult (z : Complex) :
      Int.toNat (-normData.countingData.order z) =
        if z ∈ complexPoleSetHD data x then 1 else 0 := by
    rw [normData.poleMultiplicity_eq z]
    exact hbaseMult z
  have hpoleSetFinite : poleSet.Finite := by
    apply (finite_complexPoleSetHD_inter_closedBall data x hx.analytic r hr.le).subset
    intro z hz
    exact ⟨hz.1, Metric.ball_subset_closedBall hz.2⟩
  have hPsub : hpoleSetFinite.toFinset ⊆ s := by
    intro z hz
    have hzP : z ∈ poleSet := (Set.Finite.mem_toFinset hpoleSetFinite).mp hz
    apply (Set.Finite.mem_toFinset _).mpr
    refine ⟨?_, Metric.ball_subset_closedBall hzP.2⟩
    intro horder
    have hm := hmult z
    rw [horder] at hm
    simp [hzP.1] at hm
  rw [Theorem12.Generic.poleCount, if_neg (not_le.mpr hr), complexOpenPoleCountHD]
  rw [Set.ncard_eq_toFinset_card poleSet hpoleSetFinite]
  change (∑ z ∈ s,
      if ‖z‖ < r then Int.toNat (-normData.countingData.order z) else 0) =
    hpoleSetFinite.toFinset.card
  calc
    (∑ z ∈ s,
        if ‖z‖ < r then Int.toNat (-normData.countingData.order z) else 0) =
        ∑ z ∈ s, if z ∈ hpoleSetFinite.toFinset then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [hmult z]
      by_cases hpole : z ∈ complexPoleSetHD data x <;>
        by_cases hzr : ‖z‖ < r <;> simp [poleSet, hpole, hzr]
    _ = hpoleSetFinite.toFinset.card := by
      rw [← Finset.sum_filter]
      simp only [Finset.filter_mem_eq_inter]
      rw [Finset.inter_eq_right.mpr hPsub]
      simp

/- Proof idea: rewrite normalized divisor poles as complex open poles and use the
all-real-radius density limit to obtain the eventual epsilon upper bound. -/
private theorem normalized_poleCount_upperDensityHD (P : Params)
    {S : Set (RealVec P.d)} {f : RealVec P.d → Complex}
    (data : PositiveInputDataHD P.alpha P.beta S f) (x : Torus P.d)
    (hx : PoleGoodParameterHD data x)
    (normData : OriginNormalizationDataHD data x)
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∀ᶠ r : Real in atTop,
      (Theorem12.Generic.poleCount normData.countingData r : Real) ≤
        2 * (supportMassHD data + epsilon) * r := by
  have hdensity := hx.complexPoleDensity
  have hupper : ∀ᶠ r : Real in atTop,
      (complexOpenPoleCountHD data x r : Real) / (2 * r) <
        supportMassHD data + epsilon :=
    (tendsto_order.1 hdensity).2 _ (by linarith)
  filter_upwards [hupper, eventually_gt_atTop (0 : Real)] with r hratiobound hr
  rw [poleCount_normalized_eq_complexOpenPoleCountHD P data x
    hx.fourierGood normData r hr]
  have hden : 0 < 2 * r := by positivity
  have hmul := (div_lt_iff₀ hden).mp hratiobound
  nlinarith

/- Proof idea: on a clean circle expand the logarithm of the normalized quotient, drop the
nonnegative `nu * log R` term, bound ordinary log by positive log, and integrate. -/
private theorem circleLogMean_normalized_le_posLogMeanHD (P : Params)
    {S : Set (RealVec P.d)} {f : RealVec P.d → Complex}
    (data : PositiveInputDataHD P.alpha P.beta S f) (x : Torus P.d)
    (normData : OriginNormalizationDataHD data x)
    (clean : CleanRadiusDataHD normData.normalizedM) (m : Nat) :
    Theorem12.Generic.circleLogMean normData.normalizedM (clean.R m) ≤
      circlePosLogMeanHD (activeMHD data x) (clean.R m) := by
  let R : Real := clean.R m
  let c : Real → Complex := fun t =>
    (R : Complex) * Complex.exp (Complex.I * (t : Complex))
  have hRone : 1 ≤ R := by
    have hm := (clean.bounds m).1
    have hm0 : (0 : Real) ≤ (m : Real) := Nat.cast_nonneg m
    dsimp only [R]
    linarith
  have hRpos : 0 < R := zero_lt_one.trans_le hRone
  have hc_norm (t : Real) : ‖c t‖ = R := by
    simp [c, abs_of_nonneg hRpos.le]
  have hc_ne (t : Real) : c t ≠ 0 := by
    exact norm_ne_zero_iff.mp (by rw [hc_norm t]; exact hRpos.ne')
  have hc : Continuous c := by
    dsimp only [c]
    fun_prop
  have hnormalized_cont : Continuous (fun t => normData.normalizedM (c t)) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (clean.clean m (c t) (by simpa [R] using hc_norm t)).1.continuousAt.comp
      hc.continuousAt
  have hactive_eq (t : Real) :
      activeMHD data x (c t) = normData.normalizedM (c t) * (c t) ^ normData.nu := by
    exact ((eq_div_iff (pow_ne_zero _ (hc_ne t))).mp
      (normData.normalized_eq (c t) (hc_ne t))).symm
  have hactive_cont : Continuous (fun t => activeMHD data x (c t)) := by
    apply (hnormalized_cont.mul (hc.pow normData.nu)).congr
    intro t
    exact (hactive_eq t).symm
  have hnormalized_ne (t : Real) : normData.normalizedM (c t) ≠ 0 :=
    (clean.clean m (c t) (by simpa [R] using hc_norm t)).2
  have hactive_ne (t : Real) : activeMHD data x (c t) ≠ 0 := by
    rw [hactive_eq t]
    exact mul_ne_zero (hnormalized_ne t) (pow_ne_zero _ (hc_ne t))
  have hnormalized_log_cont :
      Continuous (fun t => Real.log ‖normData.normalizedM (c t)‖) :=
    hnormalized_cont.norm.log (fun t => norm_ne_zero_iff.mpr (hnormalized_ne t))
  have hactive_log_cont : Continuous (fun t => Real.log ‖activeMHD data x (c t)‖) :=
    hactive_cont.norm.log (fun t => norm_ne_zero_iff.mpr (hactive_ne t))
  have hmax_cont : Continuous (fun t => max (Real.log ‖activeMHD data x (c t)‖) 0) :=
    hactive_log_cont.max continuous_const
  have hpointwise (t : Real) :
      Real.log ‖normData.normalizedM (c t)‖ ≤
        max (Real.log ‖activeMHD data x (c t)‖) 0 := by
    have hpow : 1 ≤ ‖(c t) ^ normData.nu‖ := by
      rw [norm_pow, hc_norm]
      exact one_le_pow₀ hRone
    have hnorm : ‖normData.normalizedM (c t)‖ ≤ ‖activeMHD data x (c t)‖ := by
      rw [hactive_eq t, norm_mul]
      nlinarith [norm_nonneg (normData.normalizedM (c t))]
    exact (Real.log_le_log (norm_pos_iff.mpr (hnormalized_ne t)) hnorm).trans
      (le_max_left _ _)
  rw [Theorem12.Generic.circleLogMean, circlePosLogMeanHD]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (by positivity))
  apply setIntegral_mono_on hnormalized_log_cont.integrableOn_Ioc
    hmax_cont.integrableOn_Ioc measurableSet_Ioc
  intro t ht
  simpa [c, R] using hpointwise t

/- Proof idea: choose one normalization and one clean-radius sequence, combine exact zero
and pole densities with the boundary comparison and sublinear error, then apply the
generic Jensen theorem at `(sigma,rho,tau)=(1,supportMassHD data,0)`. -/
private theorem one_le_supportMass_of_nonempty_activeHD (P : Params)
    {S : Set (RealVec P.d)} {f : RealVec P.d → Complex}
    (data : PositiveInputDataHD P.alpha P.beta S f) (x : Torus P.d)
    (hx : PoleGoodParameterHD data x)
    (hactive : Nonempty (ActiveIndexHD data x)) :
    1 ≤ supportMassHD data := by
  let normData : OriginNormalizationDataHD data x :=
    Classical.choice
      (exists_originNormalizationDataHD P data x hx.fourierGood hactive)
  let clean : CleanRadiusDataHD normData.normalizedM :=
    Classical.choice
      (exists_cleanRadiusDataHD normData.countingData normData.analyticAt_zero
        normData.value_zero_ne)
  have hRpos : ∀ m, 0 < clean.R m := by
    intro m
    have hm := (clean.bounds m).1
    have hm0 : (0 : Real) ≤ (m : Real) := Nat.cast_nonneg m
    linarith
  have hb : Tendsto
      (fun m => circlePosLogMeanHD (activeMHD data x) (clean.R m) / clean.R m)
      atTop (nhds 0) :=
    (circlePosLogMeanHD_div_tendsto_zero data x hx.fourierGood.analytic hactive).comp
      clean.tendsto_R
  have hboundary : ∀ᶠ m in atTop,
      Theorem12.Generic.circleLogMean normData.normalizedM (clean.R m) ≤
        2 * (0 : Real) * clean.R m +
          circlePosLogMeanHD (activeMHD data x) (clean.R m) :=
    Filter.Eventually.of_forall fun m => by
      simpa using circleLogMean_normalized_le_posLogMeanHD P data x normData clean m
  have hjensen := jensen_density_comparison
    normData.normalizedM normData.countingData normData.analyticAt_zero
    normData.value_zero_ne clean.R hRpos clean.tendsto_R clean.clean
    1 (supportMassHD data) 0
    (fun m => circlePosLogMeanHD (activeMHD data x) (clean.R m)) hb hboundary
    (fun epsilon hepsilon =>
      normalized_zeroCount_lowerDensity_oneHD P data x hx.fourierGood
        normData epsilon hepsilon)
    (fun epsilon hepsilon =>
      normalized_poleCount_upperDensityHD P data x hx normData epsilon hepsilon)
  simpa using hjensen

/- Proof idea: a hypothetical active element supplies nonemptiness; `one_le_supportMass_of_nonempty_activeHD` gives
`1 ≤ supportMassHD data`, contradicting the explicit strict mass premise. -/
theorem activeIndexHD_isEmpty (P : Params)
    {S : Set (RealVec P.d)} {f : RealVec P.d → Complex}
    (data : PositiveInputDataHD P.alpha P.beta S f) (x : Torus P.d)
    (hmass : supportMassHD data < 1) (hx : PoleGoodParameterHD data x) :
    IsEmpty (ActiveIndexHD data x) := by
  refine ⟨fun a => ?_⟩
  exact (not_le_of_gt hmass)
    (one_le_supportMass_of_nonempty_activeHD P data x hx ⟨a⟩)

end UniversalCompletenessHD.Internal
