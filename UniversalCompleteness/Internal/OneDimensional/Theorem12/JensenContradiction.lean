import Theorem12.GenericAuxiliary
import Theorem12.MeromorphicSeries
import Theorem12.FourierZeros
import Theorem12.PoleDensity
import Theorem12.BoundaryGrowth
import Mathlib.Analysis.Meromorphic.IsolatedZeros

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace Theorem12.Internal

/- Proof idea: retain one base divisor, the positive origin order, the removable normalized
extension, one normalized divisor, away-zero order equality, and global pole-multiplicity equality. -/
structure OriginNormalizationData {alpha : ℝ} {beta : ℚ} {S : Set ℝ} {f : ℝ → ℂ}
    (data : PositiveInputData alpha beta S f) (x : AddCircle (1 : ℝ)) where
  nu : ℕ
  nu_pos : 0 < nu
  baseCountingData : Theorem12.Generic.MeromorphicCountingData (activeM data x)
  normalizedM : ℂ → ℂ
  normalized_eq : ∀ z : ℂ, z ≠ 0 → normalizedM z = activeM data x z / z ^ nu
  analyticAt_zero : AnalyticAt ℂ normalizedM 0
  value_zero_ne : normalizedM 0 ≠ 0
  meromorphicOn_univ : MeromorphicOn normalizedM Set.univ
  countingData : Theorem12.Generic.MeromorphicCountingData normalizedM
  order_eq_away_zero : ∀ z : ℂ, z ≠ 0 →
    countingData.order z = baseCountingData.order z
  poleMultiplicity_eq : ∀ z : ℂ,
    Int.toNat (-countingData.order z) = Int.toNat (-baseCountingData.order z)

/- Proof idea: build the base counting datum once, factor the nontrivial analytic zero at the
origin, glue the removable quotient, and prove the normalized divisor invariants. -/
theorem exists_originNormalizationData {alpha : ℝ} {beta : ℚ} {S : Set ℝ} {f : ℝ → ℂ}
    (data : PositiveInputData alpha beta S f) (x : AddCircle (1 : ℝ))
    (hAlpha : Irrational alpha) (hbeta0 : beta ≠ 0)
    (hx : FourierGoodParameter data x)
    (hactive : Nonempty (ActiveIndex data x)) :
    Nonempty (OriginNormalizationData data x) := by
  classical
  let F : ℂ → ℂ := activeM data x
  let base : Theorem12.Generic.MeromorphicCountingData F :=
    Classical.choice (activeM_countingData data x hAlpha hbeta0 hx.analytic hactive)
  have hzeroNotPole : (0 : ℂ) ∉ complexPoleSet data x := by
    rintro ⟨y, ⟨a, rfl⟩, hy⟩
    apply poleCoord_not_int_of_not_sineBad alpha beta x hx.analytic.1
      a.1.1 a.1.2 0
    exact_mod_cast hy
  have hclosedPoleSet : IsClosed (complexPoleSet data x) := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro z hz
    let R : ℝ := ‖z‖ + 1
    have hR : 0 ≤ R := by
      dsimp only [R]
      positivity
    have hzball : z ∈ Metric.ball (0 : ℂ) R := by
      simp [Metric.mem_ball, R]
    let P : Set ℂ := complexPoleSet data x ∩ Metric.closedBall 0 R
    have hPfinite : P.Finite :=
      finite_complexPoleSet_inter_closedBall data x hx.analytic R hR
    have hzP : z ∉ P := fun hzP => hz hzP.1
    have hopen : IsOpen (Metric.ball (0 : ℂ) R \ P) :=
      IsOpen.sdiff Metric.isOpen_ball hPfinite.isClosed
    refine mem_of_superset (hopen.mem_nhds ⟨hzball, hzP⟩) ?_
    intro w hw
    rw [Set.mem_compl_iff]
    intro hwPole
    exact hw.2 ⟨hwPole, Metric.ball_subset_closedBall hw.1⟩
  have hFanalytic : AnalyticAt ℂ F 0 := by
    have hmem : (0 : ℂ) ∈ Set.univ \ complexPoleSet data x :=
      ⟨Set.mem_univ _, hzeroNotPole⟩
    have hopen : IsOpen (Set.univ \ complexPoleSet data x) :=
      IsOpen.sdiff isOpen_univ hclosedPoleSet
    have hwithin := (meromorphicOn_activeM data x hx.analytic).2 (0 : ℂ) hmem
    rw [← analyticWithinAt_univ]
    exact hwithin.mono_of_mem_nhdsWithin (by simpa using hopen.mem_nhds hmem)
  have hFzero : F 0 = 0 := by
    exact activeM_zero data x hx.analytic
  have horderFinite : analyticOrderAt F 0 ≠ ⊤ := by
    intro htop
    apply base.order_ne_top 0
    rw [hFanalytic.meromorphicOrderAt_eq, htop]
    simp
  let nu : ℕ := analyticOrderNatAt F 0
  have horderNeZero : analyticOrderAt F 0 ≠ 0 :=
    hFanalytic.analyticOrderAt_ne_zero.mpr hFzero
  have hnuNe : nu ≠ 0 := by
    intro hnu
    apply horderNeZero
    have hcast : (nu : ℕ∞) = analyticOrderAt F 0 := ENat.coe_toNat horderFinite
    rw [hnu] at hcast
    simpa using hcast.symm
  have hnuPos : 0 < nu := Nat.pos_of_ne_zero hnuNe
  obtain ⟨G, hGanalytic, hGzero, hfactor⟩ :=
    hFanalytic.analyticOrderAt_ne_top.mp horderFinite
  let N : ℂ → ℂ := fun z => if z = 0 then G z else F z / z ^ nu
  have hNeqG : N =ᶠ[nhds (0 : ℂ)] G := by
    filter_upwards [hfactor] with z hzfactor
    by_cases hz : z = 0
    · simp [N, hz]
    · simp only [N, hz, if_false]
      rw [hzfactor]
      simp only [sub_zero, smul_eq_mul]
      dsimp only [nu]
      field_simp
  have hNanalytic : AnalyticAt ℂ N 0 := hGanalytic.congr hNeqG.symm
  have hNzero : N 0 ≠ 0 := by simpa [N] using hGzero
  let Q : ℂ → ℂ := fun z => F z / z ^ nu
  have hQmeromorphic : MeromorphicOn Q Set.univ := by
    apply ((meromorphicOn_activeM data x hx.analytic).1).div
    intro z _
    exact (analyticAt_id.pow nu).meromorphicAt
  have hNeqQ (z : ℂ) : N =ᶠ[nhdsWithin z ({z} : Set ℂ)ᶜ] Q := by
    by_cases hz : z = 0
    · subst z
      filter_upwards [self_mem_nhdsWithin] with w hw
      have hw0 : w ≠ 0 := by simpa using hw
      simp [N, Q, hw0]
    · have hzeroCompl : ({0} : Set ℂ)ᶜ ∈ nhds z :=
        isOpen_compl_singleton.mem_nhds (by simpa using hz)
      have hzeroCompl' : ({0} : Set ℂ)ᶜ ∈ nhdsWithin z ({z} : Set ℂ)ᶜ :=
        Filter.Eventually.filter_mono nhdsWithin_le_nhds hzeroCompl
      filter_upwards [hzeroCompl'] with w hw
      have hw0 : w ≠ 0 := by
        change w ≠ 0 at hw
        exact hw
      simp [N, Q, hw0]
  have hNmeromorphic : MeromorphicOn N Set.univ := by
    intro z _
    exact (hQmeromorphic z (Set.mem_univ z)).congr (hNeqQ z).symm
  have hmerOrderEq (z : ℂ) (hz : z ≠ 0) :
      meromorphicOrderAt N z = meromorphicOrderAt F z := by
    rw [meromorphicOrderAt_congr (hNeqQ z)]
    change meromorphicOrderAt (F / fun w => w ^ nu) z = meromorphicOrderAt F z
    have hpowAnalytic : AnalyticAt ℂ (fun w : ℂ => w ^ nu) z := analyticAt_id.pow nu
    have hFmeromorphic : MeromorphicAt F z :=
      (meromorphicOn_activeM data x hx.analytic).1 z (by simp)
    rw [meromorphicOrderAt_div hFmeromorphic hpowAnalytic.meromorphicAt]
    rw [hpowAnalytic.meromorphicOrderAt_eq,
      (hpowAnalytic.analyticOrderAt_eq_zero).2 (pow_ne_zero nu hz)]
    simp
  let ord : ℂ → ℤ := fun z => if z = 0 then 0 else base.order z
  have hordSpec (z : ℂ) :
      ((ord z : ℤ) : WithTop ℤ) = meromorphicOrderAt N z := by
    by_cases hz : z = 0
    · subst z
      simp only [ord, if_pos]
      rw [hNanalytic.meromorphicOrderAt_eq,
        (hNanalytic.analyticOrderAt_eq_zero).2 hNzero]
      simp
    · simp only [ord, hz, if_false]
      rw [base.order_spec, hmerOrderEq z hz]
  have hordFinite (R : ℝ) :
      Set.Finite ({z : ℂ | ord z ≠ 0} ∩ Metric.closedBall 0 R) := by
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
  have horderAway (z : ℂ) (hz : z ≠ 0) : countData.order z = base.order z := by
    simp [countData, ord, hz]
  have hbaseZeroNonneg : 0 ≤ base.order 0 := by
    have htop : (0 : WithTop ℤ) ≤ meromorphicOrderAt F 0 :=
      hFanalytic.meromorphicOrderAt_nonneg
    rw [← base.order_spec 0] at htop
    exact_mod_cast htop
  have hbaseZeroPoleMultiplicity : Int.toNat (-base.order 0) = 0 :=
    Int.toNat_eq_zero.mpr (neg_nonpos.mpr hbaseZeroNonneg)
  have hpoleMultiplicity (z : ℂ) :
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

/- Proof idea: package one radius in each interval `(m+1,m+2)`, its escape to infinity,
and simultaneous analyticity and nonvanishing on the entire selected circle. -/
structure CleanRadiusData (F : ℂ → ℂ) where
  R : ℕ → ℝ
  bounds : ∀ m : ℕ, (m : ℝ) + 1 < R m ∧ R m < (m : ℝ) + 2
  tendsto_R : Tendsto R atTop atTop
  clean : ∀ m : ℕ, ∀ z : ℂ, ‖z‖ = R m → AnalyticAt ℂ F z ∧ F z ≠ 0

/- Proof idea: avoid the finitely many divisor moduli in each interval `(m+1,m+2)` and use
the interval bounds for positivity and convergence to infinity. -/
theorem exists_cleanRadiusData {F : ℂ → ℂ}
    (countData : Theorem12.Generic.MeromorphicCountingData F)
    (hF0analytic : AnalyticAt ℂ F 0) (hF0 : F 0 ≠ 0) :
    Nonempty (CleanRadiusData F) := by
  let good : Set ℂ := {z | AnalyticAt ℂ F z} ∩ {z | F z ≠ 0}
  have _hzeroGood : (0 : ℂ) ∈ good := ⟨hF0analytic, hF0⟩
  have hneTop : ∀ z ∈ (Set.univ : Set ℂ), meromorphicOrderAt F z ≠ ⊤ := by
    intro z _
    exact countData.order_ne_top z
  have hgoodUniv : good ∈ codiscreteWithin (Set.univ : Set ℂ) := by
    apply Filter.inter_mem
    · exact countData.meromorphicOn_univ.analyticAt_mem_codiscreteWithin
    · exact MeromorphicAt.MeromorphicOn.codiscreteWithin_setOf_ne_zero
        countData.meromorphicOn_univ hneTop
  have hfiniteBad (m : ℕ) :
      (Metric.closedBall (0 : ℂ) ((m : ℝ) + 2) \ good).Finite := by
    apply (isCompact_closedBall (0 : ℂ) ((m : ℝ) + 2)).finite_sdiff_of_mem_codiscreteWithin
    exact (Filter.codiscreteWithin_mono (Set.subset_univ _)) hgoodUniv
  have hchoose (m : ℕ) : ∃ r : ℝ,
      r ∈ Set.Ioo ((m : ℝ) + 1) ((m : ℝ) + 2) ∧
        r ∉ Norm.norm '' (Metric.closedBall (0 : ℂ) ((m : ℝ) + 2) \ good) := by
    let badRadii : Set ℝ := Norm.norm ''
      (Metric.closedBall (0 : ℂ) ((m : ℝ) + 2) \ good)
    have hbadFinite : badRadii.Finite := (hfiniteBad m).image _
    have hintervalInfinite :
        (Set.Ioo ((m : ℝ) + 1) ((m : ℝ) + 2)).Infinite := by
      apply Set.Ioo_infinite
      linarith
    have hdiffInfinite := hintervalInfinite.sdiff hbadFinite
    exact Set.nonempty_def.mp hdiffInfinite.nonempty
  let R : ℕ → ℝ := fun m => Classical.choose (hchoose m)
  have hRspec (m : ℕ) :
      R m ∈ Set.Ioo ((m : ℝ) + 1) ((m : ℝ) + 2) ∧
        R m ∉ Norm.norm '' (Metric.closedBall (0 : ℂ) ((m : ℝ) + 2) \ good) :=
    Classical.choose_spec (hchoose m)
  refine ⟨{
    R := R
    bounds := fun m => (hRspec m).1
    tendsto_R := ?_
    clean := ?_
  }⟩
  · rw [tendsto_atTop_atTop]
    intro b
    obtain ⟨N : ℕ, hN : b < N⟩ := exists_nat_gt b
    refine ⟨N, fun n hn => ?_⟩
    have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hnR : (n : ℝ) + 1 < R n := (hRspec n).1.1
    linarith
  · intro m z hz
    have hzBall : z ∈ Metric.closedBall (0 : ℂ) ((m : ℝ) + 2) := by
      rw [Metric.mem_closedBall, dist_zero_right, hz]
      exact (hRspec m).1.2.le
    have hzGood : z ∈ good := by
      by_contra hzNotGood
      apply (hRspec m).2
      exact ⟨z, ⟨hzBall, hzNotGood⟩, hz⟩
    exact hzGood

/- Proof idea: transfer every nonzero integer zero through normalization, count integers in the
open disk with multiplicity, and absorb the finite loss into the eventual epsilon bound. -/
theorem normalized_zeroCount_lowerDensity_one {alpha : ℝ} {beta : ℚ}
    {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f)
    (x : AddCircle (1 : ℝ)) (hx : FourierGoodParameter data x)
    (normData : OriginNormalizationData data x) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ r : ℝ in atTop,
      2 * (1 - epsilon) * r ≤
        (Theorem12.Generic.zeroCount normData.countingData r : ℝ) := by
  classical
  have hclosedPoleSet : IsClosed (complexPoleSet data x) := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro z hz
    let R : ℝ := ‖z‖ + 1
    have hR : 0 ≤ R := by
      dsimp only [R]
      positivity
    have hzball : z ∈ Metric.ball (0 : ℂ) R := by
      simp [Metric.mem_ball, R]
    let P : Set ℂ := complexPoleSet data x ∩ Metric.closedBall 0 R
    have hPfinite : P.Finite :=
      finite_complexPoleSet_inter_closedBall data x hx.analytic R hR
    have hzP : z ∉ P := fun hzP => hz hzP.1
    have hopen : IsOpen (Metric.ball (0 : ℂ) R \ P) :=
      IsOpen.sdiff Metric.isOpen_ball hPfinite.isClosed
    refine mem_of_superset (hopen.mem_nhds ⟨hzball, hzP⟩) ?_
    intro w hw
    rw [Set.mem_compl_iff]
    intro hwPole
    exact hw.2 ⟨hwPole, Metric.ball_subset_closedBall hw.1⟩
  have hzeroMultiplicity (k : ℤ) (hk : k ≠ 0) :
      1 ≤ Int.toNat (normData.countingData.order (k : ℂ)) := by
    have hkNotPole : (k : ℂ) ∉ complexPoleSet data x := by
      rintro ⟨y, ⟨a, rfl⟩, hy⟩
      apply poleCoord_not_int_of_not_sineBad alpha beta x hx.analytic.1
        a.1.1 a.1.2 k
      exact_mod_cast hy
    have hkMem : (k : ℂ) ∈ Set.univ \ complexPoleSet data x :=
      ⟨Set.mem_univ _, hkNotPole⟩
    have hopen : IsOpen (Set.univ \ complexPoleSet data x) :=
      IsOpen.sdiff isOpen_univ hclosedPoleSet
    have hanWithin := (meromorphicOn_activeM data x hx.analytic).2 (k : ℂ) hkMem
    have han : AnalyticAt ℂ (activeM data x) (k : ℂ) := by
      rw [← analyticWithinAt_univ]
      exact hanWithin.mono_of_mem_nhdsWithin (by simpa using hopen.mem_nhds hkMem)
    have hzero := activeM_int_eq_zero data x hx k
    have hanalyticOrderPos : 0 < analyticOrderAt (activeM data x) (k : ℂ) :=
      pos_iff_ne_zero.mpr (han.analyticOrderAt_ne_zero.mpr hzero)
    have hmerOrderPos : 0 < meromorphicOrderAt (activeM data x) (k : ℂ) := by
      rw [han.meromorphicOrderAt_eq]
      have hcastStrict : StrictMono (fun n : ℕ => (n : ℤ)) := by
        intro a b hab
        change (a : ℤ) < (b : ℤ)
        omega
      simpa using (ENat.strictMono_map_iff.mpr hcastStrict hanalyticOrderPos)
    have hbaseOrderPos : 0 < normData.baseCountingData.order (k : ℂ) := by
      rw [← normData.baseCountingData.order_spec (k : ℂ)] at hmerOrderPos
      exact_mod_cast hmerOrderPos
    rw [normData.order_eq_away_zero (k : ℂ) (by exact_mod_cast hk)]
    omega
  have hcountLower (r : ℝ) (hr : 0 < r) (N : ℕ) (hNr : (N : ℝ) < r) :
      2 * N ≤ Theorem12.Generic.zeroCount normData.countingData r := by
    let intEmbedding : ℤ ↪ ℂ :=
      ⟨fun k => (k : ℂ), fun a b h => by
        have hab : (a : ℝ) = (b : ℝ) := by
          apply Complex.ofReal_injective
          simpa using h
        exact_mod_cast hab⟩
    let K : Finset ℤ := (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase 0
    let Z : Finset ℂ := K.map intEmbedding
    let s : Finset ℂ := (normData.countingData.finite_orderSupport_closedBall r).toFinset
    have hKcard : K.card = 2 * N := by
      dsimp only [K]
      rw [Finset.card_erase_of_mem (by simp)]
      rw [Int.card_Icc]
      have hnonneg : 0 ≤ (N : ℤ) + 1 - (-(N : ℤ)) := by omega
      have htoNat : ((N : ℤ) + 1 - (-(N : ℤ))).toNat = 2 * N + 1 := by
        have hcast :
            ((((N : ℤ) + 1 - (-(N : ℤ))).toNat : ℕ) : ℤ) =
              (((2 * N + 1 : ℕ) : ℕ) : ℤ) := by
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
      have hkIcc : k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) :=
        (Finset.mem_erase.mp hkK).2
      have hk0 : k ≠ 0 := by
        exact fun h => (Finset.mem_erase.mp hkK).1 h
      have hmult := hzeroMultiplicity k hk0
      apply (Set.Finite.mem_toFinset _).mpr
      refine ⟨?_, ?_⟩
      · intro horder
        change normData.countingData.order (k : ℂ) = 0 at horder
        rw [horder] at hmult
        norm_num at hmult
      · rw [Metric.mem_closedBall, dist_zero_right]
        have hkabs : |k| ≤ (N : ℤ) := (abs_le).2 (by simpa using hkIcc)
        have hknorm : ‖(k : ℂ)‖ ≤ (N : ℝ) := by
          simpa using (show (|k| : ℝ) ≤ (N : ℝ) by exact_mod_cast hkabs)
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
        have hkabs : |k| ≤ (N : ℤ) := (abs_le).2 (by simpa using hkIcc)
        have hknorm : ‖(k : ℂ)‖ ≤ (N : ℝ) := by
          simpa using (show (|k| : ℝ) ≤ (N : ℝ) by exact_mod_cast hkabs)
        exact hknorm.trans_lt hNr
      _ ≤ ∑ z ∈ s,
          if ‖z‖ < r then Int.toNat (normData.countingData.order z) else 0 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hZsub
        intro z hz hzZ
        exact Nat.zero_le _
  by_cases hepsilonLarge : 1 ≤ epsilon
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    have : 2 * (1 - epsilon) * r ≤ 0 := by
      nlinarith
    exact this.trans (Nat.cast_nonneg _)
  · have hthreshold : ∀ᶠ r : ℝ in atTop, max 3 (2 / epsilon) ≤ r :=
      eventually_ge_atTop _
    filter_upwards [hthreshold] with r hr
    have hr3 : 3 ≤ r := (le_max_left _ _).trans hr
    have hrpos : 0 < r := by linarith
    let N : ℕ := ⌊r⌋₊ - 1
    have hfloorTwo : 2 ≤ ⌊r⌋₊ := by
      have h2r : (2 : ℝ) ≤ r := by linarith
      exact Nat.le_floor h2r
    have hNr : (N : ℝ) < r := by
      dsimp only [N]
      rw [Nat.cast_sub (by omega : 1 ≤ ⌊r⌋₊), Nat.cast_one]
      linarith [Nat.floor_le hrpos.le]
    have hNlower : r - 2 < (N : ℝ) := by
      dsimp only [N]
      rw [Nat.cast_sub (by omega : 1 ≤ ⌊r⌋₊), Nat.cast_one]
      linarith [Nat.sub_one_lt_floor r]
    have hepsr : 2 ≤ epsilon * r := by
      have hdiv := (le_max_right (3 : ℝ) (2 / epsilon)).trans hr
      simpa [mul_comm] using (div_le_iff₀ hepsilon).mp hdiv
    have htarget : (1 - epsilon) * r ≤ (N : ℝ) := by
      nlinarith
    have hcount := hcountLower r hrpos N hNr
    calc
      2 * (1 - epsilon) * r = 2 * ((1 - epsilon) * r) := by ring
      _ ≤ 2 * (N : ℝ) := mul_le_mul_of_nonneg_left htarget (by norm_num)
      _ ≤ (Theorem12.Generic.zeroCount normData.countingData r : ℝ) := by
        exact_mod_cast hcount

/- Proof idea: transfer pole multiplicities to the base divisor and use exact simple active poles
and absence of all other poles to identify the finite open-disk sums. -/
theorem poleCount_normalized_eq_complexOpenPoleCount {alpha : ℝ} {beta : ℚ}
    {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f)
    (x : AddCircle (1 : ℝ)) (hAlpha : Irrational alpha) (hbeta0 : beta ≠ 0)
    (hx : FourierGoodParameter data x) (normData : OriginNormalizationData data x)
    (r : ℝ) (hr : 0 < r) :
    Theorem12.Generic.poleCount normData.countingData r = complexOpenPoleCount data x r := by
  classical
  let P : Set ℂ := complexPoleSet data x ∩ Metric.ball 0 r
  let s : Finset ℂ := (normData.countingData.finite_orderSupport_closedBall r).toFinset
  have hbaseMult (z : ℂ) :
      Int.toNat (-normData.baseCountingData.order z) =
        if z ∈ complexPoleSet data x then 1 else 0 := by
    by_cases hz : z ∈ complexPoleSet data x
    · rw [if_pos hz]
      rcases hz with ⟨y, ⟨a, rfl⟩, rfl⟩
      have hord := normData.baseCountingData.order_spec
        (poleCoord alpha beta x a.1.1 a.1.2 : ℂ)
      rw [meromorphicOrderAt_activeM_pole data x hAlpha hbeta0 hx.analytic a] at hord
      have hordInt : normData.baseCountingData.order
          (poleCoord alpha beta x a.1.1 a.1.2 : ℂ) = -1 := by
        have hord' :
            ((normData.baseCountingData.order
                (poleCoord alpha beta x a.1.1 a.1.2 : ℂ) : ℤ) : WithTop ℤ) =
              (((-1 : ℤ) : ℤ) : WithTop ℤ) := by
          simpa using hord
        exact WithTop.coe_eq_coe.mp hord'
      simp [hordInt]
    · rw [if_neg hz]
      have horderNonnegTop : (0 : WithTop ℤ) ≤
          ((normData.baseCountingData.order z : ℤ) : WithTop ℤ) := by
        rw [normData.baseCountingData.order_spec z]
        exact le_of_not_gt ((activeM_hasPoleAt_iff data x hAlpha hbeta0 hx.analytic z).not.mpr hz)
      have horderNonneg : 0 ≤ normData.baseCountingData.order z := by
        exact_mod_cast horderNonnegTop
      exact Int.toNat_eq_zero.mpr (neg_nonpos.mpr horderNonneg)
  have hmult (z : ℂ) :
      Int.toNat (-normData.countingData.order z) =
        if z ∈ complexPoleSet data x then 1 else 0 := by
    rw [normData.poleMultiplicity_eq z]
    exact hbaseMult z
  have hPfinite : P.Finite := by
    apply (finite_complexPoleSet_inter_closedBall data x hx.analytic r hr.le).subset
    intro z hz
    exact ⟨hz.1, Metric.ball_subset_closedBall hz.2⟩
  have hPsub : hPfinite.toFinset ⊆ s := by
    intro z hz
    have hzP : z ∈ P := (Set.Finite.mem_toFinset hPfinite).mp hz
    apply (Set.Finite.mem_toFinset _).mpr
    refine ⟨?_, Metric.ball_subset_closedBall hzP.2⟩
    intro horder
    have hm := hmult z
    rw [horder] at hm
    simp [hzP.1] at hm
  rw [Theorem12.Generic.poleCount, if_neg (not_le.mpr hr), complexOpenPoleCount]
  rw [Set.ncard_eq_toFinset_card P hPfinite]
  change (∑ z ∈ s,
      if ‖z‖ < r then Int.toNat (-normData.countingData.order z) else 0) =
    hPfinite.toFinset.card
  calc
    (∑ z ∈ s,
        if ‖z‖ < r then Int.toNat (-normData.countingData.order z) else 0) =
        ∑ z ∈ s, if z ∈ hPfinite.toFinset then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [hmult z]
      by_cases hpole : z ∈ complexPoleSet data x <;>
        by_cases hzr : ‖z‖ < r <;> simp [P, hpole, hzr]
    _ = hPfinite.toFinset.card := by
      rw [← Finset.sum_filter]
      simp only [Finset.filter_mem_eq_inter]
      rw [Finset.inter_eq_right.mpr hPsub]
      simp

/- Proof idea: rewrite normalized divisor poles as complex open poles and use their all-real-radius
density limit to obtain the eventual `supportMass + epsilon` upper bound. -/
theorem normalized_poleCount_upperDensity {alpha : ℝ} {beta : ℚ} {S : Set ℝ}
    {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f) (x : AddCircle (1 : ℝ))
    (hAlpha : Irrational alpha) (hbeta0 : beta ≠ 0) (hx : PoleGoodParameter data x)
    (normData : OriginNormalizationData data x) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ r : ℝ in atTop,
      (Theorem12.Generic.poleCount normData.countingData r : ℝ) ≤
        2 * (supportMass data + epsilon) * r := by
  have hdensity := complexOpenPoleCount_density data x hx.fourierGood.analytic hx.poleDensity
  have hupper : ∀ᶠ r : ℝ in atTop,
      (complexOpenPoleCount data x r : ℝ) / (2 * r) < supportMass data + epsilon :=
    (tendsto_order.1 hdensity).2 _ (by linarith)
  filter_upwards [hupper, eventually_gt_atTop (0 : ℝ)] with r hratiobound hr
  rw [poleCount_normalized_eq_complexOpenPoleCount data x hAlpha hbeta0
    hx.fourierGood normData r hr]
  have hden : 0 < 2 * r := by positivity
  have hmul := (div_lt_iff₀ hden).mp hratiobound
  nlinarith

/- Proof idea: on a clean positive circle expand the logarithm of the quotient, drop the
nonnegative `nu * log R` term, and bound ordinary log by positive log before integrating. -/
theorem circleLogMean_normalized_le_posLogMean {alpha : ℝ} {beta : ℚ} {S : Set ℝ}
    {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f) (x : AddCircle (1 : ℝ))
    (normData : OriginNormalizationData data x)
    (clean : CleanRadiusData normData.normalizedM) (m : ℕ) :
    Theorem12.Generic.circleLogMean normData.normalizedM (clean.R m) ≤
      circlePosLogMean (activeM data x) (clean.R m) := by
  let R : ℝ := clean.R m
  let c : ℝ → ℂ := fun t => (R : ℂ) * Complex.exp (Complex.I * (t : ℂ))
  have hRone : 1 ≤ R := by
    have hm := (clean.bounds m).1
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    dsimp only [R]
    linarith
  have hRpos : 0 < R := zero_lt_one.trans_le hRone
  have hc_norm (t : ℝ) : ‖c t‖ = R := by
    simp [c, abs_of_nonneg hRpos.le]
  have hc_ne (t : ℝ) : c t ≠ 0 := by
    exact norm_ne_zero_iff.mp (by rw [hc_norm t]; exact hRpos.ne')
  have hc : Continuous c := by
    dsimp only [c]
    fun_prop
  have hnormalized_cont : Continuous (fun t => normData.normalizedM (c t)) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (clean.clean m (c t) (by simpa [R] using hc_norm t)).1.continuousAt.comp
      hc.continuousAt
  have hactive_eq (t : ℝ) :
      activeM data x (c t) = normData.normalizedM (c t) * (c t) ^ normData.nu := by
    exact ((eq_div_iff (pow_ne_zero _ (hc_ne t))).mp
      (normData.normalized_eq (c t) (hc_ne t))).symm
  have hactive_cont : Continuous (fun t => activeM data x (c t)) := by
    apply (hnormalized_cont.mul (hc.pow normData.nu)).congr
    intro t
    exact (hactive_eq t).symm
  have hnormalized_ne (t : ℝ) : normData.normalizedM (c t) ≠ 0 :=
    (clean.clean m (c t) (by simpa [R] using hc_norm t)).2
  have hactive_ne (t : ℝ) : activeM data x (c t) ≠ 0 := by
    rw [hactive_eq t]
    exact mul_ne_zero (hnormalized_ne t) (pow_ne_zero _ (hc_ne t))
  have hnormalized_log_cont :
      Continuous (fun t => Real.log ‖normData.normalizedM (c t)‖) :=
    hnormalized_cont.norm.log (fun t => norm_ne_zero_iff.mpr (hnormalized_ne t))
  have hactive_log_cont : Continuous (fun t => Real.log ‖activeM data x (c t)‖) :=
    hactive_cont.norm.log (fun t => norm_ne_zero_iff.mpr (hactive_ne t))
  have hmax_cont : Continuous (fun t => max (Real.log ‖activeM data x (c t)‖) 0) :=
    hactive_log_cont.max continuous_const
  have hpointwise (t : ℝ) :
      Real.log ‖normData.normalizedM (c t)‖ ≤
        max (Real.log ‖activeM data x (c t)‖) 0 := by
    have hpow : 1 ≤ ‖(c t) ^ normData.nu‖ := by
      rw [norm_pow, hc_norm]
      exact one_le_pow₀ hRone
    have hnorm : ‖normData.normalizedM (c t)‖ ≤ ‖activeM data x (c t)‖ := by
      rw [hactive_eq t, norm_mul]
      nlinarith [norm_nonneg (normData.normalizedM (c t))]
    exact (Real.log_le_log (norm_pos_iff.mpr (hnormalized_ne t)) hnorm).trans
      (le_max_left _ _)
  rw [Theorem12.Generic.circleLogMean, circlePosLogMean]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (by positivity))
  apply setIntegral_mono_on hnormalized_log_cont.integrableOn_Ioc
    hmax_cont.integrableOn_Ioc measurableSet_Ioc
  intro t ht
  simpa [c, R] using hpointwise t

/- Proof idea: construct one normalization and one clean-radius sequence, feed the exact zero,
pole, boundary, and sublinear-error bounds to Jensen at `(1,supportMass,0)`. -/
theorem one_le_supportMass_of_nonempty_active {alpha : ℝ} {beta : ℚ} {S : Set ℝ}
    {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f) (x : AddCircle (1 : ℝ))
    (hAlpha : Irrational alpha) (hbeta0 : beta ≠ 0)
    (hx : PoleGoodParameter data x) (hactive : Nonempty (ActiveIndex data x)) :
    1 ≤ supportMass data := by
  let normData : OriginNormalizationData data x :=
    Classical.choice
      (exists_originNormalizationData data x hAlpha hbeta0 hx.fourierGood hactive)
  let clean : CleanRadiusData normData.normalizedM :=
    Classical.choice
      (exists_cleanRadiusData normData.countingData normData.analyticAt_zero
        normData.value_zero_ne)
  have hRpos : ∀ m, 0 < clean.R m := by
    intro m
    have hm := (clean.bounds m).1
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hb : Tendsto
      (fun m => circlePosLogMean (activeM data x) (clean.R m) / clean.R m)
      atTop (nhds 0) :=
    (circlePosLogMean_div_tendsto_zero data x hx.fourierGood.analytic hactive).comp
      clean.tendsto_R
  have hboundary : ∀ᶠ m in atTop,
      Theorem12.Generic.circleLogMean normData.normalizedM (clean.R m) ≤
        2 * (0 : ℝ) * clean.R m + circlePosLogMean (activeM data x) (clean.R m) :=
    Filter.Eventually.of_forall fun m => by
      simpa using circleLogMean_normalized_le_posLogMean data x normData clean m
  have hjensen := Theorem12.Generic.jensen_density_comparison
    normData.normalizedM normData.countingData normData.analyticAt_zero
    normData.value_zero_ne clean.R hRpos clean.tendsto_R clean.clean
    1 (supportMass data) 0
    (fun m => circlePosLogMean (activeM data x) (clean.R m)) hb hboundary
    (fun epsilon hepsilon =>
      normalized_zeroCount_lowerDensity_one data x hx.fourierGood normData epsilon hepsilon)
    (fun epsilon hepsilon =>
      normalized_poleCount_upperDensity data x hAlpha hbeta0 hx normData epsilon hepsilon)
  simpa using hjensen

/- Proof idea: if the active subtype were nonempty, the Jensen comparison would give
`1 ≤ supportMass`, contradicting its strict upper bound from `volume S < 1`. -/
theorem activeIndex_isEmpty {alpha : ℝ} {beta : ℚ} {S : Set ℝ} {f : ℝ → ℂ}
    (data : PositiveInputData alpha beta S f) (x : AddCircle (1 : ℝ))
    (hAlpha : Irrational alpha) (hbeta0 : beta ≠ 0) (hSlt : volume S < 1)
    (hx : PoleGoodParameter data x) : IsEmpty (ActiveIndex data x) := by
  refine ⟨fun a => ?_⟩
  exact (not_le_of_gt (supportMass_mem_Ico data hSlt).2)
    (one_le_supportMass_of_nonempty_active data x hAlpha hbeta0 hx ⟨a⟩)

end Theorem12.Internal
