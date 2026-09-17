import Theorem14.FourierLaplace
import Theorem12.GenericAuxiliary
import Mathlib.Analysis.Meromorphic.Divisor

/-! # Theorem 1.4: one entire counting witness and clean radii -/

noncomputable section

open Filter MeasureTheory Metric Set
open scoped BigOperators ENNReal Topology

namespace Theorem14.Internal

/- Proof idea: rule out top order globally, use untop₀, and prove zero pole count for one witness. -/
theorem exists_entireCountingData
    {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F Set.univ) (hF0 : F 0 ≠ 0) :
    Nonempty (EntireCountingData F) := by
  /- Proof idea: Convert entire analyticity to `MeromorphicOn univ`; use `F 0 !=0` for finite order at zero and
  the connectedness iff to obtain finite order everywhere; define integer order with `untop₀`
  and prove `order_spec`; obtain finite support on each closed ball from the divisor; transfer
  analytic nonnegativity to integer orders; unfold poleCount and show each negative part is
  zero. -/
  classical
  have hmer : MeromorphicOn F Set.univ := hF.meromorphicOn
  have hzeroFinite : meromorphicOrderAt F 0 ≠ (⊤ : WithTop ℤ) := by
    rw [(hF 0 (Set.mem_univ 0)).meromorphicOrderAt_eq,
      (hF 0 (Set.mem_univ 0)).analyticOrderAt_eq_zero.mpr hF0]
    simp
  have horderFinite : ∀ z : ℂ, meromorphicOrderAt F z ≠ (⊤ : WithTop ℤ) := by
    have hall :=
      (hmer.exists_meromorphicOrderAt_ne_top_iff_forall_mem isConnected_univ).1
        ⟨0, Set.mem_univ 0, hzeroFinite⟩
    exact fun z => hall z (Set.mem_univ z)
  let ord : ℂ → ℤ := fun z => (meromorphicOrderAt F z).untop₀
  have hordSpec (z : ℂ) : ((ord z : ℤ) : WithTop ℤ) = meromorphicOrderAt F z := by
    dsimp only [ord]
    exact WithTop.coe_untop₀_of_ne_top (horderFinite z)
  have hordFinite (R : ℝ) :
      Set.Finite ({z : ℂ | ord z ≠ 0} ∩ Metric.closedBall 0 R) := by
    have hmerBall : MeromorphicOn F (Metric.closedBall (0 : ℂ) R) :=
      fun z _ => hmer z (Set.mem_univ z)
    have hdivFinite :
        (MeromorphicOn.divisor F (Metric.closedBall (0 : ℂ) R)).support.Finite :=
      (MeromorphicOn.divisor F (Metric.closedBall (0 : ℂ) R)).finiteSupport
        (isCompact_closedBall (0 : ℂ) R)
    refine hdivFinite.subset ?_
    rintro z ⟨hzord, hzR⟩
    rw [Function.mem_support, MeromorphicOn.divisor_apply hmerBall hzR]
    exact hzord
  let data : Theorem12.Generic.MeromorphicCountingData F :=
    { meromorphicOn_univ := hmer
      order_ne_top := horderFinite
      order := ord
      order_spec := hordSpec
      finite_orderSupport_closedBall := hordFinite }
  have hordNonneg (z : ℂ) : 0 ≤ data.order z := by
    have htop : (0 : WithTop ℤ) ≤ meromorphicOrderAt F z :=
      (hF z (Set.mem_univ z)).meromorphicOrderAt_nonneg
    rw [← data.order_spec z] at htop
    exact_mod_cast htop
  refine ⟨{ data := data, order_nonneg := hordNonneg, poleCount_eq_zero := ?_ }⟩
  intro R
  rw [Theorem12.Generic.poleCount]
  split_ifs with hR
  · rfl
  · apply Finset.sum_eq_zero
    intro z hz
    simp [Int.toNat_eq_zero.mpr (neg_nonpos.mpr (hordNonneg z))]

/- Proof idea: avoid the finite norm image inside every annulus (j+1,j+2). -/
theorem exists_cleanRadii
    {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F Set.univ)
    (D : EntireCountingData F) :
    Nonempty (CleanRadii F) := by
  /- Proof idea: For each `j`, take the finite nonzero-order support in the ball of radius `j+2`, map it
  through norm, and choose `Rj in (j+1,j+2)` outside the finite image. A boundary zero would
  have positive order and hence belong to that support, contradiction. Use choice to assemble
  the sequence. -/
  classical
  have hchoose (j : ℕ) : ∃ r : ℝ,
      r ∈ Set.Ioo ((j : ℝ) + 1) ((j : ℝ) + 2) ∧
        r ∉ Norm.norm ''
          ({z : ℂ | D.data.order z ≠ 0} ∩ Metric.closedBall 0 ((j : ℝ) + 2)) := by
    let badRadii : Set ℝ := Norm.norm ''
      ({z : ℂ | D.data.order z ≠ 0} ∩ Metric.closedBall 0 ((j : ℝ) + 2))
    have hbadFinite : badRadii.Finite :=
      (D.data.finite_orderSupport_closedBall ((j : ℝ) + 2)).image _
    have hintervalInfinite :
        (Set.Ioo ((j : ℝ) + 1) ((j : ℝ) + 2)).Infinite := by
      apply Set.Ioo_infinite
      linarith
    have hdiffInfinite := hintervalInfinite.sdiff hbadFinite
    exact Set.nonempty_def.mp hdiffInfinite.nonempty
  let radius : ℕ → ℝ := fun j => Classical.choose (hchoose j)
  have hradiusSpec (j : ℕ) :
      radius j ∈ Set.Ioo ((j : ℝ) + 1) ((j : ℝ) + 2) ∧
        radius j ∉ Norm.norm ''
          ({z : ℂ | D.data.order z ≠ 0} ∩ Metric.closedBall 0 ((j : ℝ) + 2)) :=
    Classical.choose_spec (hchoose j)
  refine ⟨{
    radius := radius
    lower := fun j => (hradiusSpec j).1.1
    upper := fun j => (hradiusSpec j).1.2
    clean := ?_
  }⟩
  intro j z hz
  refine ⟨hF z (Set.mem_univ z), ?_⟩
  intro hFz
  have hordNe : D.data.order z ≠ 0 := by
    intro hord
    have hanalyticOrder : analyticOrderAt F z = 0 := by
      rw [← ENat.map_natCast_eq_zero (α := ℤ)]
      rw [← (hF z (Set.mem_univ z)).meromorphicOrderAt_eq,
        ← D.data.order_spec z, hord]
      simp
    exact ((hF z (Set.mem_univ z)).analyticOrderAt_eq_zero.mp hanalyticOrder) hFz
  have hzBall : z ∈ Metric.closedBall (0 : ℂ) ((j : ℝ) + 2) := by
    rw [Metric.mem_closedBall, dist_zero_right, hz]
    exact (hradiusSpec j).1.2.le
  apply (hradiusSpec j).2
  exact ⟨z, ⟨hordNe, hzBall⟩, hz⟩

end Theorem14.Internal
