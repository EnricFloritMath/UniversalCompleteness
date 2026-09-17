import SpectralGapsPrelim.BirkhoffPointwise.Conventions

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Topology ENNReal

namespace SpectralGapsPrelim.BirkhoffPointwise

variable {X : Type*} [MeasurableSpace X]
variable {μ : Measure X} {τ : X → X}

omit [MeasurableSpace X] in
private lemma partialSum_succ
    (g : X → ℝ) (n : ℕ) (x : X) :
    partialSum τ g (n + 1) x =
      g x + partialSum τ g n (τ x) := by
  calc
    partialSum τ g (n + 1) x
        = (∑ q ∈ Finset.range n, g (τ^[q + 1] x)) + g x := by
            simp [partialSum, Finset.sum_range_succ']
    _ = (∑ q ∈ Finset.range n, g (τ^[q] (τ x))) + g x := by
            simp [Function.iterate_succ_apply]
    _ = g x + partialSum τ g n (τ x) := by
            simp [partialSum, add_comm]

private lemma stronglyMeasurable_finset_sup'
    {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    {f : ι → X → ℝ}
    (hf : ∀ i ∈ s, StronglyMeasurable (f i)) :
    StronglyMeasurable (fun x => s.sup' hs (fun i => f i x)) := by
  classical
  refine hs.cons_induction (motive := fun s hs =>
      (∀ i ∈ s, StronglyMeasurable (f i)) →
        StronglyMeasurable (fun x => s.sup' hs (fun i => f i x))) ?_ ?_ hf
  · intro a hf
    simpa using hf a (by simp)
  · intro a s ha hs ih hf
    have hfa : StronglyMeasurable (f a) := hf a (by simp [ha])
    have hfs : ∀ i ∈ s, StronglyMeasurable (f i) := by
      intro i hi
      exact hf i (by simp [hi])
    have hih : StronglyMeasurable (fun x => s.sup' hs (fun i => f i x)) :=
      ih hfs
    have hmax :
        StronglyMeasurable
          (fun x => max (f a x) (s.sup' hs (fun i => f i x))) :=
      ((hfa.measurable).max hih.measurable).stronglyMeasurable
    convert hmax using 1
    ext x
    simpa using
      (Finset.sup'_cons (H := hs) (f := fun i => f i x)
        (b := a) (hb := ha))

private lemma integrable_max
    {f h : X → ℝ} (hf : Integrable f μ) (hh : Integrable h μ) :
    Integrable (fun x => max (f x) (h x)) μ := by
  have hpos : Integrable (fun x => max (h x - f x) 0) μ :=
    (hh.sub hf).pos_part
  refine (hf.add hpos).congr ?_
  filter_upwards with x
  by_cases hx : h x ≤ f x
  · have hsub : h x - f x ≤ 0 := sub_nonpos.mpr hx
    calc
      f x + max (h x - f x) 0 = f x := by simp [max_eq_right hsub]
      _ = max (f x) (h x) := (max_eq_left hx).symm
  · have hx' : f x ≤ h x := le_of_lt (lt_of_not_ge hx)
    have hsub : 0 ≤ h x - f x := sub_nonneg.mpr hx'
    calc
      f x + max (h x - f x) 0 = h x := by
        rw [max_eq_left hsub]
        ring
      _ = max (f x) (h x) := (max_eq_right hx').symm

private lemma integrable_finset_sup'
    {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    {f : ι → X → ℝ}
    (hf : ∀ i ∈ s, Integrable (f i) μ) :
    Integrable (fun x => s.sup' hs (fun i => f i x)) μ := by
  classical
  refine hs.cons_induction (motive := fun s hs =>
      (∀ i ∈ s, Integrable (f i) μ) →
        Integrable (fun x => s.sup' hs (fun i => f i x)) μ) ?_ ?_ hf
  · intro a hf
    simpa using hf a (by simp)
  · intro a s ha hs ih hf
    have hfa : Integrable (f a) μ := hf a (by simp [ha])
    have hfs : ∀ i ∈ s, Integrable (f i) μ := by
      intro i hi
      exact hf i (by simp [hi])
    have hih : Integrable (fun x => s.sup' hs (fun i => f i x)) μ :=
      ih hfs
    have hmax :
        Integrable
          (fun x => max (f a x) (s.sup' hs (fun i => f i x))) μ :=
      integrable_max hfa hih
    convert hmax using 1
    ext x
    simpa using
      (Finset.sup'_cons (H := hs) (f := fun i => f i x)
        (b := a) (hb := ha))

omit [MeasurableSpace X] in
private lemma mem_finitePositiveMaxSet_iff_pos_finiteMaxFunction
    (g : X → ℝ) (K : ℕ) (x : X) :
    x ∈ finitePositiveMaxSet τ g K ↔
      0 < finiteMaxFunction τ g K x := by
  constructor
  · rintro ⟨n, hn_pos, hn_le, hn_sum⟩
    have hn_mem : n ∈ Finset.range (K + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le hn_le)
    have hle :
        partialSum τ g n x ≤ finiteMaxFunction τ g K x := by
      simpa [finiteMaxFunction] using
        (Finset.le_sup' (s := Finset.range (K + 1))
          (f := fun n => partialSum τ g n x) hn_mem)
    exact hn_sum.trans_le hle
  · intro hmax_pos
    have hmax_pos' :
        0 <
          (Finset.range (K + 1)).sup' (by simp)
            (fun n => partialSum τ g n x) := by
      simpa [finiteMaxFunction] using hmax_pos
    let H : (Finset.range (K + 1)).Nonempty := by simp
    rcases (Finset.lt_sup'_iff
        (H := H)
        (f := fun n => partialSum τ g n x) (a := 0)).1 hmax_pos' with
      ⟨n, hn_mem, hn_sum⟩
    have hn_le : n ≤ K := Nat.le_of_lt_succ (Finset.mem_range.mp hn_mem)
    have hn_pos : 0 < n := by
      by_contra hn_nonpos
      have hn_zero : n = 0 := Nat.eq_zero_of_not_pos hn_nonpos
      subst n
      simp [partialSum] at hn_sum
    exact ⟨n, hn_pos, hn_le, hn_sum⟩

private lemma partialSum_stronglyMeasurable
    (hτ_mp : MeasurePreserving τ μ μ)
    {g : X → ℝ} (hg : StronglyMeasurable g) (n : ℕ) :
    StronglyMeasurable (fun x => partialSum τ g n x) := by
  -- Proof idea: finite sum of strongly measurable iterates.
  change StronglyMeasurable
    (fun x => ∑ q ∈ Finset.range n, g (τ^[q] x))
  exact Finset.stronglyMeasurable_fun_sum (Finset.range n) (fun q _ =>
    hg.comp_measurable (MeasurePreserving.iterate hτ_mp q).measurable)

private lemma partialSum_integrable
    (hτ_mp : MeasurePreserving τ μ μ)
    {g : X → ℝ} (hg : Integrable g μ) (n : ℕ) :
    Integrable (fun x => partialSum τ g n x) μ := by
  -- Proof idea: finite sum of integrable iterates.
  change Integrable
    (fun x => ∑ q ∈ Finset.range n, g (τ^[q] x)) μ
  exact MeasureTheory.integrable_finsetSum (Finset.range n) (fun q _ =>
    integrable_comp_iterate_measurePreserving hτ_mp hg q)

private lemma finitePositiveMaxSet_measurable
    (hτ_mp : MeasurePreserving τ μ μ)
    {g : X → ℝ} (hg : StronglyMeasurable g) (K : ℕ) :
    MeasurableSet (finitePositiveMaxSet τ g K) := by
  -- Proof idea: finite union over `n ≤ K` of strict superlevel sets.
  rw [finitePositiveMaxSet]
  simp only [Set.setOf_exists]
  refine MeasurableSet.iUnion fun n : ℕ => ?_
  simpa [Set.setOf_and, Set.inter_assoc] using
      (MeasurableSet.const (0 < n)).inter
        ((MeasurableSet.const (n ≤ K)).inter
          (measurableSet_lt measurable_const
            (partialSum_stronglyMeasurable hτ_mp hg n).measurable))

omit [MeasurableSpace X] in
private lemma finiteMaxFunction_nonneg
    (g : X → ℝ) (K : ℕ) (x : X) :
    0 ≤ finiteMaxFunction τ g K x := by
  -- Proof idea: `partialSum τ g 0 x = 0` is included in the finite maximum.
  have h0 : 0 ∈ Finset.range (K + 1) := by simp
  have hle :
      partialSum τ g 0 x ≤ finiteMaxFunction τ g K x := by
    simpa [finiteMaxFunction] using
      (Finset.le_sup' (s := Finset.range (K + 1))
        (f := fun n => partialSum τ g n x) h0)
  simpa [partialSum] using hle

private lemma finiteMaxFunction_stronglyMeasurable
    (hτ_mp : MeasurePreserving τ μ μ)
    {g : X → ℝ} (hg : StronglyMeasurable g) (K : ℕ) :
    StronglyMeasurable (fun x => finiteMaxFunction τ g K x) := by
  -- Proof idea: repeated finite `max` of strongly measurable partial sums.
  simpa [finiteMaxFunction] using
    (stronglyMeasurable_finset_sup'
      (s := Finset.range (K + 1)) (by simp)
      (f := fun n x => partialSum τ g n x)
      (fun n _ => partialSum_stronglyMeasurable hτ_mp hg n))

private lemma finiteMaxFunction_integrable
    (hτ_mp : MeasurePreserving τ μ μ)
    {g : X → ℝ} (_hg_meas : StronglyMeasurable g)
    (hg_int : Integrable g μ) (K : ℕ) :
    Integrable (fun x => finiteMaxFunction τ g K x) μ := by
  -- Proof idea: use `partialSum_integrable` and integrability of finite maxima.
  simpa [finiteMaxFunction] using
    (integrable_finset_sup'
      (μ := μ) (s := Finset.range (K + 1)) (by simp)
      (f := fun n x => partialSum τ g n x)
      (fun n _ => partialSum_integrable hτ_mp hg_int n))

omit [MeasurableSpace X] in
private lemma finiteMaxFunction_succ
    (g : X → ℝ) (K : ℕ) (x : X) :
    finiteMaxFunction τ g (K + 1) x =
      max 0 (g x + finiteMaxFunction τ g K (τ x)) := by
  -- Proof idea: finite-sum recursion behind Hopf's lemma.
  apply le_antisymm
  · unfold finiteMaxFunction
    refine Finset.sup'_le _ _ ?_
    intro n hn
    have hn_le : n ≤ K + 1 :=
      Nat.le_of_lt_succ (Finset.mem_range.mp hn)
    rcases n with _ | m
    · simp [partialSum]
    · have hm_le : m ≤ K := Nat.succ_le_succ_iff.mp hn_le
      have hm_mem : m ∈ Finset.range (K + 1) :=
        Finset.mem_range.mpr (Nat.lt_succ_of_le hm_le)
      have hm_bound :
          partialSum τ g m (τ x) ≤ finiteMaxFunction τ g K (τ x) := by
        simpa [finiteMaxFunction] using
          (Finset.le_sup' (s := Finset.range (K + 1))
            (f := fun n => partialSum τ g n (τ x)) hm_mem)
      calc
        partialSum τ g (m + 1) x
            = g x + partialSum τ g m (τ x) := partialSum_succ g m x
        _ ≤ g x + finiteMaxFunction τ g K (τ x) :=
            add_le_add_right hm_bound _
        _ ≤ max 0 (g x + finiteMaxFunction τ g K (τ x)) :=
            le_max_right _ _
  · refine max_le ?_ ?_
    · exact finiteMaxFunction_nonneg g (K + 1) x
    · have hsup_le :
          finiteMaxFunction τ g K (τ x) ≤
            finiteMaxFunction τ g (K + 1) x - g x := by
        unfold finiteMaxFunction
        refine Finset.sup'_le _ _ ?_
        intro m hm
        have hm_le : m ≤ K :=
          Nat.le_of_lt_succ (Finset.mem_range.mp hm)
        have hsucc_mem : m + 1 ∈ Finset.range ((K + 1) + 1) :=
          Finset.mem_range.mpr
            (Nat.succ_lt_succ (Nat.lt_succ_of_le hm_le))
        have hle :
            partialSum τ g (m + 1) x ≤
              (Finset.range ((K + 1) + 1)).sup' (by simp)
                (fun n => partialSum τ g n x) :=
          Finset.le_sup' (s := Finset.range ((K + 1) + 1))
            (f := fun n => partialSum τ g n x) hsucc_mem
        have hle' :
            g x + partialSum τ g m (τ x) ≤
              (Finset.range ((K + 1) + 1)).sup' (by simp)
                (fun n => partialSum τ g n x) := by
          simpa [partialSum_succ g m x] using hle
        linarith
      linarith

omit [MeasurableSpace X] in
private lemma finiteMaxFunction_mono_succ
    (g : X → ℝ) (K : ℕ) (x : X) :
    finiteMaxFunction τ g K x ≤ finiteMaxFunction τ g (K + 1) x := by
  -- Proof idea: inclusion of `range (K+1)` into `range (K+2)`.
  unfold finiteMaxFunction
  refine Finset.sup'_le _ _ ?_
  intro n hn
  have hn' : n ∈ Finset.range ((K + 1) + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp hn))
  exact Finset.le_sup' (s := Finset.range ((K + 1) + 1))
    (f := fun n => partialSum τ g n x) hn'

omit [MeasurableSpace X] in
private lemma indicator_mul_ge_max_sub_shift_succ
    (g : X → ℝ) (K : ℕ) (x : X) :
    (finitePositiveMaxSet τ g (K + 1)).indicator g x
      ≥ finiteMaxFunction τ g (K + 1) x
           - finiteMaxFunction τ g K (τ x) := by
  -- Proof idea: split on membership in the successor positive-maximal set and
  -- use `finiteMaxFunction_succ`.
  by_cases hx : x ∈ finitePositiveMaxSet τ g (K + 1)
  · have hpos :
        0 < finiteMaxFunction τ g (K + 1) x :=
      (mem_finitePositiveMaxSet_iff_pos_finiteMaxFunction g (K + 1) x).1 hx
    have hpos_sum :
        0 < g x + finiteMaxFunction τ g K (τ x) := by
      rw [finiteMaxFunction_succ g K x] at hpos
      by_contra hnonpos
      have hle : g x + finiteMaxFunction τ g K (τ x) ≤ 0 :=
        le_of_not_gt hnonpos
      rw [max_eq_left hle] at hpos
      exact (lt_irrefl (0 : ℝ)) hpos
    rw [Set.indicator_of_mem hx, finiteMaxFunction_succ g K x,
      max_eq_right hpos_sum.le]
    linarith
  · have hnotpos :
        ¬ 0 < finiteMaxFunction τ g (K + 1) x := by
      intro hpos
      exact hx
        ((mem_finitePositiveMaxSet_iff_pos_finiteMaxFunction g (K + 1) x).2 hpos)
    have hzero : finiteMaxFunction τ g (K + 1) x = 0 :=
      le_antisymm (not_lt.mp hnotpos) (finiteMaxFunction_nonneg g (K + 1) x)
    have hprev_nonneg : 0 ≤ finiteMaxFunction τ g K (τ x) :=
      finiteMaxFunction_nonneg g K (τ x)
    rw [Set.indicator_of_notMem hx, hzero]
    linarith

private lemma indicator_finitePositiveMaxSet_integrable
    (hτ_mp : MeasurePreserving τ μ μ)
    {g : X → ℝ} (hg_meas : StronglyMeasurable g)
    (hg_int : Integrable g μ) (K : ℕ) :
    Integrable ((finitePositiveMaxSet τ g K).indicator g) μ := by
  -- Proof idea: measurable set plus `hg_int.indicator`.
  exact hg_int.indicator (finitePositiveMaxSet_measurable hτ_mp hg_meas K)

private lemma integral_indicator_finitePositiveMaxSet_eq_setIntegral
    (hτ_mp : MeasurePreserving τ μ μ)
    {g : X → ℝ} (hg_meas : StronglyMeasurable g)
    (_hg_int : Integrable g μ) (K : ℕ) :
    ∫ x, (finitePositiveMaxSet τ g K).indicator g x ∂μ
      =
    ∫ x in finitePositiveMaxSet τ g K, g x ∂μ := by
  -- Proof idea: standard set-integral/indicator rewrite.
  exact MeasureTheory.integral_indicator
    (finitePositiveMaxSet_measurable hτ_mp hg_meas K)

private lemma integral_indicator_ge_max_sub_shift_succ
    (hτ_mp : MeasurePreserving τ μ μ)
    {g : X → ℝ} (hg_meas : StronglyMeasurable g)
    (hg_int : Integrable g μ) (K : ℕ) :
    ∫ x, finiteMaxFunction τ g (K + 1) x ∂μ
      - ∫ x, finiteMaxFunction τ g K (τ x) ∂μ
      ≤
    ∫ x, (finitePositiveMaxSet τ g (K + 1)).indicator g x ∂μ := by
  -- Proof idea: integrate `indicator_mul_ge_max_sub_shift_succ`.
  have hmax_succ :
      Integrable (fun x => finiteMaxFunction τ g (K + 1) x) μ :=
    finiteMaxFunction_integrable hτ_mp hg_meas hg_int (K + 1)
  have hmax_shift :
      Integrable (fun x => finiteMaxFunction τ g K (τ x)) μ :=
    integrable_comp_measurePreserving hτ_mp
      (finiteMaxFunction_integrable hτ_mp hg_meas hg_int K)
  have hsub :
      Integrable
        (fun x =>
          finiteMaxFunction τ g (K + 1) x -
            finiteMaxFunction τ g K (τ x)) μ :=
    hmax_succ.sub hmax_shift
  have hind :
      Integrable ((finitePositiveMaxSet τ g (K + 1)).indicator g) μ :=
    indicator_finitePositiveMaxSet_integrable hτ_mp hg_meas hg_int (K + 1)
  have hle :
      ∫ x,
          finiteMaxFunction τ g (K + 1) x -
            finiteMaxFunction τ g K (τ x) ∂μ
        ≤
      ∫ x, (finitePositiveMaxSet τ g (K + 1)).indicator g x ∂μ :=
    MeasureTheory.integral_mono hsub hind fun x =>
      indicator_mul_ge_max_sub_shift_succ g K x
  rwa [MeasureTheory.integral_sub hmax_succ hmax_shift] at hle

private lemma integral_finiteMaxFunction_comp_tau
    (hτ_mp : MeasurePreserving τ μ μ)
    {g : X → ℝ} (hg_meas : StronglyMeasurable g)
    (hg_int : Integrable g μ)
    (K : ℕ) :
    ∫ x, finiteMaxFunction τ g K (τ x) ∂μ
      =
    ∫ x, finiteMaxFunction τ g K x ∂μ := by
  -- Proof idea: use local non-invertible `integral_comp_measurePreserving`.
  exact integral_comp_measurePreserving hτ_mp
    (finiteMaxFunction_integrable hτ_mp hg_meas hg_int K)

/-- Finite Hopf maximal ergodic lemma.  No ergodicity is used. -/
theorem finite_maximal_ergodic_nonneg_integral
    (hτ_mp : MeasurePreserving τ μ μ)
    {g : X → ℝ} (hg_meas : StronglyMeasurable g)
    (hg_int : Integrable g μ) (K : ℕ) :
    0 ≤ ∫ x in finitePositiveMaxSet τ g K, g x ∂μ := by
  -- Proof idea: split on `K`.  The zero case is empty.  The successor case
  -- integrates the one-step inequality, rewrites the shifted max integral by
  -- measure preservation, and uses monotonicity of `finiteMaxFunction`.
  induction K with
  | zero =>
      have hset : finitePositiveMaxSet τ g 0 = ∅ := by
        ext x
        simp [finitePositiveMaxSet]
      simp [hset]
  | succ K =>
      have hle :=
        integral_indicator_ge_max_sub_shift_succ hτ_mp hg_meas hg_int K
      have hcomp :=
        integral_finiteMaxFunction_comp_tau hτ_mp hg_meas hg_int K
      have hle' :
          ∫ x, finiteMaxFunction τ g (K + 1) x ∂μ
            - ∫ x, finiteMaxFunction τ g K x ∂μ
            ≤
          ∫ x, (finitePositiveMaxSet τ g (K + 1)).indicator g x ∂μ := by
        simpa [hcomp] using hle
      have hmono_int :
          ∫ x, finiteMaxFunction τ g K x ∂μ
            ≤ ∫ x, finiteMaxFunction τ g (K + 1) x ∂μ :=
        MeasureTheory.integral_mono
          (finiteMaxFunction_integrable hτ_mp hg_meas hg_int K)
          (finiteMaxFunction_integrable hτ_mp hg_meas hg_int (K + 1))
          (fun x => finiteMaxFunction_mono_succ g K x)
      have hnonneg :
          0 ≤
            ∫ x, finiteMaxFunction τ g (K + 1) x ∂μ
              - ∫ x, finiteMaxFunction τ g K x ∂μ := by
        linarith
      have hind_nonneg :
          0 ≤ ∫ x,
            (finitePositiveMaxSet τ g (K + 1)).indicator g x ∂μ :=
        hnonneg.trans hle'
      simpa [integral_indicator_finitePositiveMaxSet_eq_setIntegral
          hτ_mp hg_meas hg_int (K + 1)] using hind_nonneg

end SpectralGapsPrelim.BirkhoffPointwise
