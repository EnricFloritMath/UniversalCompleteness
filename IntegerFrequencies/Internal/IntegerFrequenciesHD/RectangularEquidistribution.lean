import IntegerFrequenciesHD.DefinitionsAndTarget
import Theorem14.UniformIntervalEquidistribution

/-!
# Rectangular equidistribution

The higher-dimensional count is reduced to the proved one-dimensional
uniform interval theorem by slicing the canonical first coordinate.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace IntegerFrequenciesHD.Internal

/- Use the cardinality formula for `Fintype.piFinset`; this
includes the empty-side cases without a separate hypothesis. -/
theorem card_natIndexRectangle {d : Nat} (N : Fin d → Nat) :
    (natIndexRectangle N).card = ∏ i, N i := by
  simp [natIndexRectangle]

/- In rational independence set the selected rational
coordinate coefficient to one, every other coordinate to zero, and the
constant coefficient to a hypothetical rational representation. -/
theorem firstCoordinate_irrational {d : Nat} (hd : 0 < d)
    {alpha : RealVec d} (hAlpha : RationallyIndependentWithOne alpha) :
    Irrational (alpha (firstCoordinate hd)) := by
  rintro ⟨q, hq⟩
  let c : Fin d → Rat := fun i => if i = firstCoordinate hd then 1 else 0
  have hsum : ∑ i, (c i : Real) * alpha i =
      alpha (firstCoordinate hd) := by
    classical
    rw [Finset.sum_eq_single (firstCoordinate hd)]
    · simp [c]
    · intro i _ hi
      simp [c, hi]
    · simp
  have hrel : ((-q : Rat) : Real) +
      ∑ i, (c i : Real) * alpha i = 0 := by
    calc
      ((-q : Rat) : Real) + ∑ i, (c i : Real) * alpha i =
          -(q : Real) + alpha (firstCoordinate hd) := by
            rw [hsum, Rat.cast_neg]
      _ = 0 := by rw [← hq]; ring
  have hc := (hAlpha (-q) c hrel).2 (firstCoordinate hd)
  simp [c] at hc

/- Apply the vendored 1D uniform interval count to
`alpha (firstCoordinate hd)` and an arbitrary real starting phase; multiply
out the normalized count using positivity of the selected side. -/
theorem rectangularIntervalCount_slice_bound {d : Nat} (hd : 0 < d)
    {alpha : RealVec d} (hAlpha : RationallyIndependentWithOne alpha)
    (a b : Real) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    ∀ eta : Real, 0 < eta →
      ∃ N0 : Nat, 0 < N0 ∧
      ∀ (N : Fin d → Nat) (x : Real),
        N (firstCoordinate hd) ≥ N0 →
        |(((Finset.range (N (firstCoordinate hd))).filter (fun (r : Nat) =>
              Int.fract (x + (r : Real) * alpha (firstCoordinate hd)) ∈
                Set.Ico a b)).card : Real) -
            (b - a) * (N (firstCoordinate hd) : Real)| <
          eta * (N (firstCoordinate hd) : Real) := by
  intro eta heta
  obtain ⟨Nbase, hNbase⟩ :=
    Theorem14.Internal.uniform_intervalVisitCount
      (alpha (firstCoordinate hd))
      (firstCoordinate_irrational hd hAlpha) a b ha hab hb eta heta
  refine ⟨max Nbase 1, Nat.zero_lt_one.trans_le (Nat.le_max_right _ _), ?_⟩
  intro N x hN
  let M := N (firstCoordinate hd)
  have hMbase : Nbase ≤ M := (Nat.le_max_left _ _).trans hN
  have hMpos : 0 < M :=
    Nat.zero_lt_one.trans_le ((Nat.le_max_right _ _).trans hN)
  have hvisit := hNbase M hMbase hMpos
    ((x : Real) : AddCircle (1 : Real))
  have hcount :
      Theorem14.Internal.intervalVisitCount
          (alpha (firstCoordinate hd)) a b M
          ((x : Real) : AddCircle (1 : Real)) =
        ((Finset.range M).filter (fun r : Nat =>
          Int.fract (x + (r : Real) * alpha (firstCoordinate hd)) ∈
            Set.Ico a b)).card := by
    classical
    unfold Theorem14.Internal.intervalVisitCount
    apply congrArg Finset.card
    ext r
    simp only [Finset.mem_filter, Finset.mem_range,
      Theorem14.Internal.circleInterval, Set.mem_preimage, Set.mem_Ico]
    rw [← AddCircle.coe_add, Theorem12.Generic.unitRep_coe_eq_fract]
  rw [hcount] at hvisit
  have hMreal : 0 < (M : Real) := by exact_mod_cast hMpos
  let C : Real := (((Finset.range M).filter (fun r : Nat =>
      Int.fract (x + (r : Real) * alpha (firstCoordinate hd)) ∈
        Set.Ico a b)).card : Real)
  change |C / (M : Real) - (b - a)| < eta at hvisit
  change |C - (b - a) * (M : Real)| < eta * (M : Real)
  rw [show C - (b - a) * (M : Real) =
      (M : Real) * (C / (M : Real) - (b - a)) by
    rw [mul_sub, mul_div_cancel₀ _ (ne_of_gt hMreal)]
    ring]
  rw [abs_mul, abs_of_pos hMreal]
  simpa [mul_comm] using mul_lt_mul_of_pos_left hvisit hMreal

/- Reindex the full finite Pi rectangle as outer tuples times
the selected coordinate using `Function.update`. Apply the slice bound at each
outer phase and sum errors; if an outer side is zero, both sides vanish. -/
theorem uniform_rectangularIntervalCount {d : Nat} (hd : 0 < d)
    {alpha : RealVec d} (hAlpha : RationallyIndependentWithOne alpha)
    (a b : Real) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    ∀ epsilon : Real, 0 < epsilon →
      ∃ N0 : Nat, 0 < N0 ∧
      ∀ (N : Fin d → Nat), N (firstCoordinate hd) ≥ N0 →
      ∀ x : Real,
        |(rectangularIntervalCount alpha a b N x : Real) -
            (b - a) * (∏ i, N i : Nat)| ≤
          epsilon * (∏ i, N i : Nat) := by
  intro epsilon hepsilon
  obtain ⟨N0, hN0, hslice⟩ :=
    rectangularIntervalCount_slice_bound hd hAlpha a b ha hab hb
      epsilon hepsilon
  refine ⟨N0, hN0, ?_⟩
  intro N hN x
  classical
  let i0 : Fin d := firstCoordinate hd
  let outerN : Fin d → Nat := Function.update N i0 1
  let outer : Finset (Fin d → Nat) := natIndexRectangle outerN
  let good : (Fin d → Nat) → Prop := fun k ↦
    Int.fract (x + ∑ i, (k i : Real) * alpha i) ∈ Set.Ico a b
  let slice : (Fin d → Nat) → Nat := fun u ↦
    ((Finset.range (N i0)).filter (fun r : Nat ↦
      good (Function.update u i0 r))).card
  have houter_zero {u : Fin d → Nat} (hu : u ∈ outer) : u i0 = 0 := by
    have hui := Fintype.mem_piFinset.mp hu i0
    simp only [Finset.mem_range] at hui
    have : u i0 < 1 := by simpa [outerN] using hui
    omega
  have hphase {u : Fin d → Nat} (hu : u ∈ outer) (r : Nat) :
      x + ∑ i, ((Function.update u i0 r) i : Real) * alpha i =
        (x + ∑ i, (u i : Real) * alpha i) + (r : Real) * alpha i0 := by
    have hui : u i0 = 0 := houter_zero hu
    rw [Fintype.sum_eq_add_sum_compl i0,
      Fintype.sum_eq_add_sum_compl i0]
    have hcomp :
        ∑ j ∈ {i0}ᶜ, ((Function.update u i0 r) j : Real) * alpha j =
          ∑ j ∈ {i0}ᶜ, (u j : Real) * alpha j := by
      apply Finset.sum_congr rfl
      intro j hj
      have hji : j ≠ i0 := by simpa using hj
      simp [hji]
    rw [hcomp, hui]
    simp only [Function.update_self, Nat.cast_zero, zero_mul]
    ring
  have hrestore (k : Fin d → Nat) :
      Function.update (Function.update k i0 0) i0 (k i0) = k := by
    funext j
    by_cases hj : j = i0
    · subst j
      simp
    · simp [hj]
  let pairs : Finset ((Fin d → Nat) × Nat) :=
    (outer.product (Finset.range (N i0))).filter (fun p ↦
      good (Function.update p.1 i0 p.2))
  have hreindex :
      ((natIndexRectangle N).filter good).card = pairs.card := by
    refine Finset.card_bij'
        (fun k _ ↦ (Function.update k i0 0, k i0))
        (fun p _ ↦ Function.update p.1 i0 p.2) ?_ ?_ ?_ ?_
    · intro k hk
      rcases Finset.mem_filter.mp hk with ⟨hk, hgood⟩
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · refine Finset.mem_product.mpr ⟨Fintype.mem_piFinset.mpr ?_, ?_⟩
        · intro j
          simp only [Finset.mem_range]
          by_cases hj : j = i0
          · subst j
            simp [outerN]
          · have hkj := Fintype.mem_piFinset.mp hk j
            simpa [outerN, hj] using hkj
        · exact Fintype.mem_piFinset.mp hk i0
      · rw [hrestore]
        exact hgood
    · intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hp, hgood⟩
      rcases Finset.mem_product.mp hp with ⟨hu, hr⟩
      refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr ?_, hgood⟩
      intro j
      simp only [Finset.mem_range]
      by_cases hj : j = i0
      · subst j
        simpa using hr
      · have huj := Fintype.mem_piFinset.mp hu j
        simpa [outerN, hj] using huj
    · intro k hk
      exact hrestore k
    · intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hp, _⟩
      rcases Finset.mem_product.mp hp with ⟨hu, hr⟩
      apply Prod.ext
      · funext j
        by_cases hj : j = i0
        · subst j
          simp [houter_zero hu]
        · simp [hj]
      · simp
  have hpairs_sum : pairs.card = ∑ u ∈ outer, slice u := by
    calc
      pairs.card = ∑ p ∈ outer.product (Finset.range (N i0)),
          if good (Function.update p.1 i0 p.2) then 1 else 0 := by
            simp only [pairs, Finset.card_eq_sum_ones, Finset.sum_filter]
      _ = ∑ u ∈ outer, ∑ r ∈ Finset.range (N i0),
          if good (Function.update u i0 r) then 1 else 0 := by
            simpa using Finset.sum_product outer (Finset.range (N i0))
              (fun p ↦ if good (Function.update p.1 i0 p.2) then 1 else 0)
      _ = ∑ u ∈ outer, slice u := by
            apply Finset.sum_congr rfl
            intro u hu
            simp only [slice, Finset.card_eq_sum_ones, Finset.sum_filter]
  have hslice_one (u : Fin d → Nat) (hu : u ∈ outer) :
      |(slice u : Real) - (b - a) * (N i0 : Real)| <
        epsilon * (N i0 : Real) := by
    have hs := hslice N (x + ∑ i, (u i : Real) * alpha i)
      (by simpa [i0] using hN)
    change
      |(((Finset.range (N i0)).filter (fun r : Nat ↦
          good (Function.update u i0 r))).card : Real) -
          (b - a) * (N i0 : Real)| < epsilon * (N i0 : Real)
    have hfilters :
        (Finset.range (N i0)).filter (fun r : Nat ↦
            good (Function.update u i0 r)) =
          (Finset.range (N i0)).filter (fun r : Nat ↦
            Int.fract ((x + ∑ i, (u i : Real) * alpha i) +
              (r : Real) * alpha i0) ∈ Set.Ico a b) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_range]
      change (r < N i0 ∧
        Int.fract (x + ∑ i, ((Function.update u i0 r) i : Real) * alpha i) ∈
          Set.Ico a b) ↔
        (r < N i0 ∧
          Int.fract ((x + ∑ i, (u i : Real) * alpha i) +
            (r : Real) * alpha i0) ∈ Set.Ico a b)
      rw [hphase hu r]
    rw [hfilters]
    simpa [i0] using hs
  have herror :
      |(∑ u ∈ outer, (slice u : Real)) -
          (b - a) * ((outer.card * N i0 : Nat) : Real)| ≤
        epsilon * ((outer.card * N i0 : Nat) : Real) := by
    calc
      |(∑ u ∈ outer, (slice u : Real)) -
          (b - a) * ((outer.card * N i0 : Nat) : Real)| =
          |∑ u ∈ outer,
            ((slice u : Real) - (b - a) * (N i0 : Real))| := by
              congr 1
              rw [Finset.sum_sub_distrib]
              simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_mul]
              ring
      _ ≤ ∑ u ∈ outer,
          |(slice u : Real) - (b - a) * (N i0 : Real)| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _u ∈ outer, epsilon * (N i0 : Real) := by
            exact Finset.sum_le_sum (fun u hu ↦ le_of_lt (hslice_one u hu))
      _ = epsilon * ((outer.card * N i0 : Nat) : Real) := by
            simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_mul]
            ring
  have houter_card : outer.card * N i0 = ∏ i, N i := by
    rw [show outer.card = ∏ i, outerN i from card_natIndexRectangle outerN]
    rw [Fintype.prod_eq_prod_compl_mul i0,
      Fintype.prod_eq_prod_compl_mul i0]
    simp only [outerN, Function.update_self]
    rw [mul_one]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    have hji : j ≠ i0 := by simpa using hj
    simp [hji]
  have hcount : rectangularIntervalCount alpha a b N x =
      ∑ u ∈ outer, slice u := by
    change ((natIndexRectangle N).filter good).card =
      ∑ u ∈ outer, slice u
    exact hreindex.trans hpairs_sum
  rw [hcount, ← houter_card]
  simpa only [Nat.cast_sum] using herror

end IntegerFrequenciesHD.Internal
