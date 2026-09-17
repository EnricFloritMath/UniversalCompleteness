import IntegerFrequenciesHD.RectangularEquidistribution

/-!
# Cubical frequency density

Integer points in an arbitrary translated real cube are reindexed by the
canonical natural rectangle and compared quantitatively with `R ^ d`.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace IntegerFrequenciesHD.Internal

/- Reindex by `intVecRealCubeEquivNatIndexRectangle`, expand `n = M + k`, distribute
the finite dot product, and normalize fractional-part membership. -/
theorem selected_realCube_count_eq_rectangularIntervalCount {d : Nat}
    (alpha : RealVec d) (v : Real) (y : RealVec d) (R : Real) (hR : 0 ≤ R) :
    cubeCount (integerFrequencySetHD alpha v) y R =
      rectangularIntervalCount alpha (1 - v) 1
        (latticeRectangleSide y R)
        (dotIntReal (latticeRectangleOrigin y) alpha) := by
  classical
  let M : IntVec d := latticeRectangleOrigin y
  let K : Fin d → Nat := latticeRectangleSide y R
  let e := intVecRealCubeEquivNatIndexRectangle y R hR
  have hdot (n : {n : IntVec d //
      (fun i ↦ (n i : Real)) ∈ realCube y R}) :
      dotIntReal n.1 alpha =
        dotIntReal M alpha + ∑ i, ((e n).1 i : Real) * alpha i := by
    have hcoord (i : Fin d) : (n.1 i : Real) =
        (M i : Real) + ((e n).1 i : Real) := by
      have hback := congrArg (fun z ↦ z.1 i) (e.symm_apply_apply n)
      change M i + ((e n).1 i : Int) = n.1 i at hback
      norm_cast
      exact hback.symm
    unfold dotIntReal
    simp_rw [hcoord, add_mul]
    rw [Finset.sum_add_distrib]
  unfold cubeCount rectangularIntervalCount
  rw [← Set.ncard_coe_finset]
  refine Set.ncard_congr
      (fun n hn ↦ (e ⟨n, hn.2⟩).1) ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_coe, Finset.mem_filter]
    refine ⟨(e ⟨n, hn.2⟩).2, ?_⟩
    rw [← hdot ⟨n, hn.2⟩]
    exact hn.1
  · intro n m hn hm hnm
    have hem : e ⟨n, hn.2⟩ = e ⟨m, hm.2⟩ := Subtype.ext hnm
    exact congrArg Subtype.val (e.injective hem)
  · intro k hk
    simp only [Finset.mem_coe, Finset.mem_filter] at hk
    let nk := e.symm ⟨k, hk.1⟩
    refine ⟨nk.1, ?_, ?_⟩
    · refine ⟨?_, nk.2⟩
      change Int.fract (dotIntReal nk.1 alpha) ∈ Set.Ico (1 - v) 1
      rw [hdot nk]
      have henk : e nk = ⟨k, hk.1⟩ := by simp [nk]
      rw [henk]
      simpa [M] using hk.2
    · change (e nk).1 = k
      simp [nk]

/- Use lower and upper ceiling inequalities; `hR` makes the
ceiling difference nonnegative, allowing removal of `Int.toNat`. -/
theorem latticeRectangleSide_close {d : Nat} (y : RealVec d)
    (R : Real) (hR : 0 ≤ R) (i : Fin d) :
    |(latticeRectangleSide y R i : Real) - R| ≤ 1 := by
  have hmono : Int.ceil (y i) ≤ Int.ceil (y i + R) :=
    Int.ceil_mono (by linarith)
  have hdiff : 0 ≤ Int.ceil (y i + R) - Int.ceil (y i) :=
    sub_nonneg.mpr hmono
  have hside : (latticeRectangleSide y R i : Real) =
      (Int.ceil (y i + R) : Real) - (Int.ceil (y i) : Real) := by
    have hz : ((Int.toNat
        (Int.ceil (y i + R) - Int.ceil (y i)) : Nat) : Int) =
        Int.ceil (y i + R) - Int.ceil (y i) :=
      Int.toNat_of_nonneg hdiff
    change ((Int.toNat
      (Int.ceil (y i + R) - Int.ceil (y i)) : Nat) : Real) = _
    norm_cast
  rw [hside, abs_le]
  constructor
  · have hceilUpper : (Int.ceil (y i) : Real) < y i + 1 :=
      Int.ceil_lt_add_one (y i)
    have hceilLower : y i + R ≤ (Int.ceil (y i + R) : Real) :=
      Int.le_ceil (y i + R)
    linarith
  · have hceilUpper : (Int.ceil (y i + R) : Real) < y i + R + 1 :=
      Int.ceil_lt_add_one (y i + R)
    have hceilLower : y i ≤ (Int.ceil (y i) : Real) :=
      Int.le_ceil (y i)
    linarith

/- Sandwich every side between `R - 1` and `R + 1`, compare
the finite products, and use an explicit fixed-power estimate for large `R`.
The threshold and estimate are uniform in `y`. -/
theorem latticeRectangle_volume_error (d : Nat) :
    ∀ epsilon : Real, 0 < epsilon →
      ∃ R0 : Real, 1 ≤ R0 ∧ ∀ R : Real, R0 ≤ R →
      ∀ y : RealVec d,
        |∏ i, (latticeRectangleSide y R i : Real) - R ^ d| ≤
          epsilon * R ^ d := by
  induction d with
  | zero =>
      intro epsilon hepsilon
      refine ⟨1, le_rfl, ?_⟩
      intro R hR y
      simp [hepsilon.le]
  | succ d ih =>
      intro epsilon hepsilon
      let eta : Real := epsilon / 3
      have heta : 0 < eta := by dsimp [eta]; linarith
      obtain ⟨Rprev, hRprev, hprev⟩ := ih eta heta
      let R0 : Real := max Rprev (max 1 ((1 + eta) / eta))
      have hR0one : 1 ≤ R0 :=
        (le_max_left 1 ((1 + eta) / eta)).trans
          (le_max_right Rprev (max 1 ((1 + eta) / eta)))
      refine ⟨R0, hR0one, ?_⟩
      intro R hRR0 y
      have hRprevR : Rprev ≤ R :=
        (le_max_left Rprev (max 1 ((1 + eta) / eta))).trans hRR0
      have hinner : max 1 ((1 + eta) / eta) ≤ R0 :=
        le_max_right Rprev _
      have hRone : 1 ≤ R :=
        (le_max_left 1 ((1 + eta) / eta)).trans (hinner.trans hRR0)
      have hRratio : (1 + eta) / eta ≤ R :=
        (le_max_right 1 ((1 + eta) / eta)).trans (hinner.trans hRR0)
      have hRnonneg : 0 ≤ R := zero_le_one.trans hRone
      have hcoeff : 1 + eta ≤ eta * R := by
        have := (div_le_iff₀ heta).mp hRratio
        simpa [mul_comm] using this
      let ytail : RealVec d := fun i ↦ y i.succ
      let P : Real := ∏ i : Fin d,
        (latticeRectangleSide y R i.succ : Real)
      let S : Real := latticeRectangleSide y R (0 : Fin (d + 1))
      have htail : |P - R ^ d| ≤ eta * R ^ d := by
        simpa [P, ytail, latticeRectangleSide] using
          hprev R hRprevR ytail
      have hPnonneg : 0 ≤ P := by
        dsimp [P]
        exact Finset.prod_nonneg fun i _ ↦ Nat.cast_nonneg _
      have hpow : 0 ≤ R ^ d := pow_nonneg hRnonneg d
      have hPupper : P ≤ (1 + eta) * R ^ d := by
        have hu := (abs_le.mp htail).2
        calc
          P ≤ R ^ d + eta * R ^ d := by linarith
          _ = (1 + eta) * R ^ d := by ring
      have hPscaled : P ≤ eta * R ^ (d + 1) := by
        calc
          P ≤ (1 + eta) * R ^ d := hPupper
          _ ≤ (eta * R) * R ^ d :=
            mul_le_mul_of_nonneg_right hcoeff hpow
          _ = eta * R ^ (d + 1) := by rw [pow_succ]; ring
      have hside : |S - R| ≤ 1 := by
        exact latticeRectangleSide_close y R hRnonneg 0
      rw [Fin.prod_univ_succ]
      change |S * P - R ^ (d + 1)| ≤ epsilon * R ^ (d + 1)
      calc
        |S * P - R ^ (d + 1)| =
            |(S - R) * P + R * (P - R ^ d)| := by
              rw [pow_succ]
              ring
        _ ≤ |(S - R) * P| + |R * (P - R ^ d)| := abs_add_le _ _
        _ = |S - R| * P + R * |P - R ^ d| := by
              rw [abs_mul, abs_mul, abs_of_nonneg hPnonneg,
                abs_of_nonneg hRnonneg]
        _ ≤ 1 * P + R * (eta * R ^ d) := by
              exact add_le_add
                (mul_le_mul_of_nonneg_right hside hPnonneg)
                (mul_le_mul_of_nonneg_left htail hRnonneg)
        _ ≤ eta * R ^ (d + 1) + eta * R ^ (d + 1) := by
              simp only [one_mul]
              apply add_le_add hPscaled
              rw [pow_succ]
              ring_nf
              exact le_rfl
        _ ≤ epsilon * R ^ (d + 1) := by
              have hpow' : 0 ≤ R ^ (d + 1) := pow_nonneg hRnonneg _
              dsimp [eta]
              nlinarith

/- The lower half of `latticeRectangleSide_close` gives
`N0 ≤ R - 1 ≤ side`; cast this final inequality back to naturals. -/
theorem latticeRectangleSide_ge_of_add_one_le {d : Nat}
    (N0 : Nat) (y : RealVec d) (R : Real) (i : Fin d)
    (h : (N0 : Real) + 1 ≤ R) :
    N0 ≤ latticeRectangleSide y R i := by
  have hN0 : 0 ≤ (N0 : Real) := Nat.cast_nonneg N0
  have hR : 0 ≤ R := by linarith
  have hclose := latticeRectangleSide_close y R hR i
  have hlower : (N0 : Real) ≤ (latticeRectangleSide y R i : Real) := by
    rw [abs_le] at hclose
    linarith [hclose.1]
  exact_mod_cast hlower

/- Apply rectangular equidistribution with a small error and the
product-volume estimate. Choose `R0` also large enough for the selected side,
bound the rectangle volume by `2 * R^d`, and finish by triangle inequality. -/
theorem uniform_realCube_density {d : Nat} (hd : 0 < d)
    {alpha : RealVec d} (hAlpha : RationallyIndependentWithOne alpha)
    (v : Real) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    ∀ epsilon : Real, 0 < epsilon →
      ∃ R0 : Real, 0 < R0 ∧ ∀ R : Real, R0 ≤ R →
      ∀ y : RealVec d,
        |(cubeCount (integerFrequencySetHD alpha v) y R : Real) - v * R ^ d| ≤
          epsilon * R ^ d := by
  intro epsilon hepsilon
  let delta : Real := epsilon / 4
  let eta : Real := min 1 (epsilon / 4)
  have hdelta : 0 < delta := by dsimp [delta]; linarith
  have heta : 0 < eta := by
    dsimp [eta]
    exact lt_min zero_lt_one (by linarith)
  have heta_one : eta ≤ 1 := by exact min_le_left _ _
  have heta_epsilon : eta ≤ epsilon / 4 := by exact min_le_right _ _
  obtain ⟨N0, hN0, hrect⟩ :=
    uniform_rectangularIntervalCount hd hAlpha (1 - v) 1
      (by linarith) (by linarith) le_rfl delta hdelta
  obtain ⟨Rvol, hRvol_one, hvol⟩ :=
    latticeRectangle_volume_error d eta heta
  let R0 : Real := max Rvol ((N0 : Real) + 1)
  have hR0pos : 0 < R0 :=
    lt_of_lt_of_le zero_lt_one
      (hRvol_one.trans (le_max_left Rvol ((N0 : Real) + 1)))
  refine ⟨R0, hR0pos, ?_⟩
  intro R hRR0 y
  have hRvolR : Rvol ≤ R :=
    (le_max_left Rvol ((N0 : Real) + 1)).trans hRR0
  have hRN0 : (N0 : Real) + 1 ≤ R :=
    (le_max_right Rvol ((N0 : Real) + 1)).trans hRR0
  have hRone : 1 ≤ R := hRvol_one.trans hRvolR
  have hRnonneg : 0 ≤ R := zero_le_one.trans hRone
  have hpow : 0 ≤ R ^ d := pow_nonneg hRnonneg d
  let K : Fin d → Nat := latticeRectangleSide y R
  let P : Real := ∏ i, (K i : Real)
  have hside : N0 ≤ K (firstCoordinate hd) := by
    exact latticeRectangleSide_ge_of_add_one_le N0 y R
      (firstCoordinate hd) hRN0
  have hvolume : |P - R ^ d| ≤ eta * R ^ d := by
    simpa [P, K] using hvol R hRvolR y
  have hPnonneg : 0 ≤ P := by
    dsimp [P]
    exact Finset.prod_nonneg fun i _ ↦ Nat.cast_nonneg _
  have hPtwo : P ≤ 2 * R ^ d := by
    have hu := (abs_le.mp hvolume).2
    calc
      P ≤ (1 + eta) * R ^ d := by linarith
      _ ≤ 2 * R ^ d :=
        mul_le_mul_of_nonneg_right (by linarith [heta_one]) hpow
  have hcountP :
      |(cubeCount (integerFrequencySetHD alpha v) y R : Real) - v * P| ≤
        delta * P := by
    rw [selected_realCube_count_eq_rectangularIntervalCount alpha v y R hRnonneg]
    have hc := hrect K hside (dotIntReal (latticeRectangleOrigin y) alpha)
    simpa only [sub_sub_cancel, P, Nat.cast_prod] using hc
  have hcountSmall :
      |(cubeCount (integerFrequencySetHD alpha v) y R : Real) - v * P| ≤
        (epsilon / 2) * R ^ d := by
    calc
      |(cubeCount (integerFrequencySetHD alpha v) y R : Real) - v * P| ≤
          delta * P := hcountP
      _ ≤ delta * (2 * R ^ d) :=
        mul_le_mul_of_nonneg_left hPtwo hdelta.le
      _ = (epsilon / 2) * R ^ d := by dsimp [delta]; ring
  have hetaPow : 0 ≤ eta * R ^ d := mul_nonneg heta.le hpow
  have hvolumeSmall : |v * (P - R ^ d)| ≤
      (epsilon / 4) * R ^ d := by
    calc
      |v * (P - R ^ d)| = v * |P - R ^ d| := by
        rw [abs_mul, abs_of_nonneg hv0]
      _ ≤ v * (eta * R ^ d) :=
        mul_le_mul_of_nonneg_left hvolume hv0
      _ ≤ 1 * (eta * R ^ d) :=
        mul_le_mul_of_nonneg_right hv1 hetaPow
      _ ≤ (epsilon / 4) * R ^ d := by
        simp only [one_mul]
        exact mul_le_mul_of_nonneg_right heta_epsilon hpow
  calc
    |(cubeCount (integerFrequencySetHD alpha v) y R : Real) - v * R ^ d| =
        |((cubeCount (integerFrequencySetHD alpha v) y R : Real) - v * P) +
          v * (P - R ^ d)| := by ring
    _ ≤ |(cubeCount (integerFrequencySetHD alpha v) y R : Real) - v * P| +
        |v * (P - R ^ d)| := abs_add_le _ _
    _ ≤ (epsilon / 2) * R ^ d + (epsilon / 4) * R ^ d :=
      add_le_add hcountSmall hvolumeSmall
    _ = (epsilon / 2 + epsilon / 4) * R ^ d := by ring
    _ ≤ epsilon * R ^ d :=
      mul_le_mul_of_nonneg_right (by linarith) hpow

end IntegerFrequenciesHD.Internal

namespace IntegerFrequenciesHD

/- Fill the structure's finiteness field from the canonical
finite rectangle equivalence and its quantitative field from
`Internal.uniform_realCube_density`. -/
theorem integerFrequencySetHD_hasUniformCubicalDensity {d : Nat}
    (hd : 0 < d) {alpha : RealVec d}
    (hAlpha : RationallyIndependentWithOne alpha)
    (v : Real) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    HasUniformCubicalDensity (integerFrequencySetHD alpha v) v := by
  refine ⟨?_, Internal.uniform_realCube_density hd hAlpha v hv0 hv1⟩
  intro y R hR
  let e := Internal.intVecRealCubeEquivNatIndexRectangle y R hR
  have hcube : Set.Finite {n : IntVec d |
      (fun i ↦ (n i : Real)) ∈ realCube y R} := by
    rw [← Set.finite_coe_iff]
    exact Finite.of_injective e e.injective
  apply hcube.subset
  intro n hn
  exact hn.2

end IntegerFrequenciesHD
