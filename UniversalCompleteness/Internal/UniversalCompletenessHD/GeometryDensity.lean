import UniversalCompletenessHD.Definitions

/-!
# Frequency geometry and quantitative cubical density

This module proves the frequency geometry and cubical density statements.
Its transparent definitions live in `Definitions.lean`.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace UniversalCompletenessHD.Internal

/- Expand the `WithLp 2` norm and the explicit square-root
sum-of-squares definition. -/
private theorem euclideanNormHD_eq_norm_toEuclideanSpaceHD {d : Nat}
    (x : RealVec d) :
    euclideanNormHD x = ‖toEuclideanSpaceHD x‖ := by
  rw [euclideanNormHD, EuclideanSpace.norm_eq]
  simp [toEuclideanSpaceHD, Real.norm_eq_abs, sq_abs]

/- Rewrite to a norm and use `norm_nonneg`. -/
private theorem euclideanNormHD_nonneg {d : Nat} (x : RealVec d) :
    0 ≤ euclideanNormHD x := by
  rw [euclideanNormHD_eq_norm_toEuclideanSpaceHD]
  exact norm_nonneg _

/- Rewrite to a norm and use injectivity of the coordinate
wrapper. -/
private theorem euclideanNormHD_eq_zero_iff {d : Nat} (x : RealVec d) :
    euclideanNormHD x = 0 ↔ x = 0 := by
  rw [euclideanNormHD_eq_norm_toEuclideanSpaceHD, norm_eq_zero]
  constructor
  · intro h
    funext i
    have hi := congrArg (fun y : EuclideanSpace Real (Fin d) ↦ y i) h
    simpa [toEuclideanSpaceHD] using hi
  · rintro rfl
    rfl

/- Transport `norm_smul` through the coordinate wrapper. -/
private theorem euclideanNormHD_smul {d : Nat} (c : Real) (x : RealVec d) :
    euclideanNormHD (c • x) = |c| * euclideanNormHD x := by
  rw [euclideanNormHD_eq_norm_toEuclideanSpaceHD,
    euclideanNormHD_eq_norm_toEuclideanSpaceHD]
  change ‖c • toEuclideanSpaceHD x‖ = _
  rw [norm_smul, Real.norm_eq_abs]

/- Transport the norm triangle inequality. -/
private theorem euclideanNormHD_add_le {d : Nat} (x y : RealVec d) :
    euclideanNormHD (x + y) ≤ euclideanNormHD x + euclideanNormHD y := by
  rw [euclideanNormHD_eq_norm_toEuclideanSpaceHD,
    euclideanNormHD_eq_norm_toEuclideanSpaceHD,
    euclideanNormHD_eq_norm_toEuclideanSpaceHD]
  change ‖toEuclideanSpaceHD x + toEuclideanSpaceHD y‖ ≤ _
  exact norm_add_le _ _

/- Use the reverse triangle inequality in the selected
Euclidean norm. -/
private theorem euclideanNormHD_sub_le_add {d : Nat} (x y : RealVec d) :
    euclideanNormHD x - euclideanNormHD y ≤ euclideanNormHD (x - y) := by
  rw [euclideanNormHD_eq_norm_toEuclideanSpaceHD,
    euclideanNormHD_eq_norm_toEuclideanSpaceHD,
    euclideanNormHD_eq_norm_toEuclideanSpaceHD]
  change ‖toEuclideanSpaceHD x‖ - ‖toEuclideanSpaceHD y‖ ≤
    ‖toEuclideanSpaceHD x - toEuclideanSpaceHD y‖
  exact norm_sub_norm_le _ _

/- Bound a coordinate projection by the finite Euclidean
norm. -/
private theorem abs_coord_le_euclideanNormHD {d : Nat} (x : RealVec d)
    (i : Fin d) :
    |x i| ≤ euclideanNormHD x := by
  rw [euclideanNormHD_eq_norm_toEuclideanSpaceHD]
  simpa [Real.norm_eq_abs, toEuclideanSpaceHD] using
    (PiLp.norm_apply_le (toEuclideanSpaceHD x) i)

/- Choose a differing integer coordinate and compare its
absolute value with the Euclidean norm. -/
private theorem one_le_euclideanNormHD_int_sub {d : Nat} (n m : IntVec d)
    (hnm : n ≠ m) :
    1 ≤ euclideanNormHD (intCast n - intCast m) := by
  have hcoord : ∃ i : Fin d, n i ≠ m i := by
    by_contra h
    apply hnm
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  obtain ⟨i, hi⟩ := hcoord
  have honeInt : (1 : Int) ≤ |n i - m i| :=
    Int.one_le_abs (sub_ne_zero.mpr hi)
  have honeReal : (1 : Real) ≤ |((n i - m i : Int) : Real)| := by
    rw [← Int.cast_abs]
    exact_mod_cast honeInt
  calc
    (1 : Real) ≤ |((n i - m i : Int) : Real)| := honeReal
    _ = |(intCast n - intCast m) i| := by
      simp [intCast]
    _ ≤ euclideanNormHD (intCast n - intCast m) :=
      abs_coord_le_euclideanNormHD _ i

/- Apply the exact fractional-part bounds.  The final conjunct
is the strict difference bound used by the displacement estimate. -/
private theorem orbitThetaHD_mem {d : Nat} (alpha : RealVec d)
    (n : IntVec d) :
    (-1 / 2 : Real) ≤ orbitThetaHD alpha n ∧
      orbitThetaHD alpha n < 1 / 2 ∧
      |orbitThetaHD alpha n| ≤ 1 / 2 ∧
      ∀ m : IntVec d,
        |orbitThetaHD alpha n - orbitThetaHD alpha m| < 1 := by
  have hnonneg := Int.fract_nonneg (dotIntReal n alpha)
  have hlt := Int.fract_lt_one (dotIntReal n alpha)
  refine ⟨by unfold orbitThetaHD; linarith,
    by unfold orbitThetaHD; linarith, ?_, ?_⟩
  · rw [abs_le]
    constructor <;> unfold orbitThetaHD <;> linarith
  · intro m
    rw [abs_lt]
    constructor <;>
      unfold orbitThetaHD <;>
      linarith [Int.fract_nonneg (dotIntReal m alpha),
        Int.fract_lt_one (dotIntReal m alpha)]

/- Use Euclidean scaling and the theta half-bound. -/
private theorem euclideanNormHD_delta_le {d : Nat} (alpha beta : RealVec d)
    (n : IntVec d) :
    euclideanNormHD (modulatedDeltaHD alpha beta n) ≤
      euclideanNormHD beta / 2 := by
  have hdelta : modulatedDeltaHD alpha beta n =
      orbitThetaHD alpha n • beta := by
    rfl
  rw [hdelta, euclideanNormHD_smul]
  have htheta := (orbitThetaHD_mem alpha n).2.2.1
  exact (mul_le_mul_of_nonneg_right htheta
    (euclideanNormHD_nonneg beta)).trans_eq (by ring)

/- Factor the theta difference and use its non-strict bound by
one; this remains true at `beta = 0`. -/
private theorem euclideanNormHD_delta_sub_le {d : Nat}
    (alpha beta : RealVec d) (n m : IntVec d) :
    euclideanNormHD
        (modulatedDeltaHD alpha beta n - modulatedDeltaHD alpha beta m) ≤
      euclideanNormHD beta := by
  have hdelta : modulatedDeltaHD alpha beta n -
      modulatedDeltaHD alpha beta m =
      (orbitThetaHD alpha n - orbitThetaHD alpha m) • beta := by
    funext i
    simp [modulatedDeltaHD]
    ring
  rw [hdelta, euclideanNormHD_smul]
  have htheta : |orbitThetaHD alpha n - orbitThetaHD alpha m| ≤ 1 :=
    (orbitThetaHD_mem alpha n).2.2.2 m |>.le
  simpa using mul_le_mul_of_nonneg_right htheta
    (euclideanNormHD_nonneg beta)

/- Apply reverse triangle to the integer difference and the
modulation difference. -/
private theorem modulatedLambdaHD_separation_indexed {d : Nat}
    (alpha beta : RealVec d) (n m : IntVec d) (hnm : n ≠ m) :
    1 - euclideanNormHD beta ≤
      euclideanNormHD
        (modulatedLambdaHD alpha beta n - modulatedLambdaHD alpha beta m) := by
  let u : RealVec d := intCast n - intCast m
  let v : RealVec d := modulatedDeltaHD alpha beta n -
    modulatedDeltaHD alpha beta m
  have huv : modulatedLambdaHD alpha beta n - modulatedLambdaHD alpha beta m =
      u + v := by
    funext i
    simp [u, v, intCast, modulatedLambdaHD]
    ring
  have hrev : euclideanNormHD u - euclideanNormHD v ≤
      euclideanNormHD (u + v) := by
    have h := euclideanNormHD_sub_le_add u (-v)
    have hneg : euclideanNormHD (-v) = euclideanNormHD v := by
      rw [euclideanNormHD_eq_norm_toEuclideanSpaceHD,
        euclideanNormHD_eq_norm_toEuclideanSpaceHD]
      change ‖-(toEuclideanSpaceHD v)‖ = ‖toEuclideanSpaceHD v‖
      exact norm_neg _
    simpa [hneg] using h
  have hu : 1 ≤ euclideanNormHD u :=
    one_le_euclideanNormHD_int_sub n m hnm
  have hv : euclideanNormHD v ≤ euclideanNormHD beta :=
    euclideanNormHD_delta_sub_le alpha beta n m
  rw [huv]
  linarith

/- Combine indexed separation with strict beta smallness. -/
private theorem one_half_lt_modulatedLambdaHD_distance {d : Nat}
    (alpha beta : RealVec d) (hbeta : euclideanNormHD beta < 1 / 2)
    (n m : IntVec d) (hnm : n ≠ m) :
    1 / 2 < euclideanNormHD
      (modulatedLambdaHD alpha beta n - modulatedLambdaHD alpha beta m) := by
  have hsep := modulatedLambdaHD_separation_indexed alpha beta n m hnm
  linarith

/- Equality of frequencies contradicts positive indexed
separation. -/
private theorem modulatedLambdaHD_injective {d : Nat}
    (alpha beta : RealVec d) (hbeta : euclideanNormHD beta < 1 / 2) :
    Function.Injective (modulatedLambdaHD alpha beta) := by
  intro n m hnm
  by_contra hne
  have hsep := one_half_lt_modulatedLambdaHD_distance alpha beta hbeta n m hne
  rw [hnm, sub_self] at hsep
  norm_num [euclideanNormHD] at hsep

end UniversalCompletenessHD.Internal

namespace UniversalCompletenessHD

/- Eliminate range witnesses and apply indexed separation with
the Euclidean witness `1/2`. -/
theorem modulatedLambdaSetHD_uniformlyDiscrete {d : Nat}
    (alpha beta : RealVec d) (hbeta : euclideanNormHD beta < 1 / 2) :
    IsUniformlyDiscreteHD (modulatedLambdaSetHD alpha beta) := by
  refine ⟨1 / 2, by norm_num, ?_⟩
  rintro _ ⟨n, rfl⟩ _ ⟨m, rfl⟩ hne
  have hnm : n ≠ m := by
    intro h
    subst m
    exact hne rfl
  exact (Internal.one_half_lt_modulatedLambdaHD_distance
    alpha beta hbeta n m hnm).le

namespace Internal

/- A coordinate is bounded by the Euclidean modulation norm. -/
private theorem modulatedLambdaHD_coordinate_displacement {d : Nat}
    (alpha beta : RealVec d) (n : IntVec d) (i : Fin d) :
    |modulatedLambdaHD alpha beta n i - (n i : Real)| ≤
      euclideanNormHD beta / 2 := by
  have hcoord := Internal.abs_coord_le_euclideanNormHD
    (modulatedDeltaHD alpha beta n) i
  have hnorm := Internal.euclideanNormHD_delta_le alpha beta n
  have heq : modulatedLambdaHD alpha beta n i - (n i : Real) =
      modulatedDeltaHD alpha beta n i := by
    simp [modulatedLambdaHD]
  rw [heq]
  exact hcoord.trans hnorm

/- Use the coordinate displacement bound, preserving the
half-open upper faces. -/
private theorem innerLatticeCubeHD_subset_frequencyIndexCubeHD {d : Nat}
    (alpha beta x : RealVec d) (R : Real) :
    innerLatticeCubeHD beta x R ⊆
      frequencyIndexCubeHD alpha beta x R := by
  intro n hn
  change ∀ i, x i ≤ modulatedLambdaHD alpha beta n i ∧
    modulatedLambdaHD alpha beta n i < x i + R
  change ∀ i, x i + cubeBufferHD beta ≤ (n i : Real) ∧
    (n i : Real) < x i + R - cubeBufferHD beta at hn
  intro i
  have hdisp := abs_le.mp
    (modulatedLambdaHD_coordinate_displacement alpha beta n i)
  have hB : cubeBufferHD beta = euclideanNormHD beta / 2 := rfl
  constructor <;> rw [hB] at hn <;>
    linarith [hn i |>.1, hn i |>.2]

/- Reverse the bounded-displacement inequalities
coordinatewise. -/
private theorem frequencyIndexCubeHD_subset_outerLatticeCubeHD {d : Nat}
    (alpha beta x : RealVec d) (R : Real) :
    frequencyIndexCubeHD alpha beta x R ⊆
      outerLatticeCubeHD beta x R := by
  intro n hn
  change ∀ i, x i - cubeBufferHD beta ≤ (n i : Real) ∧
    (n i : Real) < x i + R + cubeBufferHD beta
  change ∀ i, x i ≤ modulatedLambdaHD alpha beta n i ∧
    modulatedLambdaHD alpha beta n i < x i + R at hn
  intro i
  have hdisp := abs_le.mp
    (modulatedLambdaHD_coordinate_displacement alpha beta n i)
  have hB : cubeBufferHD beta = euclideanNormHD beta / 2 := rfl
  rw [hB]
  constructor <;> have hni := hn i <;>
    linarith [hni.1, hni.2]

/- Bound each integer coordinate between two real endpoints
and use finiteness of finite products. -/
private theorem finite_inner_outer_latticeCubesHD {d : Nat}
    (beta x : RealVec d) (R : Real) :
    (innerLatticeCubeHD beta x R).Finite ∧
      (outerLatticeCubeHD beta x R).Finite := by
  classical
  have hinterval (a b : Real) :
      ({m : Int | a ≤ (m : Real) ∧ (m : Real) < b}).Finite := by
    have heq : {m : Int | a ≤ (m : Real) ∧ (m : Real) < b} =
        (↑(Finset.Ico ⌈a⌉ ⌈b⌉) : Set Int) := by
      ext m
      simp only [Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_Ico]
      rw [Int.ceil_le, Int.lt_ceil]
    rw [heq]
    exact Finset.finite_toSet _
  constructor
  · have hpi := Set.Finite.pi' (fun i : Fin d ↦
      hinterval (x i + cubeBufferHD beta)
        (x i + R - cubeBufferHD beta))
    simpa only [innerLatticeCubeHD, Set.mem_setOf_eq] using hpi
  · have hpi := Set.Finite.pi' (fun i : Fin d ↦
      hinterval (x i - cubeBufferHD beta)
        (x i + R + cubeBufferHD beta))
    simpa only [outerLatticeCubeHD, Set.mem_setOf_eq] using hpi

/- Count a half-open integer interval with floor/ceiling
bounds. -/
private theorem halfOpenIntegerInterval_count_error (a L : Real)
    (hL : 0 ≤ L) :
    ({m : Int | a ≤ (m : Real) ∧ (m : Real) < a + L}).Finite ∧
      |((({m : Int | a ≤ (m : Real) ∧
          (m : Real) < a + L}).ncard : Nat) : Real) - L| ≤ 1 := by
  classical
  let s : Set Int := {m : Int | a ≤ (m : Real) ∧ (m : Real) < a + L}
  have hset : s = (↑(Finset.Ico ⌈a⌉ ⌈a + L⌉) : Set Int) := by
    ext m
    simp only [s, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_Ico]
    rw [Int.ceil_le, Int.lt_ceil]
  have hceil : ⌈a⌉ ≤ ⌈a + L⌉ := Int.ceil_mono (by linarith)
  have hcardInt : ((Finset.Ico ⌈a⌉ ⌈a + L⌉).card : Int) =
      ⌈a + L⌉ - ⌈a⌉ := Int.card_Ico_of_le ⌈a⌉ ⌈a + L⌉ hceil
  have hcardReal : ((Finset.Ico ⌈a⌉ ⌈a + L⌉).card : Real) =
      ((⌈a + L⌉ - ⌈a⌉ : Int) : Real) := by
    exact_mod_cast hcardInt
  have hfinite : s.Finite := by
    rw [hset]
    exact Finset.finite_toSet _
  change s.Finite ∧ |(s.ncard : Real) - L| ≤ 1
  refine ⟨hfinite, ?_⟩
  rw [hset, Set.ncard_coe_finset, hcardReal, abs_le]
  have haLower : a ≤ ((⌈a⌉ : Int) : Real) := Int.le_ceil a
  have haUpper : ((⌈a⌉ : Int) : Real) < a + 1 := Int.ceil_lt_add_one a
  have hbLower : a + L ≤ ((⌈a + L⌉ : Int) : Real) :=
    Int.le_ceil (a + L)
  have hbUpper : ((⌈a + L⌉ : Int) : Real) < a + L + 1 :=
    Int.ceil_lt_add_one (a + L)
  push_cast
  constructor <;> linarith

/- Reindex each integer-vector cube as the product of its
one-coordinate half-open intervals. -/
private theorem inner_outer_latticeCube_card_product {d : Nat}
    (beta x : RealVec d) (R : Real) :
    (innerLatticeCubeHD beta x R).ncard =
        ∏ i, ({m : Int |
          x i + cubeBufferHD beta ≤ (m : Real) ∧
          (m : Real) < x i + R - cubeBufferHD beta}).ncard ∧
      (outerLatticeCubeHD beta x R).ncard =
        ∏ i, ({m : Int |
          x i - cubeBufferHD beta ≤ (m : Real) ∧
          (m : Real) < x i + R + cubeBufferHD beta}).ncard := by
  classical
  let sIn : Fin d → Set Int := fun i ↦ {m : Int |
    x i + cubeBufferHD beta ≤ (m : Real) ∧
    (m : Real) < x i + R - cubeBufferHD beta}
  let sOut : Fin d → Set Int := fun i ↦ {m : Int |
    x i - cubeBufferHD beta ≤ (m : Real) ∧
    (m : Real) < x i + R + cubeBufferHD beta}
  have hin : innerLatticeCubeHD beta x R = Set.univ.pi sIn := by
    ext n
    simp [innerLatticeCubeHD, sIn]
  have hout : outerLatticeCubeHD beta x R = Set.univ.pi sOut := by
    ext n
    simp [outerLatticeCubeHD, sOut]
  rw [hin, hout]
  constructor <;> simp [Set.ncard, Set.encard_pi_eq_prod_encard, sIn, sOut]

/- Telescope a finite product and bound every remaining
factor by `(1+D)R`. -/
private theorem abs_prod_sub_pow_le_HD (d : Nat) (R D : Real)
    (a : Fin d → Real) (hR : 1 ≤ R) (hD : 0 ≤ D)
    (ha : ∀ i, 0 ≤ a i) (hclose : ∀ i, |a i - R| ≤ D) :
    |∏ i, a i - R ^ d| ≤
      (d : Real) * D * (1 + D) ^ (d - 1) * R ^ (d - 1) := by
  induction d with
  | zero => simp
  | succ d ih =>
      let S : Real := a 0
      let P : Real := ∏ i : Fin d, a i.succ
      have hR0 : 0 ≤ R := zero_le_one.trans hR
      have hbase : 1 ≤ 1 + D := by linarith
      have htail : |P - R ^ d| ≤
          (d : Real) * D * (1 + D) ^ (d - 1) * R ^ (d - 1) := by
        exact ih (fun i ↦ a i.succ)
          (fun i ↦ ha i.succ) (fun i ↦ hclose i.succ)
      have hP0 : 0 ≤ P := by
        dsimp [P]
        exact Finset.prod_nonneg (fun i _ ↦ ha i.succ)
      have hcoordUpper (i : Fin d) : a i.succ ≤ (1 + D) * R := by
        have hi := (abs_le.mp (hclose i.succ)).2
        have hDR : D ≤ D * R := by nlinarith
        nlinarith
      have hPupper : P ≤ (1 + D) ^ d * R ^ d := by
        calc
          P ≤ ∏ _i : Fin d, ((1 + D) * R) := by
            dsimp [P]
            exact Finset.prod_le_prod (fun i _ ↦ ha i.succ)
              (fun i _ ↦ hcoordUpper i)
          _ = ((1 + D) * R) ^ d := by simp
          _ = (1 + D) ^ d * R ^ d := by rw [mul_pow]
      have hpowD : (1 + D) ^ (d - 1) ≤ (1 + D) ^ d :=
        pow_le_pow_right₀ hbase (Nat.sub_le d 1)
      have htailWeak :
          (d : Real) * D * (1 + D) ^ (d - 1) * R ^ (d - 1) ≤
            (d : Real) * D * (1 + D) ^ d * R ^ (d - 1) := by
        gcongr <;> positivity
      have hS : |S - R| ≤ D := hclose 0
      rw [Fin.prod_univ_succ]
      change |S * P - R ^ (d + 1)| ≤
        ((d + 1 : Nat) : Real) * D * (1 + D) ^ d * R ^ d
      calc
        |S * P - R ^ (d + 1)| =
            |(S - R) * P + R * (P - R ^ d)| := by
              rw [pow_succ]
              ring
        _ ≤ |(S - R) * P| + |R * (P - R ^ d)| := abs_add_le _ _
        _ = |S - R| * P + R * |P - R ^ d| := by
              rw [abs_mul, abs_mul, abs_of_nonneg hP0, abs_of_nonneg hR0]
        _ ≤ D * ((1 + D) ^ d * R ^ d) +
            R * ((d : Real) * D * (1 + D) ^ d * R ^ (d - 1)) := by
              apply add_le_add
              · exact mul_le_mul hS hPupper hP0 hD
              · exact mul_le_mul_of_nonneg_left (htail.trans htailWeak) hR0
        _ ≤ ((d + 1 : Nat) : Real) * D * (1 + D) ^ d * R ^ d := by
              push_cast
              by_cases hd0 : d = 0
              · subst d
                norm_num
              · have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
                have hpow : R * R ^ (d - 1) = R ^ d := by
                  rw [mul_comm, ← pow_succ,
                    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hd0)]
                rw [show R * ((d : Real) * D * (1 + D) ^ d * R ^ (d - 1)) =
                    (d : Real) * D * (1 + D) ^ d * R ^ d by
                  rw [← hpow]; ring]
                ring_nf
                exact le_rfl

/- Apply the scalar count estimate coordinatewise and the
finite product perturbation inequality. -/
private theorem inner_outer_latticeCube_count_error {d : Nat}
    (beta x : RealVec d) (R : Real)
    (hbeta : euclideanNormHD beta < 1 / 2) (hR : 1 ≤ R) :
    |(((innerLatticeCubeHD beta x R).ncard : Nat) : Real) - R ^ d| ≤
        cubeCountConstantHD d beta * R ^ (d - 1) ∧
      |(((outerLatticeCubeHD beta x R).ncard : Nat) : Real) - R ^ d| ≤
        cubeCountConstantHD d beta * R ^ (d - 1) := by
  classical
  let B : Real := cubeBufferHD beta
  let D : Real := cubeCoordinateErrorHD beta
  let aIn : Fin d → Real := fun i ↦
    (({m : Int | x i + B ≤ (m : Real) ∧
      (m : Real) < x i + R - B}.ncard : Nat) : Real)
  let aOut : Fin d → Real := fun i ↦
    (({m : Int | x i - B ≤ (m : Real) ∧
      (m : Real) < x i + R + B}.ncard : Nat) : Real)
  have hB0 : 0 ≤ B := by
    dsimp [B, cubeBufferHD]
    exact div_nonneg (Internal.euclideanNormHD_nonneg beta) (by norm_num)
  have hBsmall : 2 * B < 1 := by
    dsimp [B, cubeBufferHD]
    linarith
  have hDin : 0 ≤ R - 2 * B := by linarith
  have hDout : 0 ≤ R + 2 * B := by linarith
  have hD0 : 0 ≤ D := by
    dsimp [D, cubeCoordinateErrorHD]
    linarith
  have haIn0 : ∀ i, 0 ≤ aIn i := fun i ↦ by
    dsimp [aIn]
    positivity
  have haOut0 : ∀ i, 0 ≤ aOut i := fun i ↦ by
    dsimp [aOut]
    positivity
  have hcloseIn : ∀ i, |aIn i - R| ≤ D := by
    intro i
    have hi := (halfOpenIntegerInterval_count_error
      (x i + B) (R - 2 * B) hDin).2
    have hset : {m : Int | x i + B ≤ (m : Real) ∧
        (m : Real) < x i + B + (R - 2 * B)} =
        {m : Int | x i + B ≤ (m : Real) ∧
          (m : Real) < x i + R - B} := by
      ext m
      simp only [Set.mem_setOf_eq]
      constructor <;> intro hm
      · convert hm using 1 <;> ring
      · convert hm using 1 <;> ring
    rw [hset] at hi
    change |aIn i - (R - 2 * B)| ≤ 1 at hi
    rw [abs_le] at hi ⊢
    dsimp [D, cubeCoordinateErrorHD]
    constructor <;> linarith
  have hcloseOut : ∀ i, |aOut i - R| ≤ D := by
    intro i
    have hi := (halfOpenIntegerInterval_count_error
      (x i - B) (R + 2 * B) hDout).2
    have hset : {m : Int | x i - B ≤ (m : Real) ∧
        (m : Real) < x i - B + (R + 2 * B)} =
        {m : Int | x i - B ≤ (m : Real) ∧
          (m : Real) < x i + R + B} := by
      ext m
      simp only [Set.mem_setOf_eq]
      constructor <;> intro hm
      · convert hm using 1 <;> ring
      · convert hm using 1 <;> ring
    rw [hset] at hi
    change |aOut i - (R + 2 * B)| ≤ 1 at hi
    rw [abs_le] at hi ⊢
    dsimp [D, cubeCoordinateErrorHD]
    constructor <;> linarith
  have hprodIn := abs_prod_sub_pow_le_HD d R D aIn hR hD0 haIn0 hcloseIn
  have hprodOut := abs_prod_sub_pow_le_HD d R D aOut hR hD0 haOut0 hcloseOut
  have hcard := inner_outer_latticeCube_card_product beta x R
  have hcastIn : (((innerLatticeCubeHD beta x R).ncard : Nat) : Real) =
      ∏ i, aIn i := by
    rw [hcard.1, Nat.cast_prod]
  have hcastOut : (((outerLatticeCubeHD beta x R).ncard : Nat) : Real) =
      ∏ i, aOut i := by
    rw [hcard.2, Nat.cast_prod]
  rw [hcastIn, hcastOut]
  simpa [cubeCountConstantHD, D] using And.intro hprodIn hprodOut

/- Squeeze the indexed frequency set between the finite inner
and outer lattice cubes. -/
private theorem frequencyIndexCubeHD_count_error {d : Nat}
    (hd : 0 < d) (alpha beta x : RealVec d) (R : Real)
    (hbeta : euclideanNormHD beta < 1 / 2) (hR : 1 ≤ R) :
    (frequencyIndexCubeHD alpha beta x R).Finite ∧
      |(((frequencyIndexCubeHD alpha beta x R).ncard : Nat) : Real) - R ^ d| ≤
        cubeCountConstantHD d beta * (R ^ (d - 1) + 1) := by
  let I := innerLatticeCubeHD beta x R
  let F := frequencyIndexCubeHD alpha beta x R
  let O := outerLatticeCubeHD beta x R
  have hfin := finite_inner_outer_latticeCubesHD beta x R
  have hIF : I ⊆ F := innerLatticeCubeHD_subset_frequencyIndexCubeHD alpha beta x R
  have hFO : F ⊆ O := frequencyIndexCubeHD_subset_outerLatticeCubeHD alpha beta x R
  have hFfinite : F.Finite := hfin.2.subset hFO
  have hIFcard : I.ncard ≤ F.ncard := Set.ncard_le_ncard hIF hFfinite
  have hFOcard : F.ncard ≤ O.ncard := Set.ncard_le_ncard hFO hfin.2
  have hIFcast : (I.ncard : Real) ≤ (F.ncard : Real) := by exact_mod_cast hIFcard
  have hFOcast : (F.ncard : Real) ≤ (O.ncard : Real) := by exact_mod_cast hFOcard
  have herr := inner_outer_latticeCube_count_error beta x R hbeta hR
  change |(I.ncard : Real) - R ^ d| ≤
      cubeCountConstantHD d beta * R ^ (d - 1) ∧
    |(O.ncard : Real) - R ^ d| ≤
      cubeCountConstantHD d beta * R ^ (d - 1) at herr
  simp only [abs_le] at herr
  have hB0 : 0 ≤ cubeBufferHD beta := by
    unfold cubeBufferHD
    exact div_nonneg (Internal.euclideanNormHD_nonneg beta) (by norm_num)
  have hC0 : 0 ≤ cubeCountConstantHD d beta := by
    unfold cubeCountConstantHD cubeCoordinateErrorHD
    positivity
  have hpow0 : 0 ≤ R ^ (d - 1) := pow_nonneg (by linarith) _
  refine ⟨hFfinite, ?_⟩
  rw [abs_le]
  constructor
  · calc
      -(cubeCountConstantHD d beta * (R ^ (d - 1) + 1)) ≤
          -(cubeCountConstantHD d beta * R ^ (d - 1)) := by
            nlinarith
      _ ≤ (I.ncard : Real) - R ^ d := herr.1.1
      _ ≤ (F.ncard : Real) - R ^ d := by linarith
  · calc
      (F.ncard : Real) - R ^ d ≤ (O.ncard : Real) - R ^ d := by linarith
      _ ≤ cubeCountConstantHD d beta * R ^ (d - 1) := herr.2.2
      _ ≤ cubeCountConstantHD d beta * (R ^ (d - 1) + 1) := by
        nlinarith

/- Restrict the injective range map to the indexed cube and
deduce equality of the two cardinalities. -/
private theorem range_frequencyIndexCubeHD_equiv {d : Nat}
    (alpha beta x : RealVec d) (R : Real)
    (hbeta : euclideanNormHD beta < 1 / 2) :
    (frequencyIndexCubeHD alpha beta x R).ncard =
      (modulatedLambdaSetHD alpha beta ∩ realCubeHD x R).ncard := by
  have hinj := modulatedLambdaHD_injective alpha beta hbeta
  have himage : modulatedLambdaHD alpha beta ''
      frequencyIndexCubeHD alpha beta x R =
      modulatedLambdaSetHD alpha beta ∩ realCubeHD x R := by
    ext y
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨⟨n, rfl⟩, hn⟩
    · rintro ⟨⟨n, rfl⟩, hn⟩
      exact ⟨n, hn, rfl⟩
  rw [← himage, Set.ncard_image_of_injective _ hinj]

end Internal

/- Transfer the indexed sandwich estimate through the
injective range/cardinality bridge. -/
theorem modulatedLambdaSetHD_countEstimate {d : Nat} (hd : 0 < d)
    (alpha beta : RealVec d) (hbeta : euclideanNormHD beta < 1 / 2) :
    HasCubicalCountEstimateOneHD (modulatedLambdaSetHD alpha beta)
      (cubeCountConstantHD d beta) := by
  have hB0 : 0 ≤ cubeBufferHD beta := by
    unfold cubeBufferHD
    exact div_nonneg (Internal.euclideanNormHD_nonneg beta) (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · unfold cubeCountConstantHD cubeCoordinateErrorHD
    positivity
  · intro x R hR
    have hidx := Internal.frequencyIndexCubeHD_count_error
      hd alpha beta x R hbeta hR
    have himage : modulatedLambdaHD alpha beta ''
        Internal.frequencyIndexCubeHD alpha beta x R =
        modulatedLambdaSetHD alpha beta ∩ realCubeHD x R := by
      ext y
      constructor
      · rintro ⟨n, hn, rfl⟩
        exact ⟨⟨n, rfl⟩, hn⟩
      · rintro ⟨⟨n, rfl⟩, hn⟩
        exact ⟨n, hn, rfl⟩
    rw [← himage]
    exact hidx.1.image _
  · intro x R hR
    have hidx := Internal.frequencyIndexCubeHD_count_error
      hd alpha beta x R hbeta hR
    have heq := Internal.range_frequencyIndexCubeHD_equiv
      alpha beta x R hbeta
    unfold realFrequencyCubeCountHD
    rw [← heq]
    exact hidx.2

namespace Internal

/- For radii below one, embed into the radius-one cube; for
larger radii use the quantitative estimate. -/
private theorem finite_modulatedLambdaSetHD_inter_realCubeHD {d : Nat}
    (hd : 0 < d) (alpha beta x : RealVec d) (R : Real)
    (hbeta : euclideanNormHD beta < 1 / 2) (hR : 0 ≤ R) :
    (modulatedLambdaSetHD alpha beta ∩ realCubeHD x R).Finite := by
  have hcount := modulatedLambdaSetHD_countEstimate hd alpha beta hbeta
  by_cases hRone : 1 ≤ R
  · exact hcount.finite_count x R hRone
  · have hRlt : R < 1 := lt_of_not_ge hRone
    apply (hcount.finite_count x 1 le_rfl).subset
    rintro y ⟨hyLambda, hyCube⟩
    refine ⟨hyLambda, ?_⟩
    intro i
    have hi := hyCube i
    constructor
    · exact hi.1
    · linarith [hi.2]

end Internal

/- Divide the quantitative count error by `R^d`; positivity of
the dimension makes the normalized error tend uniformly to zero. -/
theorem modulatedLambdaSetHD_uniformDensityOne {d : Nat} (hd : 0 < d)
    (alpha beta : RealVec d) (hbeta : euclideanNormHD beta < 1 / 2) :
    HasUniformCubicalDensityOneHD (modulatedLambdaSetHD alpha beta) := by
  let Lambda := modulatedLambdaSetHD alpha beta
  let C := cubeCountConstantHD d beta
  have hcount := modulatedLambdaSetHD_countEstimate hd alpha beta hbeta
  have hC0 : 0 ≤ C := hcount.constant_nonneg
  refine ⟨?_, ?_⟩
  · intro x R hR
    exact Internal.finite_modulatedLambdaSetHD_inter_realCubeHD
      hd alpha beta x R hbeta hR
  · intro epsilon hepsilon
    let R0 : Real := max 1 ((2 * C + 1) / epsilon)
    have hR0pos : 0 < R0 :=
      lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    refine ⟨R0, hR0pos, ?_⟩
    intro x R hRR0
    have hRone : 1 ≤ R := (le_max_left _ _).trans hRR0
    have hRpos : 0 < R := zero_lt_one.trans_le hRone
    have hratio : (2 * C + 1) / epsilon ≤ R :=
      (le_max_right _ _).trans hRR0
    have htwoC : 2 * C < epsilon * R := by
      have hle := (div_le_iff₀ hepsilon).mp hratio
      nlinarith
    have hqone : 1 ≤ R ^ (d - 1) := by
      have := pow_le_pow_right₀ hRone (Nat.zero_le (d - 1))
      simpa using this
    have hqpos : 0 < R ^ (d - 1) := zero_lt_one.trans_le hqone
    have hpowEq : R ^ d = R ^ (d - 1) * R := by
      rw [← pow_succ]
      congr 1
      omega
    have hpowPos : 0 < R ^ d := pow_pos hRpos _
    have herr := hcount.uniform_error x R hRone
    change |((realFrequencyCubeCountHD Lambda x R : Nat) : Real) - R ^ d| ≤
      C * (R ^ (d - 1) + 1) at herr
    have hstrict :
        |((realFrequencyCubeCountHD Lambda x R : Nat) : Real) - R ^ d| <
          epsilon * R ^ d := by
      calc
        |((realFrequencyCubeCountHD Lambda x R : Nat) : Real) - R ^ d| ≤
            C * (R ^ (d - 1) + 1) := herr
        _ ≤ C * (2 * R ^ (d - 1)) := by
          gcongr
          linarith
        _ = (2 * C) * R ^ (d - 1) := by ring
        _ < (epsilon * R) * R ^ (d - 1) :=
          mul_lt_mul_of_pos_right htwoC hqpos
        _ = epsilon * R ^ d := by rw [hpowEq]; ring
    change |((realFrequencyCubeCountHD Lambda x R : Nat) : Real) /
      R ^ d - 1| < epsilon
    rw [show ((realFrequencyCubeCountHD Lambda x R : Nat) : Real) /
        R ^ d - 1 =
        (((realFrequencyCubeCountHD Lambda x R : Nat) : Real) - R ^ d) /
          R ^ d by field_simp,
      abs_div, abs_of_pos hpowPos]
    exact (div_lt_iff₀ hpowPos).2 hstrict

end UniversalCompletenessHD
