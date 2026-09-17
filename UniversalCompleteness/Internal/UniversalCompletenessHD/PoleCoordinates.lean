import UniversalCompletenessHD.SupportSlicing

/-!
# Orbit, pole, residue, and exceptional-set coordinates

Orbit, phase, pole, residue, and
exceptional-set definitions are centralized in `Definitions.lean`.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators ComplexConjugate ENNReal Topology

namespace UniversalCompletenessHD.Internal

/- In positive dimension, zero beta contradicts rational
independence of `1 + alpha·beta, beta_1, ..., beta_d`. -/
theorem beta_ne_zero_of_nonresonant {d : Nat} (hd : 0 < d)
    (alpha beta : RealVec d) (hPole : PoleNonresonant alpha beta) :
    beta ≠ 0 := by
  intro hbeta
  let i : Fin d := ⟨0, hd⟩
  let q : Fin d → Rat := fun k ↦ if k = i then 1 else 0
  have hrel :
      ((0 : Rat) : Real) * (1 + dotReal alpha beta) +
          ∑ k, (q k : Real) * beta k = 0 := by
    simp [hbeta]
  have hzero := (hPole 0 q hrel).2 i
  simpa [q, i] using hzero

/- Apply floor-plus-fractional-part decomposition to
`beta·j` and expand the finite dot product. -/
theorem rawPhaseHD_eq_floor_add_reducedPhaseHD {d : Nat}
    (alpha beta : RealVec d) (x : Torus d) (j : IntVec d) (q : Int) :
    rawPhaseHD beta j (uCoordHD alpha beta x j q) =
      (floorBetaDot beta j : Real) + reducedPhaseHD alpha beta x j q := by
  rw [rawPhaseHD, reducedPhaseHD]
  have hfloor := Int.floor_add_fract (dotReal beta (intCast j))
  rw [floorBetaDot]
  calc
    dotReal beta
        (torusToCubeHD (uCoordHD alpha beta x j q) + intCast j) =
        dotReal beta (torusToCubeHD (uCoordHD alpha beta x j q)) +
          dotReal beta (intCast j) := by
            simp only [dotReal, Pi.add_apply, mul_add,
              Finset.sum_add_distrib]
    _ = (↑⌊dotReal beta (intCast j)⌋ : Real) +
          (Int.fract (dotReal beta (intCast j)) +
            dotReal beta (torusToCubeHD (uCoordHD alpha beta x j q))) := by
          linarith

/- Translate sine by the integer floor and retain the exact
complex parity factor. -/
theorem sin_rawPhaseHD_eq_intParity_mul_sin_reducedPhaseHD {d : Nat}
    (alpha beta : RealVec d) (x : Torus d) (j : IntVec d) (q : Int) :
    ((Real.sin (Real.pi * rawPhaseHD beta j
        (uCoordHD alpha beta x j q)) : Real) : Complex) =
      intParityHD (floorBetaDot beta j) *
        ((Real.sin (Real.pi * reducedPhaseHD alpha beta x j q) : Real) : Complex) := by
  rw [rawPhaseHD_eq_floor_add_reducedPhaseHD]
  have hs := Real.sin_add_int_mul_pi
    (Real.pi * reducedPhaseHD alpha beta x j q) (floorBetaDot beta j)
  have hangle :
      Real.pi * ((floorBetaDot beta j : Real) +
          reducedPhaseHD alpha beta x j q) =
        Real.pi * reducedPhaseHD alpha beta x j q +
          (floorBetaDot beta j : Real) * Real.pi := by ring
  rw [hangle]
  rw [hs]
  simp [intParityHD]

/- Normalize the pole after substituting
`ell = floor(beta·j) + q`. -/
theorem poleCoordHD_eq_q_sub_reducedPhaseHD {d : Nat}
    (alpha beta : RealVec d) (x : Torus d) (j : IntVec d) (q : Int) :
    poleCoordHD alpha beta x j q =
      (q : Real) - reducedPhaseHD alpha beta x j q := by
  rw [poleCoordHD, rawPhaseHD_eq_floor_add_reducedPhaseHD]
  simp only [ellIndexHD, Int.cast_add]
  ring

/- A nonzero scalar product has a nonzero cube-slice factor;
no sine nonvanishing premise is needed. -/
theorem residueCoordHD_ne_zero_imp_cubeSlice_ne_zero {d : Nat}
    {dataAlpha dataBeta : RealVec d} {S : Set (RealVec d)}
    {f : RealVec d → Complex} (data : PositiveInputDataHD dataAlpha dataBeta S f)
    (alpha beta : RealVec d) (x : Torus d) (j : IntVec d) (q : Int)
    (hres : residueCoordHD data alpha beta x j q ≠ 0) :
    cubeSlice data j (uCoordHD alpha beta x j q) ≠ 0 := by
  intro hslice
  apply hres
  simp [residueCoordHD, hslice]

/- Turn the total residue-to-slice implication into an
ENNReal indicator inequality. -/
theorem residue_indicator_le_slice_indicatorHD {d : Nat}
    {dataAlpha dataBeta : RealVec d} {S : Set (RealVec d)}
    {f : RealVec d → Complex} (data : PositiveInputDataHD dataAlpha dataBeta S f)
    (alpha beta : RealVec d) (x : Torus d) (j : IntVec d) (q : Int) :
    (if residueCoordHD data alpha beta x j q ≠ 0
      then (1 : ENNReal) else 0) ≤
    (if cubeSlice data j (uCoordHD alpha beta x j q) ≠ 0
      then (1 : ENNReal) else 0) := by
  classical
  by_cases hslice : cubeSlice data j (uCoordHD alpha beta x j q) = 0
  · have hres : residueCoordHD data alpha beta x j q = 0 := by
      simp [residueCoordHD, hslice]
    simp [hres, hslice]
  · split <;> simp

/- Bound the fractional part by one and the representative
dot product coordinatewise by `sum |beta_i|`. -/
theorem abs_poleCoordHD_sub_q_le {d : Nat} (alpha beta : RealVec d)
    (x : Torus d) (j : IntVec d) (q : Int) :
    |poleCoordHD alpha beta x j q - (q : Real)| ≤
      poleShiftConstantHD beta := by
  rw [poleCoordHD_eq_q_sub_reducedPhaseHD]
  simp only [sub_sub_cancel_left, abs_neg]
  let u : RealVec d := torusToCubeHD (uCoordHD alpha beta x j q)
  have hu : u ∈ iocUnitCubeHD d := by
    exact (torusIocEquivHD d (uCoordHD alpha beta x j q)).property
  have hu_abs (i : Fin d) : |u i| ≤ 1 := by
    have hui := hu i
    change u i ∈ Set.Ioc (0 : Real) (0 + 1) at hui
    rw [abs_of_nonneg hui.1.le]
    norm_num at hui
    exact hui.2
  have hdot : |dotReal beta u| ≤ ∑ i, |beta i| := by
    calc
      |dotReal beta u| ≤ ∑ i, |beta i * u i| := by
        exact Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, |beta i| * |u i| := by
        congr 1
        funext i
        exact abs_mul _ _
      _ ≤ ∑ i, |beta i| := by
        apply Finset.sum_le_sum
        intro i hi
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left (hu_abs i) (abs_nonneg (beta i))
  have hfract :
      |Int.fract (dotReal beta (intCast j))| ≤ 1 := by
    rw [abs_of_nonneg (Int.fract_nonneg _)]
    exact (Int.fract_lt_one _).le
  rw [reducedPhaseHD, poleShiftConstantHD]
  change |Int.fract (dotReal beta (intCast j)) + dotReal beta u| ≤
    1 + ∑ i, |beta i|
  exact (abs_add_le _ _).trans (add_le_add hfract hdot)

/- Evaluate the continuous functional on a standard basis
vector in a nonzero coordinate. -/
private theorem betaLinearMapHD_ne_zero {d : Nat} (beta : RealVec d)
    (hbeta : beta ≠ 0) :
    betaLinearMapHD beta ≠ 0 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, beta i ≠ 0 := by
    by_contra h
    push_neg at h
    apply hbeta
    funext k
    exact h k
  intro hmap
  have heval := congrArg
    (fun L : RealVec d →L[Real] Real ↦
      L (Pi.single i (1 : Real))) hmap
  have hsum : ∑ k, beta k *
      (Pi.single i (1 : Real) : RealVec d) k = beta i := by
    simp [Pi.single_apply]
  simp only [betaLinearMapHD, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul, ContinuousLinearMap.zero_apply] at heval
  rw [hsum] at heval
  exact hi heval

/- Identify the level set with a strict affine subspace and
apply `Measure.addHaar_affineSubspace`. -/
theorem affineBetaHyperplane_null {d : Nat} (beta : RealVec d)
    (hbeta : beta ≠ 0) (c : Real) :
    volume {u : RealVec d | dotReal beta u = c} = 0 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, beta i ≠ 0 := by
    by_contra h
    push_neg at h
    apply hbeta
    funext k
    exact h k
  let u0 : RealVec d := fun k ↦ if k = i then c / beta i else 0
  let A : AffineSubspace Real (RealVec d) :=
    AffineSubspace.mk' u0
      (LinearMap.ker (betaLinearMapHD beta).toLinearMap)
  have hmap (u : RealVec d) :
      betaLinearMapHD beta u = dotReal beta u := by
    simp [betaLinearMapHD, dotReal]
  have hu0 : dotReal beta u0 = c := by
    rw [show dotReal beta u0 = beta i * (c / beta i) by
      simp [dotReal, u0]]
    exact mul_div_cancel₀ c hi
  have hcarrier : {u : RealVec d | dotReal beta u = c} = (A : Set (RealVec d)) := by
    ext u
    simp only [Set.mem_setOf_eq, SetLike.mem_coe]
    rw [show u ∈ A ↔ u - u0 ∈
        LinearMap.ker (betaLinearMapHD beta).toLinearMap by
      rfl]
    rw [LinearMap.mem_ker]
    change dotReal beta u = c ↔ betaLinearMapHD beta (u - u0) = 0
    rw [hmap]
    simp only [dotReal, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    change dotReal beta u = c ↔ dotReal beta u - dotReal beta u0 = 0
    rw [hu0]
    constructor <;> intro h <;> linarith
  rw [hcarrier]
  apply Measure.addHaar_affineSubspace volume A
  intro htop
  apply betaLinearMapHD_ne_zero beta hbeta
  ext u
  have hu : u ∈ LinearMap.ker (betaLinearMapHD beta).toLinearMap := by
    have hdir := congrArg AffineSubspace.direction htop
    have : A.direction = ⊤ := by simpa using hdir
    have hker : LinearMap.ker (betaLinearMapHD beta).toLinearMap = ⊤ := by
      simpa [A] using this
    rw [hker]
    exact Submodule.mem_top
  exact hu

/- Transport ambient hyperplane nullity through the native
torus representative and its restricted target measure. -/
theorem affineBetaHyperplane_torus_preimage_null {d : Nat}
    (beta : RealVec d) (hbeta : beta ≠ 0) (c : Real) :
    volume ((torusToCubeHD : Torus d → RealVec d) ⁻¹'
      {u : RealVec d | dotReal beta u = c}) = 0 := by
  let mu : Measure (Torus d) := volume
  change mu ((torusToCubeHD : Torus d → RealVec d) ⁻¹'
    {u : RealVec d | dotReal beta u = c}) = 0
  have hnull : (volume.restrict (iocUnitCubeHD d))
      {u : RealVec d | dotReal beta u = c} = 0 :=
    le_antisymm
      (calc
        (volume.restrict (iocUnitCubeHD d))
              {u : RealVec d | dotReal beta u = c} ≤
            volume {u : RealVec d | dotReal beta u = c} :=
          Measure.restrict_le_self _
        _ = 0 := affineBetaHyperplane_null beta hbeta c)
      (bot_le)
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
  rw [hmunu]
  exact (measurePreserving_torusToCubeHD_ambient d).preimage_null hnull

/- Express each fixed bad event as a translated beta
hyperplane and take the countable union. -/
theorem sineBadHD_null (P : Params) :
    volume (sineBadHD P.alpha P.beta) = 0 := by
  have hbeta : P.beta ≠ 0 :=
    beta_ne_zero_of_nonresonant P.hd P.alpha P.beta P.pole_nonresonant
  change volume {x | ∃ (j : IntVec P.d) (ell k : Int),
    (ell : Real) - rawPhaseHD P.beta j
      (uOrbitHD P.alpha x ell) = (k : Real)} = 0
  rw [show {x | ∃ (j : IntVec P.d) (ell k : Int),
      (ell : Real) - rawPhaseHD P.beta j
        (uOrbitHD P.alpha x ell) = (k : Real)} =
      ⋃ j : IntVec P.d, ⋃ ell : Int, ⋃ k : Int,
        {x | (ell : Real) - rawPhaseHD P.beta j
          (uOrbitHD P.alpha x ell) = (k : Real)} by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]]
  apply measure_iUnion_null
  intro j
  apply measure_iUnion_null
  intro ell
  apply measure_iUnion_null
  intro k
  let a : Torus P.d := ell • alphaTorusHD P.alpha
  let c : Real := (ell : Real) - (k : Real) -
    dotReal P.beta (intCast j)
  have hpre : volume
      ((torusToCubeHD : Torus P.d → RealVec P.d) ⁻¹'
        {u : RealVec P.d | dotReal P.beta u = c}) = 0 :=
    affineBetaHyperplane_torus_preimage_null P.beta hbeta c
  have htranslated : volume
      ((fun x : Torus P.d ↦ x - a) ⁻¹'
        ((torusToCubeHD : Torus P.d → RealVec P.d) ⁻¹'
          {u : RealVec P.d | dotReal P.beta u = c})) = 0 :=
    (measurePreserving_sub_right volume a).preimage_null hpre
  apply measure_mono_null _ htranslated
  intro x hx
  change dotReal P.beta (torusToCubeHD (x - a)) = c
  have hsplit :
      rawPhaseHD P.beta j (uOrbitHD P.alpha x ell) =
        dotReal P.beta (torusToCubeHD (uOrbitHD P.alpha x ell)) +
          dotReal P.beta (intCast j) := by
    simp only [rawPhaseHD, dotReal, Pi.add_apply, mul_add,
      Finset.sum_add_distrib]
  change (ell : Real) - rawPhaseHD P.beta j
    (uOrbitHD P.alpha x ell) = (k : Real) at hx
  rw [hsplit] at hx
  change dotReal P.beta
    (torusToCubeHD (uOrbitHD P.alpha x ell)) = c
  dsimp only [c]
  linarith

/- Instantiate the existential bad-set definition with the
row and integer pole supplied by an assumed collision. -/
theorem poleCoordHD_not_int_of_not_sineBad {d : Nat}
    (alpha beta : RealVec d) (x : Torus d)
    (hx : x ∉ sineBadHD alpha beta) (j : IntVec d) (q r : Int) :
    poleCoordHD alpha beta x j q ≠ (r : Real) := by
  intro hpole
  apply hx
  refine ⟨j, ellIndexHD beta j q, r, ?_⟩
  unfold poleCoordHD at hpole
  simpa only [uCoordHD] using hpole

/- Lift coordinatewise quotient equality to one integer
vector, retaining the leading minus sign. -/
private theorem uOrbit_representative_differenceHD {d : Nat}
    (alpha : RealVec d) (x : Torus d) (ell ell' : Int) :
    ∃ z : IntVec d,
      torusToCubeHD (uOrbitHD alpha x ell) -
          torusToCubeHD (uOrbitHD alpha x ell') =
        -((((ell - ell' : Int) : Real)) • alpha) + intCast z := by
  classical
  have hrep (u : Torus d) (i : Fin d) :
      ((torusToCubeHD u i : Real) : UnitAddCircle) = u i := by
    have h := congrFun
      (IntegerFrequenciesHD.Internal.cubeToTorusHD_torusToCubeHD u) i
    change ((IntegerFrequenciesHD.Internal.torusToCubeHD u i : Real) :
      UnitAddCircle) = u i
    exact h
  have hex : ∀ i : Fin d, ∃ z : Int,
      (z : Real) =
        torusToCubeHD (uOrbitHD alpha x ell) i -
          torusToCubeHD (uOrbitHD alpha x ell') i +
            (((ell - ell' : Int) : Real) * alpha i) := by
    intro i
    let y : Real := torusToCubeHD (uOrbitHD alpha x ell) i -
      torusToCubeHD (uOrbitHD alpha x ell') i +
        (((ell - ell' : Int) : Real) * alpha i)
    have hcircle : (y : UnitAddCircle) = 0 := by
      dsimp only [y]
      rw [AddCircle.coe_add, AddCircle.coe_sub, hrep, hrep]
      rw [← zsmul_eq_mul (alpha i) (ell - ell'),
        AddCircle.coe_zsmul]
      unfold uOrbitHD alphaTorusHD
      simp only [Pi.sub_apply, Pi.smul_apply]
      simp only [sub_eq_add_neg, add_smul, neg_smul, one_smul]
      abel
    obtain ⟨z, hz⟩ :=
      (AddCircle.coe_eq_zero_iff (p := (1 : Real))).mp hcircle
    refine ⟨z, ?_⟩
    rw [Int.smul_one_eq_cast] at hz
    exact hz
  choose z hz using hex
  refine ⟨z, funext fun i ↦ ?_⟩
  have hzi := hz i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply, Pi.smul_apply,
    smul_eq_mul, intCast]
  linarith

/- Preserve the same representative-lift witness in both
the vector equation and the scalar collision equation. -/
private theorem poleCoordHD_collision_relation {d : Nat}
    (alpha beta : RealVec d) (x : Torus d)
    (j j' : IntVec d) (q q' : Int)
    (hcollision : poleCoordHD alpha beta x j q =
      poleCoordHD alpha beta x j' q') :
    let ell : Int := ellIndexHD beta j q
    let ell' : Int := ellIndexHD beta j' q'
    ∃ z : IntVec d,
      torusToCubeHD (uOrbitHD alpha x ell) -
          torusToCubeHD (uOrbitHD alpha x ell') =
          -((((ell - ell' : Int) : Real)) • alpha) + intCast z ∧
        (((ell - ell' : Int) : Real) * (1 + dotReal alpha beta)) =
          dotIntReal (j - j' + z) beta := by
  dsimp only
  let ell : Int := ellIndexHD beta j q
  let ell' : Int := ellIndexHD beta j' q'
  have hc := hcollision
  change (ell : Real) -
      rawPhaseHD beta j (uOrbitHD alpha x ell) =
    (ell' : Real) -
      rawPhaseHD beta j' (uOrbitHD alpha x ell') at hc
  obtain ⟨z, hz⟩ :=
    uOrbit_representative_differenceHD alpha x ell ell'
  refine ⟨z, hz, ?_⟩
  let u : RealVec d := torusToCubeHD (uOrbitHD alpha x ell)
  let u' : RealVec d := torusToCubeHD (uOrbitHD alpha x ell')
  have hdot_add (v w : RealVec d) :
      dotReal beta (v + w) = dotReal beta v + dotReal beta w := by
    simp only [dotReal, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  have hdot_sub (v w : RealVec d) :
      dotReal beta (v - w) = dotReal beta v - dotReal beta w := by
    simp only [dotReal, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  have hdot_neg (v : RealVec d) :
      dotReal beta (-v) = -dotReal beta v := by
    simp only [dotReal, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
  have hdot_smul (r : Real) (v : RealVec d) :
      dotReal beta (r • v) = r * dotReal beta v := by
    simp only [dotReal, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    congr 1
    funext i
    ring
  have hdot_int (v : IntVec d) :
      dotReal beta (intCast v) = dotIntReal v beta := by
    simp only [dotReal, dotIntReal, intCast]
    congr 1
    funext i
    ring
  change (ell : Real) - dotReal beta (u + intCast j) =
    (ell' : Real) - dotReal beta (u' + intCast j') at hc
  have hc' : (((ell - ell' : Int) : Real)) =
      (dotReal beta u - dotReal beta u') +
        (dotIntReal j beta - dotIntReal j' beta) := by
    rw [hdot_add, hdot_add, hdot_int, hdot_int] at hc
    norm_num only [Int.cast_sub]
    linarith
  have hz' := congrArg (dotReal beta) hz
  change dotReal beta (u - u') =
      dotReal beta (-((((ell - ell' : Int) : Real)) • alpha) +
        intCast z) at hz'
  rw [hdot_sub, hdot_add, hdot_neg, hdot_smul, hdot_int] at hz'
  have hsymm : dotReal alpha beta = dotReal beta alpha := by
    simp only [dotReal]
    congr 1
    funext i
    ring
  have hjz : dotIntReal (j - j' + z) beta =
      (dotIntReal j beta - dotIntReal j' beta) + dotIntReal z beta := by
    simp only [dotIntReal, Pi.sub_apply, Pi.add_apply, Int.cast_add,
      Int.cast_sub, add_mul, sub_mul, Finset.sum_add_distrib,
      Finset.sum_sub_distrib]
  change (((ell - ell' : Int) : Real) * (1 + dotReal alpha beta)) =
    dotIntReal (j - j' + z) beta
  rw [hjz, hsymm]
  norm_num only [Int.cast_sub] at hc' hz' ⊢
  nlinarith

end UniversalCompletenessHD.Internal

namespace UniversalCompletenessHD.PoleNonresonant

/- Specialize rational independence to integer-cast
coefficients and normalize casts. -/
private theorem integer_specialization {d : Nat} {alpha beta : RealVec d}
    (hPole : PoleNonresonant alpha beta) (a : Int) (h : IntVec d)
    (hrel : (a : Real) * (1 + dotReal alpha beta) = dotIntReal h beta) :
    a = 0 ∧ h = 0 := by
  let q0 : Rat := (a : Rat)
  let q : Fin d → Rat := fun i ↦ -(h i : Rat)
  have hzero : (q0 : Real) * (1 + dotReal alpha beta) +
      ∑ i, (q i : Real) * beta i = 0 := by
    dsimp only [q0, q]
    norm_num only [Rat.cast_intCast, Rat.cast_neg]
    rw [hrel]
    simp only [dotIntReal]
    simp_rw [neg_mul]
    rw [Finset.sum_neg_distrib]
    ring
  have hs := hPole q0 q hzero
  dsimp only [q0, q] at hs
  constructor
  · exact_mod_cast hs.1
  · funext i
    have hi := hs.2 i
    have hi' : (h i : Rat) = 0 := neg_eq_zero.mp hi
    exact_mod_cast hi'

end UniversalCompletenessHD.PoleNonresonant

namespace UniversalCompletenessHD.Internal

/- Use the retained lift witness and integer specialization to
recover `ell`, then `z`, then `j`, and finally `q`. -/
theorem poleCoordHD_injective (P : Params) (x : Torus P.d) :
    Function.Injective (fun a : IntVec P.d × Int ↦
      poleCoordHD P.alpha P.beta x a.1 a.2) := by
  rintro ⟨j, q⟩ ⟨j', q'⟩ hcollision
  let ell : Int := ellIndexHD P.beta j q
  let ell' : Int := ellIndexHD P.beta j' q'
  obtain ⟨z, hrep, hrel⟩ :=
    poleCoordHD_collision_relation P.alpha P.beta x j j' q q' hcollision
  change torusToCubeHD (uOrbitHD P.alpha x ell) -
      torusToCubeHD (uOrbitHD P.alpha x ell') =
        -((((ell - ell' : Int) : Real)) • P.alpha) + intCast z at hrep
  have hspecial :=
    UniversalCompletenessHD.PoleNonresonant.integer_specialization
      P.pole_nonresonant (ell - ell') (j - j' + z) hrel
  have hell : ell = ell' := sub_eq_zero.mp hspecial.1
  have hrep' := hrep
  rw [hell] at hrep'
  simp only [sub_self, Int.cast_zero, zero_smul, neg_zero, zero_add] at hrep'
  have hz : z = 0 := by
    funext i
    have hzi := congrFun hrep' i
    simp only [Pi.sub_apply, sub_self, intCast, Pi.zero_apply] at hzi
    change z i = (0 : Int)
    exact_mod_cast hzi.symm
  have hjsub : j - j' = 0 := by
    simpa only [hz, add_zero] using hspecial.2
  have hj : j = j' := sub_eq_zero.mp hjsub
  subst j'
  have hq : q = q' := by
    dsimp only [ell, ell', ellIndexHD] at hell
    omega
  subst q'
  rfl

/- Off the bad set the sine factor is nonzero, so residue
nonvanishing is equivalent to slice nonvanishing. -/
theorem residueCoordHD_ne_zero_iff {d : Nat} {alpha beta : RealVec d}
    {S : Set (RealVec d)} {f : RealVec d → Complex}
    (data : PositiveInputDataHD alpha beta S f) (x : Torus d)
    (hx : x ∉ sineBadHD alpha beta) (j : IntVec d) (q : Int) :
    residueCoordHD data alpha beta x j q ≠ 0 ↔
      cubeSlice data j (uCoordHD alpha beta x j q) ≠ 0 := by
  constructor
  · exact residueCoordHD_ne_zero_imp_cubeSlice_ne_zero
      data alpha beta x j q
  · intro hslice
    have hraw_not_int : ∀ r : Int,
        rawPhaseHD beta j (uCoordHD alpha beta x j q) ≠ (r : Real) := by
      intro r hraw
      apply poleCoordHD_not_int_of_not_sineBad alpha beta x hx j q
        (ellIndexHD beta j q - r)
      unfold poleCoordHD
      norm_num only [Int.cast_sub]
      linarith
    have hsin :
        Real.sin (Real.pi * rawPhaseHD beta j
          (uCoordHD alpha beta x j q)) ≠ 0 := by
      intro hzero
      rw [Real.sin_eq_zero_iff] at hzero
      obtain ⟨r, hr⟩ := hzero
      apply hraw_not_int r
      nlinarith [Real.pi_pos]
    unfold residueCoordHD
    exact mul_ne_zero
      (div_ne_zero (Complex.ofReal_ne_zero.mpr hsin)
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) hslice

/- Unfold orbit and row-index definitions. -/
theorem uCoordHD_translate {d : Nat} (alpha beta : RealVec d)
    (x : Torus d) (j : IntVec d) (q : Int) :
    uCoordHD alpha beta x j q =
      x - ellIndexHD beta j q • alphaTorusHD alpha := by
  rfl

/- Substitute the translated base point and normalize the
additive group expression. -/
theorem uCoordHD_add_ellIndex_smul {d : Nat} (alpha beta : RealVec d)
    (u : Torus d) (j : IntVec d) (q : Int) :
    uCoordHD alpha beta
        (u + ellIndexHD beta j q • alphaTorusHD alpha) j q = u := by
  rw [uCoordHD_translate]
  abel

/- Expand `ellIndexHD = floorBetaDot + q` and move the
`q`-translation into the torus base point with the minus sign shown above. -/
theorem uCoordHD_eq_uCoordHD_sub_q_smul_zero {d : Nat}
    (alpha beta : RealVec d) (x : Torus d) (j : IntVec d) (q : Int) :
    uCoordHD alpha beta x j q =
      uCoordHD alpha beta (x - q • alphaTorusHD alpha) j 0 := by
  rw [uCoordHD_translate, uCoordHD_translate]
  unfold ellIndexHD
  simp only [add_zero]
  rw [add_smul]
  abel

end UniversalCompletenessHD.Internal
