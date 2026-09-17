import Theorem12.GenericAuxiliary
import Theorem12.SupportSlicing

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Theorem12.Internal

/- Proof idea: transparently take the integer floor after casting the rational and integer to reals. -/
def floorBeta (beta : ℚ) (j : ℤ) : ℤ :=
  ⌊(beta : ℝ) * (j : ℝ)⌋

/- Proof idea: use the complex integer power without replacing it by a natural power. -/
def intParity (m : ℤ) : ℂ :=
  (-1 : ℂ) ^ m

/- Proof idea: subtract the class of `(floorBeta beta j + q) * alpha` from `x`. -/
def uCoordClass (alpha : ℝ) (beta : ℚ) (x : AddCircle (1 : ℝ))
    (j q : ℤ) : AddCircle (1 : ℝ) :=
  x - ((((floorBeta beta j + q : ℤ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ))

/- Proof idea: apply the canonical period-one representative to `uCoordClass`. -/
def uCoord (alpha : ℝ) (beta : ℚ) (x : AddCircle (1 : ℝ))
    (j q : ℤ) : ℝ :=
  Theorem12.Generic.unitRep (uCoordClass alpha beta x j q)

/- Proof idea: use the real formula with the fixed floor and representative conventions. -/
def tCoord (alpha : ℝ) (beta : ℚ) (x : AddCircle (1 : ℝ))
    (j q : ℤ) : ℝ :=
  (beta : ℝ) * (uCoord alpha beta x j q + (j : ℝ)) - (floorBeta beta j : ℝ)

/- Proof idea: take the countable union of loci where one `tCoord` is an integer. -/
def sineBad (alpha : ℝ) (beta : ℚ) : Set (AddCircle (1 : ℝ)) :=
  {x | ∃ j q ell : ℤ, tCoord alpha beta x j q = (ell : ℝ)}

/- Proof idea: for each integer triple show the affine level set in the canonical representative is
empty or a singleton, prove it null, and take the countable union. -/
theorem sineBad_null (alpha : ℝ) (beta : ℚ) (hbeta0 : beta ≠ 0) :
    AddCircle.haarAddCircle (sineBad alpha beta) = 0 := by
  have hbetaR : (beta : ℝ) ≠ 0 := by exact_mod_cast hbeta0
  change AddCircle.haarAddCircle
    {x | ∃ j q ell : ℤ, tCoord alpha beta x j q = (ell : ℝ)} = 0
  rw [show {x | ∃ j q ell : ℤ, tCoord alpha beta x j q = (ell : ℝ)} =
      ⋃ j : ℤ, ⋃ q : ℤ, ⋃ ell : ℤ,
        {x | tCoord alpha beta x j q = (ell : ℝ)} by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]]
  apply measure_iUnion_null
  intro j
  apply measure_iUnion_null
  intro q
  apply measure_iUnion_null
  intro ell
  let a : AddCircle (1 : ℝ) :=
    ((((floorBeta beta j + q : ℤ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ))
  let c : ℝ := ((ell : ℝ) + (floorBeta beta j : ℝ)) / (beta : ℝ) - (j : ℝ)
  have hrep_null : AddCircle.haarAddCircle
      (Theorem12.Generic.unitRep ⁻¹' ({c} : Set ℝ)) = 0 := by
    rw [Theorem12.Generic.measure_unitRep_preimage ({c} : Set ℝ)
      (measurableSet_singleton c)]
    exact measure_mono_null Set.inter_subset_left
      (Real.volume_singleton (a := c))
  have htranslated_null : AddCircle.haarAddCircle
      ((fun x : AddCircle (1 : ℝ) => x - a) ⁻¹'
        (Theorem12.Generic.unitRep ⁻¹' ({c} : Set ℝ))) = 0 :=
    (Theorem12.Generic.measurePreserving_addCircle_sub a).preimage_null hrep_null
  apply measure_mono_null _ htranslated_null
  intro x hx
  change Theorem12.Generic.unitRep (x - a) ∈ ({c} : Set ℝ)
  rw [Set.mem_singleton_iff]
  simp only [Set.mem_setOf_eq] at hx
  dsimp only [tCoord, uCoord, uCoordClass] at hx
  dsimp only [a, c]
  rw [eq_sub_iff_add_eq, eq_div_iff hbetaR]
  linarith

/- Proof idea: use the literal source formula; the equivalent `q - tCoord` form remains a theorem. -/
def poleCoord (alpha : ℝ) (beta : ℚ) (x : AddCircle (1 : ℝ))
    (j q : ℤ) : ℝ :=
  ((floorBeta beta j + q : ℤ) : ℝ) -
    (beta : ℝ) * (uCoord alpha beta x j q + (j : ℝ))

/- Proof idea: unfold both coordinates and normalize the real ring expression. -/
theorem poleCoord_eq_q_sub_tCoord (alpha : ℝ) (beta : ℚ)
    (x : AddCircle (1 : ℝ)) (j q : ℤ) :
    poleCoord alpha beta x j q = (q : ℝ) - tCoord alpha beta x j q := by
  rw [poleCoord, tCoord]
  norm_num only [Int.cast_add]
  ring

/- Proof idea: rewrite `t` as `fract(beta*j) + beta*u` and combine the half-open bounds with
`abs beta < 1/2`, including the negative-beta case. -/
theorem abs_tCoord_lt_three_halves (alpha : ℝ) (beta : ℚ)
    (hbetaSmall : |(beta : ℝ)| < 1 / 2) (x : AddCircle (1 : ℝ)) (j q : ℤ) :
    |tCoord alpha beta x j q| < 3 / 2 := by
  let u := uCoord alpha beta x j q
  let y : ℝ := (beta : ℝ) * (j : ℝ)
  have hu := Theorem12.Generic.unitRep_mem_Ico
    (uCoordClass alpha beta x j q)
  have hu0 : 0 ≤ u := hu.1
  have hu1 : u < 1 := hu.2
  have habsu : |u| ≤ 1 := by
    rw [abs_of_nonneg hu0]
    exact hu1.le
  have hprod : |(beta : ℝ) * u| < 1 / 2 := by
    calc
      |(beta : ℝ) * u| = |(beta : ℝ)| * |u| := abs_mul _ _
      _ ≤ |(beta : ℝ)| * 1 :=
        mul_le_mul_of_nonneg_left habsu (abs_nonneg (beta : ℝ))
      _ < 1 / 2 := by simpa using hbetaSmall
  have hfract0 : 0 ≤ Int.fract y := Int.fract_nonneg y
  have hfract1 : Int.fract y < 1 := Int.fract_lt_one y
  have ht : tCoord alpha beta x j q = Int.fract y + (beta : ℝ) * u := by
    have hfloor : (floorBeta beta j : ℝ) + Int.fract y = y := by
      simpa only [floorBeta, y] using Int.floor_add_fract y
    dsimp only [tCoord, u, y] at hfloor ⊢
    linarith
  rw [ht, abs_lt]
  constructor <;> have habs := abs_le.mp hprod.le <;> linarith

/- Proof idea: rewrite `poleCoord - q` as `-tCoord` and invoke `abs_tCoord_lt_three_halves`. -/
theorem abs_poleCoord_sub_q_lt (alpha : ℝ) (beta : ℚ)
    (hbetaSmall : |(beta : ℝ)| < 1 / 2) (x : AddCircle (1 : ℝ)) (j q : ℤ) :
    |poleCoord alpha beta x j q - (q : ℝ)| < 3 / 2 := by
  rw [poleCoord_eq_q_sub_tCoord]
  simpa only [sub_sub_cancel_left, abs_neg] using
    abs_tCoord_lt_three_halves alpha beta hbetaSmall x j q

/- Proof idea: multiply the integer parity, real sine divided by real pi, and
the fixed slice value in the displayed factor order. -/
def residueCoord {dataAlpha : ℝ} {dataBeta : ℚ} {S : Set ℝ} {f : ℝ → ℂ}
    (data : PositiveInputData dataAlpha dataBeta S f) (alpha : ℝ) (beta : ℚ)
    (x : AddCircle (1 : ℝ)) (j q : ℤ) : ℂ :=
  intParity (floorBeta beta j) *
    ((Real.sin (Real.pi * tCoord alpha beta x j q) : ℝ) : ℂ) /
    (Real.pi : ℂ) * slice data j (uCoordClass alpha beta x j q)

/- Proof idea: if `q - t = ell`, rearrange to make `t` an integer and contradict `x ∉ sineBad`. -/
theorem poleCoord_not_int_of_not_sineBad (alpha : ℝ) (beta : ℚ)
    (x : AddCircle (1 : ℝ)) (hx : x ∉ sineBad alpha beta) (j q ell : ℤ) :
    poleCoord alpha beta x j q ≠ (ell : ℝ) := by
  intro hpole
  apply hx
  refine ⟨j, q, q - ell, ?_⟩
  rw [poleCoord_eq_q_sub_tCoord] at hpole
  norm_num only [Int.cast_sub]
  linarith

/- Proof idea: expand the residue, prove parity/sine/pi nonzero from `poleCoord_not_int_of_not_sineBad`, and cancel
those factors to expose the definition of `sliceSupport`. -/
theorem residueCoord_ne_zero_iff {alpha : ℝ} {beta : ℚ} {S : Set ℝ}
    {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f)
    (x : AddCircle (1 : ℝ)) (hx : x ∉ sineBad alpha beta) (j q : ℤ) :
    residueCoord data alpha beta x j q ≠ 0 ↔
      uCoordClass alpha beta x j q ∈ sliceSupport data j := by
  have ht_not_int : ∀ ell : ℤ, tCoord alpha beta x j q ≠ (ell : ℝ) := by
    intro ell ht
    apply hx
    exact ⟨j, q, ell, ht⟩
  have hsin : Real.sin (Real.pi * tCoord alpha beta x j q) ≠ 0 := by
    intro hzero
    rw [Real.sin_eq_zero_iff] at hzero
    obtain ⟨ell, hell⟩ := hzero
    apply ht_not_int ell
    nlinarith [Real.pi_pos]
  rw [sliceSupport, Set.mem_setOf_eq]
  constructor
  · intro hres hslice
    apply hres
    simp [residueCoord, hslice]
  · intro hslice
    unfold residueCoord
    apply mul_ne_zero
    · apply div_ne_zero
      · apply mul_ne_zero
        · exact zpow_ne_zero _ (by norm_num)
        · exact Complex.ofReal_ne_zero.mpr hsin
      · exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    · exact hslice

/- Proof idea: a nonzero product forces its slice factor nonzero; translate that implication into
the pointwise ENNReal `0/1` inequality without an off-bad hypothesis. -/
theorem residue_indicator_le_slice_indicator {alpha : ℝ} {beta : ℚ}
    {S : Set ℝ} {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f)
    (x : AddCircle (1 : ℝ)) (j q : ℤ) : open Classical in
    (if residueCoord data alpha beta x j q ≠ 0 then (1 : ENNReal) else 0) ≤
      if uCoordClass alpha beta x j q ∈ sliceSupport data j then 1 else 0 := by
  classical
  by_cases hs : uCoordClass alpha beta x j q ∈ sliceSupport data j
  · by_cases hres : residueCoord data alpha beta x j q = 0 <;> simp [hs, hres]
  · have hslice : slice data j (uCoordClass alpha beta x j q) = 0 := by
      simpa only [sliceSupport, Set.mem_setOf_eq, not_not] using hs
    have hres : residueCoord data alpha beta x j q = 0 := by
      simp [residueCoord, hslice]
    simp [hs, hres]

/- Proof idea: compare equal pole coordinates and the corresponding torus classes; rationality of
`beta` and irrationality of `alpha` force the combined labels, then `j` and `q`, to agree. -/
theorem poleCoord_injective (alpha : ℝ) (halpha : Irrational alpha)
    (beta : ℚ) (hbeta0 : beta ≠ 0) (x : AddCircle (1 : ℝ)) :
    Function.Injective
      (fun a : ℤ × ℤ => poleCoord alpha beta x a.1 a.2) := by
  have hbetaR : (beta : ℝ) ≠ 0 := by exact_mod_cast hbeta0
  rintro ⟨j₁, q₁⟩ ⟨j₂, q₂⟩ hp
  let ell₁ : ℤ := floorBeta beta j₁ + q₁
  let ell₂ : ℤ := floorBeta beta j₂ + q₂
  let r : ℚ := ((ell₁ - ell₂ : ℤ) : ℚ) / beta - ((j₁ - j₂ : ℤ) : ℚ)
  have hp' :
      (beta : ℝ) * ((uCoord alpha beta x j₁ q₁ - uCoord alpha beta x j₂ q₂) +
        ((j₁ - j₂ : ℤ) : ℝ)) = ((ell₁ - ell₂ : ℤ) : ℝ) := by
    unfold poleCoord at hp
    dsimp only [ell₁, ell₂]
    norm_num only [Int.cast_sub, Int.cast_add] at hp ⊢
    linarith
  have hdu :
      uCoord alpha beta x j₁ q₁ - uCoord alpha beta x j₂ q₂ = (r : ℝ) := by
    dsimp only [r]
    norm_num only [Rat.cast_sub, Rat.cast_div, Rat.cast_intCast]
    rw [eq_sub_iff_add_eq, eq_div_iff hbetaR]
    norm_num only [Int.cast_sub] at hp' ⊢
    linarith
  have hcircle :
      (((uCoord alpha beta x j₁ q₁ - uCoord alpha beta x j₂ q₂ +
          (((ell₁ - ell₂ : ℤ) : ℝ) * alpha)) : ℝ) : AddCircle (1 : ℝ)) = 0 := by
    unfold uCoord
    rw [AddCircle.coe_add, AddCircle.coe_sub]
    rw [Theorem12.Generic.coe_unitRep, Theorem12.Generic.coe_unitRep]
    change
      (x - (((ell₁ : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ))) -
          (x - (((ell₂ : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ))) +
          (((((ell₁ - ell₂ : ℤ) : ℝ) * alpha) : ℝ) : AddCircle (1 : ℝ)) = 0
    have hlabel : (((ell₁ - ell₂ : ℤ) : ℝ) * alpha) =
        (ell₁ : ℝ) * alpha - (ell₂ : ℝ) * alpha := by
      norm_num only [Int.cast_sub]
      ring
    rw [hlabel]
    rw [AddCircle.coe_sub]
    abel
  obtain ⟨n, hn⟩ :=
    (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp hcircle
  rw [Int.smul_one_eq_cast] at hn
  have hell : ell₁ = ell₂ := by
    by_contra hell
    have hirr : Irrational (((ell₁ - ell₂ : ℤ) : ℝ) * alpha) :=
      halpha.intCast_mul (sub_ne_zero.mpr hell)
    apply hirr
    refine ⟨(n : ℚ) - r, ?_⟩
    norm_num only [Rat.cast_sub, Rat.cast_intCast]
    linarith [hn, hdu]
  have hu : uCoord alpha beta x j₁ q₁ = uCoord alpha beta x j₂ q₂ := by
    unfold uCoord uCoordClass
    rw [show floorBeta beta j₁ + q₁ = floorBeta beta j₂ + q₂ by
      exact hell]
  have hjR : (j₁ : ℝ) = (j₂ : ℝ) := by
    have hpzero : (beta : ℝ) * (((j₁ - j₂ : ℤ) : ℝ)) = 0 := by
      simpa only [hu, sub_self, zero_add, hell, sub_self, Int.cast_zero]
        using hp'
    have hjzero : (((j₁ - j₂ : ℤ) : ℝ)) = 0 :=
      (mul_eq_zero.mp hpzero).resolve_left hbetaR
    norm_num only [Int.cast_sub] at hjzero
    linarith
  have hj : j₁ = j₂ := by exact_mod_cast hjR
  subst j₂
  have hq : q₁ = q₂ := by
    dsimp only [ell₁, ell₂] at hell
    omega
  subst q₂
  rfl

/- Proof idea: unfold `uCoordClass` and cancel the identical translated AddCircle class. -/
theorem uCoordClass_translate (alpha : ℝ) (beta : ℚ)
    (u : AddCircle (1 : ℝ)) (j q : ℤ) :
    let a : ℤ := floorBeta beta j + q
    uCoordClass alpha beta
      (u + ((((a : ℤ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ))) j q = u := by
  dsimp [uCoordClass]
  abel

/- Proof idea: unfold `uCoord` and rewrite the underlying class using `uCoordClass_translate`. -/
theorem uCoord_translate (alpha : ℝ) (beta : ℚ)
    (u : AddCircle (1 : ℝ)) (j q : ℤ) :
    let a : ℤ := floorBeta beta j + q
    uCoord alpha beta
      (u + ((((a : ℤ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ))) j q =
        Theorem12.Generic.unitRep u := by
  dsimp only
  rw [uCoord, uCoordClass_translate]

/- Proof idea: unfold `tCoord` and replace its representative with `uCoord_translate`. -/
theorem tCoord_translate (alpha : ℝ) (beta : ℚ)
    (u : AddCircle (1 : ℝ)) (j q : ℤ) :
    let a : ℤ := floorBeta beta j + q
    tCoord alpha beta
      (u + ((((a : ℤ) : ℝ) * alpha : ℝ) : AddCircle (1 : ℝ))) j q =
        (beta : ℝ) * (Theorem12.Generic.unitRep u + (j : ℝ)) -
          (floorBeta beta j : ℝ) := by
  dsimp only
  rw [tCoord, uCoord_translate]

end Theorem12.Internal
