import IntegerFrequenciesHD.CubeTorusBridge
import SpectralGapsPrelim.BirkhoffPointwise.Basic
import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# Product-torus rotation ergodicity

Ergodicity is obtained directly from product Fourier coefficients and the
multitorus Hilbert basis, followed by the proved inclusive two-sided
Birkhoff adapter. No dense-orbit theorem is used.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology ComplexConjugate

local instance : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs
    (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs
    (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace IntegerFrequenciesHD.Internal

/- Expand the product character at `alphaTorus alpha` and use
the finite product-of-exponentials identity to recover the exponential of the
finite dot product. -/
theorem mFourier_alphaTorus_eq_exp_dot {d : Nat} (alpha : RealVec d)
    (n : IntVec d) :
    UnitAddTorus.mFourier n (alphaTorus alpha) =
      Complex.exp ((((2 * Real.pi : Real) : Complex) * Complex.I) *
        (dotIntReal n alpha : Complex)) := by
  simp only [UnitAddTorus.mFourier, alphaTorus, ContinuousMap.coe_mk,
    fourier_coe_apply, ← Complex.exp_sum, dotIntReal,
    Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_intCast]
  congr 1
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/- An exponential equal to one forces the real phase to be an
integer, contradicting total nonresonance from `nonresonant_dotIntReal`. -/
theorem mFourier_alphaTorus_ne_one {d : Nat} {alpha : RealVec d}
    (hAlpha : RationallyIndependentWithOne alpha)
    (n : IntVec d) (hn : n ≠ 0) :
    UnitAddTorus.mFourier n (alphaTorus alpha) ≠ 1 := by
  intro h
  rw [mFourier_alphaTorus_eq_exp_dot] at h
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp h
  have hK : ((((2 * Real.pi : Real) : Complex) * Complex.I)) ≠ 0 := by
    apply mul_ne_zero
    · exact_mod_cast
        (mul_ne_zero (by norm_num : (2 : Real) ≠ 0) Real.pi_ne_zero)
    · exact Complex.I_ne_zero
  have hc :
      ((((2 * Real.pi : Real) : Complex) * Complex.I)) *
          (dotIntReal n alpha : Complex) =
        ((((2 * Real.pi : Real) : Complex) * Complex.I)) * (m : Complex) := by
    calc
      _ = (m : Complex) * (2 * (Real.pi : Complex) * Complex.I) := hm
      _ = _ := by
        push_cast
        ring
  have hcast : (dotIntReal n alpha : Complex) = (m : Complex) :=
    mul_left_cancel₀ hK hc
  apply nonresonant_dotIntReal hAlpha n hn m
  exact_mod_cast hcast

/- Unfold the total coefficient integral, change variables by
the measure-preserving translation, and normalize `mFourier_add` and
`mFourier_neg`. No integrability premise is required. -/
theorem mFourierCoeff_translate_add {d : Nat} (F : Torus d → Complex)
    (a : Torus d) (n : IntVec d) :
    UnitAddTorus.mFourierCoeff (fun x => F (x + a)) n =
      UnitAddTorus.mFourier n a * UnitAddTorus.mFourierCoeff F n := by
  rw [UnitAddTorus.mFourierCoeff, UnitAddTorus.mFourierCoeff]
  have hchange := (measurePreserving_torus_add a).integral_comp
    (Homeomorph.addRight a).measurableEmbedding
    (fun y : Torus d => UnitAddTorus.mFourier (-n) (y - a) • F y)
  have hchange' :
      (∫ x : Torus d, UnitAddTorus.mFourier (-n) x • F (x + a) ∂volume) =
        ∫ y : Torus d, UnitAddTorus.mFourier (-n) (y - a) • F y ∂volume := by
    simpa only [add_sub_cancel_right] using hchange
  rw [hchange']
  change (∫ y : Torus d, UnitAddTorus.mFourier (-n) (y - a) • F y ∂volume) =
    UnitAddTorus.mFourier n a •
      ∫ t : Torus d, UnitAddTorus.mFourier (-n) t • F t ∂volume
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards with y
  rw [smul_smul]
  congr 1
  change (∏ i, fourier (-(n i)) (y i - a i)) =
    (∏ i, fourier (n i) (a i)) * (∏ i, fourier (-(n i)) (y i))
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  simp only [sub_eq_add_neg, fourier_apply, smul_add, smul_neg,
    neg_smul, neg_neg, AddCircle.toCircle_add, Circle.coe_mul]
  rw [mul_comm]

/- Convert the raw representative to `Lp Complex 2 volume`,
identify every `mFourierBasis` coordinate with the raw coefficient, use
injectivity of the basis representation, then return to raw a.e. equality. -/
theorem ae_zero_of_memLp_two_mFourierCoeff_zero {d : Nat}
    (F : Torus d → Complex) (hF : MemLp F 2 volume)
    (hcoeff : ∀ n : IntVec d, UnitAddTorus.mFourierCoeff F n = 0) :
    F =ᵐ[volume] 0 := by
  let f2 : Lp Complex 2 (volume : Measure (Torus d)) := hF.toLp F
  have hrepr : UnitAddTorus.mFourierBasis.repr f2 = 0 := by
    ext n
    rw [UnitAddTorus.mFourierBasis_repr]
    change (∫ t : Torus d, UnitAddTorus.mFourier (-n) t • f2 t ∂volume) = 0
    calc
      _ = ∫ t : Torus d, UnitAddTorus.mFourier (-n) t • F t ∂volume := by
        apply integral_congr_ae
        filter_upwards [hF.coeFn_toLp] with t ht
        rw [ht]
      _ = UnitAddTorus.mFourierCoeff F n := rfl
      _ = 0 := hcoeff n
  have hf2 : f2 = 0 := UnitAddTorus.mFourierBasis.repr.injective (by simpa using hrepr)
  have hcoe : (f2 : Torus d → Complex) =ᵐ[volume] 0 := by
    rw [hf2]
    exact Lp.coeFn_zero ℂ 2 volume
  exact hF.coeFn_toLp.symm.trans hcoe

/- Center the complex indicator of a strictly invariant
measurable set. Translation multiplies each coefficient by `mFourier n a`;
nonresonance kills nonzero modes and centering kills the zero mode. Apply the
L2 uniqueness adapter and indicator idempotence to obtain `PreErgodic`. -/
theorem preErgodic_torus_add_of_mFourier_ne_one {d : Nat} (a : Torus d)
    (ha : ∀ n : IntVec d, n ≠ 0 → UnitAddTorus.mFourier n a ≠ 1) :
    PreErgodic (fun x : Torus d => x + a) volume := by
  refine ⟨?_⟩
  intro s hs hinv
  let G : Torus d → Complex := s.indicator (fun _ => 1)
  let c : Complex := ∫ x : Torus d, G x ∂volume
  let F : Torus d → Complex := fun x => G x - c
  have hG : MemLp G 2 volume := by
    exact memLp_indicator_const 2 hs 1
      (Or.inr (measure_lt_top volume s).ne)
  have hF : MemLp F 2 volume := hG.sub (memLp_const c)
  have hFinv : (fun x : Torus d => F (x + a)) = F := by
    funext x
    have hmem : x + a ∈ s ↔ x ∈ s := by
      change x ∈ (fun y : Torus d => y + a) ⁻¹' s ↔ x ∈ s
      rw [hinv]
    simp only [F, G]
    by_cases hx : x ∈ s <;> simp [Set.indicator, hx, hmem]
  have hcoeff : ∀ n : IntVec d, UnitAddTorus.mFourierCoeff F n = 0 := by
    intro n
    by_cases hn : n = 0
    · subst n
      rw [UnitAddTorus.mFourierCoeff]
      simp only [neg_zero, UnitAddTorus.mFourier_zero,
        ContinuousMap.one_apply, one_smul]
      change (∫ t : Torus d, F t ∂volume) = 0
      simp only [F]
      rw [integral_sub (hG.integrable (by norm_num)) (integrable_const c)]
      simp [c]
    · have heq : UnitAddTorus.mFourierCoeff F n =
          UnitAddTorus.mFourier n a * UnitAddTorus.mFourierCoeff F n := by
        rw [← mFourierCoeff_translate_add, hFinv]
      by_contra hne
      apply ha n hn
      apply mul_right_cancel₀ hne
      simpa using heq.symm
  have hzero : F =ᵐ[volume] 0 :=
    ae_zero_of_memLp_two_mFourierCoeff_zero F hF hcoeff
  obtain ⟨x, hx⟩ := hzero.exists
  have hc : c = 0 ∨ c = 1 := by
    by_cases hxs : x ∈ s
    · right
      have : (1 : Complex) - c = 0 := by simpa [F, G, hxs] using hx
      exact (sub_eq_zero.mp this).symm
    · left
      have : -c = 0 := by simpa [F, G, hxs] using hx
      exact neg_eq_zero.mp this
  rw [eventuallyConst_set]
  rcases hc with hc | hc
  · right
    filter_upwards [hzero] with y hy
    intro hys
    simpa [F, G, hc, hys] using hy
  · left
    filter_upwards [hzero] with y hy
    by_contra hys
    simpa [F, G, hc, hys] using hy

/- Rewrite the character at `-alphaTorus alpha` as complex
conjugation; equality to one would contradict the positive-sign result. -/
theorem mFourier_neg_alphaTorus_ne_one {d : Nat} {alpha : RealVec d}
    (hAlpha : RationallyIndependentWithOne alpha)
    (n : IntVec d) (hn : n ≠ 0) :
    UnitAddTorus.mFourier n (-alphaTorus alpha) ≠ 1 := by
  intro h
  apply mFourier_alphaTorus_ne_one hAlpha n hn
  have hc : conj (UnitAddTorus.mFourier n (alphaTorus alpha)) = 1 := by
    simpa [UnitAddTorus.mFourier, fourier_apply] using h
  simpa using congrArg conj hc

/- Specialize the generic Fourier criterion to
`a = alphaTorus alpha` using `mFourier_alphaTorus_ne_one`. -/
theorem preErgodic_torus_add_alpha {d : Nat} {alpha : RealVec d}
    (hAlpha : RationallyIndependentWithOne alpha) :
    PreErgodic (fun x : Torus d => x + alphaTorus alpha) volume := by
  exact preErgodic_torus_add_of_mFourier_ne_one (alphaTorus alpha)
    (fun n hn => mFourier_alphaTorus_ne_one hAlpha n hn)

/- Pair pre-ergodicity with normalized-Haar measure
preservation for positive translation. -/
theorem ergodic_torus_add_alpha {d : Nat} {alpha : RealVec d}
    (hAlpha : RationallyIndependentWithOne alpha) :
    Ergodic (fun x : Torus d => x + alphaTorus alpha) volume :=
  { toMeasurePreserving := measurePreserving_torus_add (alphaTorus alpha)
    toPreErgodic := preErgodic_torus_add_alpha hAlpha }

/- Rewrite subtraction as addition by the inverse, use Haar
measure preservation, and discharge negative-sign nonresonance by `mFourier_neg_alphaTorus_ne_one`. -/
theorem ergodic_torus_sub_alpha {d : Nat} {alpha : RealVec d}
    (hAlpha : RationallyIndependentWithOne alpha) :
    Ergodic (fun x : Torus d => x - alphaTorus alpha) volume :=
  { toMeasurePreserving := measurePreserving_torus_sub (alphaTorus alpha)
    toPreErgodic := by
      simpa [sub_eq_add_neg] using
        preErgodic_torus_add_of_mFourier_ne_one (-alphaTorus alpha)
          (fun n hn => mFourier_neg_alphaTorus_ne_one hAlpha n hn) }

end IntegerFrequenciesHD.Internal

namespace IntegerFrequenciesHD

/- Apply one-sided pointwise Birkhoff to both rotation signs,
shift the backward observable by one step, split the inclusive integer sum,
and combine the two limits with denominator `2*N+1`. -/
theorem twoSided_average_torusTranslation {d : Nat} {alpha : RealVec d}
    (hAlpha : RationallyIndependentWithOne alpha)
    (phi : Internal.Torus d → Real) (hphi : Integrable phi volume) :
    ∀ᵐ x : Internal.Torus d ∂volume,
      Tendsto
        (fun N : Nat => (2 * (N : Real) + 1)⁻¹ *
          ∑ k ∈ Finset.Icc (-(N : Int)) (N : Int),
            phi (x - k • Internal.alphaTorus alpha))
        atTop (nhds (∫ y, phi y ∂volume)) := by
  let a : Internal.Torus d := Internal.alphaTorus alpha
  have hergPlus : Ergodic (fun x : Internal.Torus d => x + a) volume := by
    exact Internal.ergodic_torus_add_alpha hAlpha
  have hergMinus : Ergodic (fun x : Internal.Torus d => x + (-a)) volume := by
    simpa [sub_eq_add_neg] using Internal.ergodic_torus_sub_alpha hAlpha
  have hforward :
      ∀ᵐ x : Internal.Torus d ∂volume,
        Tendsto
          (fun N : Nat =>
            (∑ r ∈ Finset.range N, phi (x + r • a)) / (N : Real))
          atTop (nhds (∫ y, phi y ∂volume)) := by
    filter_upwards [SpectralGapsPrelim.BirkhoffPointwise.ae_tendsto_birkhoff_average_of_ergodic
      hergPlus hphi] with x hx
    refine hx.congr' ?_
    filter_upwards with N
    congr 1
    apply Finset.sum_congr rfl
    intro r hr
    rw [add_right_iterate_apply]
  let psi : Internal.Torus d → Real := fun y => phi (y - a)
  have hpsi : Integrable psi volume := by
    have hc := (Internal.measurePreserving_torus_sub a).integrable_comp
      hphi.aestronglyMeasurable
    exact hc.mpr hphi
  have hbackward :
      ∀ᵐ x : Internal.Torus d ∂volume,
        Tendsto
          (fun N : Nat =>
            (∑ r ∈ Finset.range N, phi (x - (r + 1) • a)) / (N : Real))
          atTop (nhds (∫ y, phi y ∂volume)) := by
    filter_upwards [SpectralGapsPrelim.BirkhoffPointwise.ae_tendsto_birkhoff_average_of_ergodic
      hergMinus hpsi] with x hx
    have hx' := hx
    rw [show (∫ y, psi y ∂volume) = ∫ y, phi y ∂volume by
      exact (Internal.measurePreserving_torus_sub a).integral_comp
        (Homeomorph.subRight a).measurableEmbedding phi] at hx'
    refine hx'.congr' ?_
    filter_upwards with N
    congr 1
    apply Finset.sum_congr rfl
    intro r hr
    rw [add_right_iterate_apply]
    dsimp only [psi]
    congr 1
    rw [smul_neg, add_nsmul, one_nsmul]
    abel
  have hsumNeg : ∀ (N : Nat) (f : Int → Real),
      (∑ q ∈ Finset.Icc (-(N : Int)) 0, f q) =
        ∑ r ∈ Finset.range (N + 1), f (-(r : Int)) := by
    intro N f
    refine Finset.sum_bij (fun q hq => Int.toNat (-q)) ?_ ?_ ?_ ?_
    · intro q hq
      rw [Finset.mem_range]
      rw [Finset.mem_Icc] at hq
      exact (Int.toNat_lt_of_ne_zero (m := -q) (Nat.succ_ne_zero N)).2 (by omega)
    · intro q₁ hq₁ q₂ hq₂ heq
      rw [Finset.mem_Icc] at hq₁ hq₂
      have hcast : ((Int.toNat (-q₁) : Nat) : Int) =
          ((Int.toNat (-q₂) : Nat) : Int) := by exact_mod_cast heq
      rw [Int.toNat_of_nonneg (by omega : 0 ≤ -q₁),
        Int.toNat_of_nonneg (by omega : 0 ≤ -q₂)] at hcast
      omega
    · intro r hr
      refine ⟨-(r : Int), ?_, ?_⟩
      · rw [Finset.mem_Icc]
        rw [Finset.mem_range] at hr
        omega
      · simp
    · intro q hq
      rw [Finset.mem_Icc] at hq
      have hq_eq : -((Int.toNat (-q) : Nat) : Int) = q := by
        rw [Int.toNat_of_nonneg (by omega : 0 ≤ -q)]
        omega
      exact (congrArg f hq_eq).symm
  have hsumPos : ∀ (N : Nat) (f : Int → Real),
      (∑ q ∈ Finset.Icc 1 (N : Int), f q) =
        ∑ r ∈ Finset.range N, f ((r : Int) + 1) := by
    intro N f
    by_cases hN : N = 0
    · subst N
      simp
    refine Finset.sum_bij (fun q hq => Int.toNat (q - 1)) ?_ ?_ ?_ ?_
    · intro q hq
      rw [Finset.mem_range]
      rw [Finset.mem_Icc] at hq
      exact (Int.toNat_lt_of_ne_zero (m := q - 1) hN).2 (by omega)
    · intro q₁ hq₁ q₂ hq₂ heq
      rw [Finset.mem_Icc] at hq₁ hq₂
      have hcast : ((Int.toNat (q₁ - 1) : Nat) : Int) =
          ((Int.toNat (q₂ - 1) : Nat) : Int) := by exact_mod_cast heq
      rw [Int.toNat_of_nonneg (by omega : 0 ≤ q₁ - 1),
        Int.toNat_of_nonneg (by omega : 0 ≤ q₂ - 1)] at hcast
      omega
    · intro r hr
      refine ⟨(r : Int) + 1, ?_, ?_⟩
      · rw [Finset.mem_Icc]
        rw [Finset.mem_range] at hr
        omega
      · simp
    · intro q hq
      rw [Finset.mem_Icc] at hq
      have hq_eq : ((Int.toNat (q - 1) : Nat) : Int) + 1 = q := by
        rw [Int.toNat_of_nonneg (by omega : 0 ≤ q - 1)]
        omega
      exact (congrArg f hq_eq).symm
  filter_upwards [hforward, hbackward] with x hxForward hxBackward
  let f : Int → Real := fun k => phi (x - k • a)
  let A : Nat → Real := fun N => ∑ r ∈ Finset.range (N + 1), f (-(r : Int))
  let B : Nat → Real := fun N => ∑ r ∈ Finset.range N, f ((r : Int) + 1)
  let S : Nat → Real := fun N => ∑ k ∈ Finset.Icc (-(N : Int)) (N : Int), f k
  have hA : Tendsto (fun N : Nat => A N / ((N : Real) + 1)) atTop
      (nhds (∫ y, phi y ∂volume)) := by
    have hs := hxForward.comp (tendsto_add_atTop_nat 1)
    change Tendsto
      (fun N : Nat =>
        (∑ r ∈ Finset.range (N + 1), phi (x + r • a)) /
          ((N + 1 : Nat) : Real)) atTop (nhds (∫ y, phi y ∂volume)) at hs
    simpa [Function.comp_apply, Nat.cast_add, Nat.cast_one, A, f,
      neg_zsmul, sub_neg_eq_add] using hs
  have hB : Tendsto (fun N : Nat => B N / (N : Real)) atTop
      (nhds (∫ y, phi y ∂volume)) := by
    simpa [B, f, add_zsmul, add_nsmul] using hxBackward
  have hsplit : ∀ N : Nat, S N = A N + B N := by
    intro N
    have hset : Finset.Icc (-(N : Int)) (N : Int) =
        Finset.Icc (-(N : Int)) 0 ∪ Finset.Icc 1 (N : Int) := by
      ext q
      simp
      omega
    have hdisj : Disjoint (Finset.Icc (-(N : Int)) 0)
        (Finset.Icc 1 (N : Int)) := by
      rw [Finset.disjoint_left]
      intro q hq0 hq1
      rw [Finset.mem_Icc] at hq0 hq1
      omega
    dsimp only [S, A, B]
    rw [hset, Finset.sum_union hdisj, hsumNeg N f, hsumPos N f]
  have hden : Tendsto (fun N : Nat => 4 * (N : Real) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : Real) < 4))
  have hsmall : Tendsto (fun N : Nat => (4 * (N : Real) + 2)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hden
  have hwA : Tendsto
      (fun N : Nat => ((N : Real) + 1) / (2 * (N : Real) + 1)) atTop
      (nhds (1 / 2 : Real)) := by
    have h := (tendsto_const_nhds.add hsmall : Tendsto
      (fun N : Nat => (1 / 2 : Real) + (4 * (N : Real) + 2)⁻¹) atTop
      (nhds ((1 / 2 : Real) + 0)))
    simpa only [add_zero] using h.congr' (by
      filter_upwards with N
      have hd : (2 * (N : Real) + 1) ≠ 0 := by positivity
      field_simp
      ring)
  have hwB : Tendsto
      (fun N : Nat => (N : Real) / (2 * (N : Real) + 1)) atTop
      (nhds (1 / 2 : Real)) := by
    have h := (tendsto_const_nhds.sub hsmall : Tendsto
      (fun N : Nat => (1 / 2 : Real) - (4 * (N : Real) + 2)⁻¹) atTop
      (nhds ((1 / 2 : Real) - 0)))
    simpa only [sub_zero] using h.congr' (by
      filter_upwards with N
      have hd : (2 * (N : Real) + 1) ≠ 0 := by positivity
      field_simp
      ring)
  have hcombined := (hwA.mul hA).add (hwB.mul hB)
  have hlimit : (1 / 2 : Real) * (∫ y, phi y ∂volume) +
      (1 / 2 : Real) * (∫ y, phi y ∂volume) = ∫ y, phi y ∂volume := by ring
  rw [hlimit] at hcombined
  refine hcombined.congr' ?_
  filter_upwards [Nat.eventually_pos] with N hN
  have hNR : (N : Real) ≠ 0 := by exact_mod_cast hN.ne'
  have hN1R : (N : Real) + 1 ≠ 0 := by positivity
  have hdenR : 2 * (N : Real) + 1 ≠ 0 := by positivity
  change
    ((N : Real) + 1) / (2 * (N : Real) + 1) * (A N / ((N : Real) + 1)) +
        (N : Real) / (2 * (N : Real) + 1) * (B N / (N : Real)) =
      (2 * (N : Real) + 1)⁻¹ * S N
  rw [hsplit N]
  field_simp

namespace Internal

/- Apply the real two-sided theorem to the indicator of `C`,
rewrite the finite indicator sum as a filtered cardinality, and identify the
indicator integral with `(volume C).toReal`. -/
theorem twoSided_set_visit_density {d : Nat} {alpha : RealVec d}
    (hAlpha : RationallyIndependentWithOne alpha)
    (C : Set (Torus d)) (hC : MeasurableSet C) :
    ∀ᵐ x : Torus d ∂volume,
      Tendsto
        (fun N : Nat =>
          (((@Finset.filter Int (fun k => x - k • alphaTorus alpha ∈ C)
              (Classical.decPred _) (Finset.Icc (-(N : Int)) (N : Int))).card : Nat) : Real) /
            (2 * (N : Real) + 1))
        atTop (nhds (volume C).toReal) := by
  let phi : Torus d → Real := C.indicator (fun _ => 1)
  have hphi : Integrable phi volume := (integrable_const (1 : Real)).indicator hC
  filter_upwards [twoSided_average_torusTranslation hAlpha phi hphi] with x hx
  have hint : (∫ y : Torus d, phi y ∂volume) = (volume C).toReal := by
    dsimp only [phi]
    exact integral_indicator_one hC
  rw [hint] at hx
  refine hx.congr' ?_
  filter_upwards with N
  dsimp only [phi]
  change
    (2 * (N : Real) + 1)⁻¹ *
        ∑ k ∈ Finset.Icc (-(N : Int)) (N : Int),
          C.indicator (fun _ => (1 : Real)) (x - k • alphaTorus alpha) =
      ((((@Finset.filter Int (fun k => x - k • alphaTorus alpha ∈ C)
        (Classical.decPred _) (Finset.Icc (-(N : Int)) (N : Int))).card : Nat) : Real) /
      (2 * (N : Real) + 1))
  rw [div_eq_mul_inv, mul_comm]
  congr 1
  simp only [Set.indicator, Finset.sum_boole]

end Internal
end IntegerFrequenciesHD
