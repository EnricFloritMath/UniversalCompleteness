import IntegerFrequenciesHD.Broadening
import IntegerFrequenciesHD.TorusRotationErgodic
import Theorem14.ZeroDensityUniqueness

/-!
# Restricted-L1 uniqueness

This module proves restricted-L1 uniqueness.  It combines the fixed
multitorus representative, two-sided ergodic visit density, canonical
one-dimensional broadening, and the proved zero-density uniqueness tail.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology

local instance l1UniquenessMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance l1UniquenessIsAddHaarMeasureUnitAddCircle : Measure.IsAddHaarMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance l1UniquenessIsProbabilityMeasureUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace IntegerFrequenciesHD
namespace Internal

/- Bound `volume S` by the unit-cube volume one, convert the
strict ENNReal inequality to `(volume S).toReal < v`, unfold the deterministic
half-gap, and solve the six displayed inequalities by linear arithmetic. -/
theorem broadeningWidthHD_facts {d : Nat} {v : Real} {S : Set (RealVec d)}
    (hv0 : 0 < v) (hv1 : v < 1)
    (hSsub : S ⊆ unitCubeHD d)
    (hSlt : volume S < ENNReal.ofReal v) :
    let epsilon := broadeningWidthHD v S
    let L := 1 - v + epsilon
    0 < epsilon ∧ epsilon < v ∧ epsilon < 1 ∧ 0 ≤ L ∧ L < 1 ∧
      L < 1 - (volume S).toReal := by
  have hvolLe : volume S ≤ volume (unitCubeHD d) := measure_mono hSsub
  have hunitNe : volume (unitCubeHD d) ≠ ∞ := by
    rw [show unitCubeHD d =
        Set.Icc (fun _ : Fin d ↦ (0 : Real)) (fun _ ↦ (1 : Real)) by
      ext x
      constructor
      · intro hx
        exact ⟨fun i ↦ (hx i).1, fun i ↦ (hx i).2⟩
      · rintro ⟨hx0, hx1⟩ i
        exact ⟨hx0 i, hx1 i⟩]
    rw [Real.volume_Icc_pi]
    simp
  have hofNe : ENNReal.ofReal v ≠ ∞ := ENNReal.ofReal_ne_top
  have hvolNe : volume S ≠ ∞ := ne_top_of_le_ne_top hunitNe hvolLe
  have hmeasureLt : (volume S).toReal < v := by
    have h := (ENNReal.toReal_lt_toReal hvolNe hofNe).2 hSlt
    simpa [ENNReal.toReal_ofReal hv0.le] using h
  have hmeasureNonneg : 0 ≤ (volume S).toReal := ENNReal.toReal_nonneg
  dsimp [broadeningWidthHD]
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/- Rewrite each torus coefficient of the fixed representative
with the exact cube/torus bridge and apply the corresponding input sample-zero
hypothesis.  The multi-index and negative article sign are unchanged. -/
theorem torusRepresentativeHD_selectedCoeffs_zero {d : Nat}
    {alpha : RealVec d} {v : Real} {S : Set (RealVec d)}
    (hSmeas : MeasurableSet S) (hSsub : S ⊆ unitCubeHD d)
    {f : RealVec d → Complex} (hf : Integrable f (volume.restrict S))
    (hzero : ∀ n ∈ integerFrequencySetHD alpha v,
      fourierSampleOnHD S f (fun i => (n i : Real)) = 0) :
    ∀ n ∈ integerFrequencySetHD alpha v,
      UnitAddTorus.mFourierCoeff (torusRepresentativeHD S f) n = 0 := by
  intro n hn
  rw [mFourierCoeff_torusRepresentativeHD hSmeas hSsub hf n]
  exact hzero n hn

/- Apply two-sided set-visit density to the complement of the
fixed torus carrier, whose probability is exactly
`1-(volume S).toReal`.  Choose `sigma` strictly between the support length and
this limit.  Every complement visit forces the corresponding orbit value,
and hence the exact broadened coefficient, to vanish; compare the inclusive
finite counts without cancelling a window coefficient. -/
theorem broadening_has_zeroDensity_aeHD {d : Nat}
    {S : Set (RealVec d)} {alpha : RealVec d} {v epsilon : Real}
    {F : Torus d → Complex}
    (hSmeas : MeasurableSet S) (hSsub : S ⊆ unitCubeHD d)
    (hAlpha : RationallyIndependentWithOne alpha)
    (hoff : ∀ x, x ∉ torusCarrierHD S → F x = 0)
    (hgap : 1 - v + epsilon < 1 - (volume S).toReal) :
    ∀ᵐ x ∂volume, ∀ B : BroadeningDataHD epsilon alpha v F x,
      ∃ sigma : Real, 1 - v + epsilon < sigma ∧
        Theorem14.Internal.HasEventuallySymmetricFourierZeroDensity
          (broadenedFunctionHD epsilon alpha F x) sigma := by
  classical
  have hcarrierMeas : MeasurableSet (torusCarrierHD S) :=
    measurableSet_torusCarrierHD hSmeas
  have hcarrierMeasure : volume (torusCarrierHD S) = volume S :=
    volume_torusCarrierHD hSmeas hSsub
  have hcarrierNe : volume (torusCarrierHD S) ≠ ∞ :=
    ne_top_of_le_ne_top
      MeasureTheory.IsFiniteMeasure.measure_univ_lt_top.ne
      (measure_mono (Set.subset_univ _))
  have hcompReal : (volume (torusCarrierHD S)ᶜ).toReal =
      1 - (volume S).toReal := by
    rw [measure_compl hcarrierMeas hcarrierNe,
      ENNReal.toReal_sub_of_le (measure_mono (Set.subset_univ _))
        MeasureTheory.IsFiniteMeasure.measure_univ_lt_top.ne]
    simp only [measure_univ, hcarrierMeasure]
    norm_num
  have hbir := twoSided_set_visit_density hAlpha
    (torusCarrierHD S)ᶜ hcarrierMeas.compl
  filter_upwards [hbir] with x hx
  intro B
  let L : Real := 1 - v + epsilon
  let q : Real := 1 - (volume S).toReal
  let sigma : Real := (L + q) / 2
  have hLq : L < q := by simpa only [L, q] using hgap
  have hLsigma : L < sigma := by dsimp [sigma]; linarith
  have hsigmaq : sigma < q := by dsimp [sigma]; linarith
  refine ⟨sigma, by simpa only [L] using hLsigma, ?_⟩
  unfold Theorem14.Internal.HasEventuallySymmetricFourierZeroDensity
  have hxq : Tendsto
      (fun N : Nat ↦
        (((@Finset.filter Int
          (fun k ↦ x - k • alphaTorus alpha ∈ (torusCarrierHD S)ᶜ)
          (Classical.decPred _)
          (Finset.Icc (-(N : Int)) (N : Int))).card : Nat) : Real) /
            (2 * (N : Real) + 1))
      atTop (nhds q) := by
    rw [hcompReal] at hx
    simpa only [q] using hx
  have havg : ∀ᶠ N : Nat in atTop,
      sigma <
        (((@Finset.filter Int
          (fun k ↦ x - k • alphaTorus alpha ∈ (torusCarrierHD S)ᶜ)
          (Classical.decPred _)
          (Finset.Icc (-(N : Int)) (N : Int))).card : Nat) : Real) /
            (2 * (N : Real) + 1) :=
    (tendsto_order.1 hxq).1 sigma hsigmaq
  filter_upwards [havg] with N hN
  let K : Finset Int := Finset.Icc (-(N : Int)) (N : Int)
  let p : Int → Prop := fun k ↦
    x - k • alphaTorus alpha ∈ (torusCarrierHD S)ᶜ
  have hsubset : K.filter p ⊆
      K.filter (fun k ↦
        fourierCoeff (broadenedFunctionHD epsilon alpha F x) k = 0) := by
    intro k hk
    rw [Finset.mem_filter] at hk ⊢
    refine ⟨hk.1, ?_⟩
    have hFzero : F (x - k • alphaTorus alpha) = 0 := by
      apply hoff
      simpa only [p, Set.mem_compl_iff] using hk.2
    rw [B.coeff_eq k, weightedOrbitCoeffHD, hFzero, mul_zero]
  have hcard : ((K.filter p).card : Real) ≤
      ((K.filter (fun k ↦
        fourierCoeff (broadenedFunctionHD epsilon alpha F x) k = 0)).card : Real) := by
    exact_mod_cast Finset.card_le_card hsubset
  have hfilter :
      (@Finset.filter Int
          (fun k ↦ x - k • alphaTorus alpha ∈ (torusCarrierHD S)ᶜ)
          (Classical.decPred _)
          (Finset.Icc (-(N : Int)) (N : Int))) = K.filter p := by
    ext k
    simp only [Finset.mem_filter]
    rfl
  have hdenom : 0 < 2 * (N : Real) + 1 := by positivity
  have hscaled : sigma * (2 * (N : Real) + 1) ≤
      ((K.filter p).card : Real) := by
    rw [hfilter] at hN
    apply le_of_lt
    apply (lt_div_iff₀ hdenom).mp
    exact hN
  exact hscaled.trans
    (by simpa only [Theorem14.Internal.symmetricFourierZeroCount, K] using hcard)

/- Set `F` to the fixed torus representative and choose the
deterministic half-gap.  Intersect broadening and zero-density conull events
before fixing `x`, apply the proved one-dimensional bandlimited
zero-density theorem, recover `F x=0` using only coefficient `k=0` and the
nonzero zero-window coefficient, then transport a.e. zero back to
`volume.restrict S`. -/
theorem l1_uniqueness_interiorHD {d : Nat}
    {alpha : RealVec d} {v : Real}
    (hAlpha : RationallyIndependentWithOne alpha)
    (hv0 : 0 < v) (hv1 : v < 1)
    {S : Set (RealVec d)} (hSmeas : MeasurableSet S)
    (hSsub : S ⊆ unitCubeHD d)
    (hSlt : volume S < ENNReal.ofReal v)
    {f : RealVec d → Complex} (hf : Integrable f (volume.restrict S))
    (hzero : ∀ n ∈ integerFrequencySetHD alpha v,
      fourierSampleOnHD S f (fun i => (n i : Real)) = 0) :
    f =ᵐ[volume.restrict S] 0 := by
  let F : Torus d → Complex := torusRepresentativeHD S f
  let epsilon : Real := broadeningWidthHD v S
  let L : Real := 1 - v + epsilon
  have hfacts := broadeningWidthHD_facts hv0 hv1 hSsub hSlt
  have he0 : 0 < epsilon := by simpa only [epsilon] using hfacts.1
  have hev : epsilon < v := by simpa only [epsilon] using hfacts.2.1
  have he1 : epsilon < 1 := by simpa only [epsilon] using hfacts.2.2.1
  have hL0 : 0 ≤ L := by
    simpa only [L, epsilon] using hfacts.2.2.2.1
  have hL1 : L < 1 := by
    simpa only [L, epsilon] using hfacts.2.2.2.2.1
  have hLgap : L < 1 - (volume S).toReal := by
    simpa only [L, epsilon] using hfacts.2.2.2.2.2
  have hFint : Integrable F volume := by
    simpa only [F] using integrable_torusRepresentativeHD hSmeas hSsub hf
  have hoff : ∀ x, x ∉ torusCarrierHD S → F x = 0 := by
    intro x hx
    exact torusRepresentativeHD_eq_zero_off S f hx
  have hcoeff : ∀ n ∈ integerFrequencySetHD alpha v,
      UnitAddTorus.mFourierCoeff F n = 0 := by
    simpa only [F] using
      torusRepresentativeHD_selectedCoeffs_zero hSmeas hSsub hf hzero
  have hbroad := broadeningHD_ae hFint hv0 hv1 he0 hev hcoeff
  have hdensity := broadening_has_zeroDensity_aeHD
    hSmeas hSsub hAlpha hoff (by simpa only [L] using hLgap)
  have hFzero : F =ᵐ[volume] 0 := by
    filter_upwards [hbroad, hdensity] with x B hdenx
    obtain ⟨sigma, hLsigma, hsigma⟩ := hdenx B
    have hbroadened : broadenedFunctionHD epsilon alpha F x = 0 :=
      Theorem14.Internal.bandlimited_zeroDensity_uniqueness
        (broadenedFunctionHD epsilon alpha F x) hL0 hL1 B.supported
          (by simpa only [L] using hLsigma) hsigma
    have hfourierZero :
        fourierCoeff (broadenedFunctionHD epsilon alpha F x) 0 = 0 := by
      rw [hbroadened]
      simp [fourierCoeff]
    have hproduct : Theorem14.Internal.windowCoeff epsilon 0 * F x = 0 := by
      have hcoeffZero := B.coeff_eq 0
      rw [hfourierZero] at hcoeffZero
      simpa [weightedOrbitCoeffHD] using hcoeffZero.symm
    exact (mul_eq_zero.mp hproduct).resolve_left
      (Theorem14.Internal.windowCoeff_eq_sq_and_zero epsilon he0 he1).2.2
  have hFzero' : torusRepresentativeHD S f =ᵐ[volume] 0 := by
    filter_upwards [hFzero] with x hx
    simpa [F] using hx
  exact ae_zero_restrict_of_torusRepresentativeHD hSmeas hSsub hf
    hFzero'

/- At `v=1` the selected integer-frequency set is universal.
Transfer all article samples to all multitorus coefficients, invoke the
product-Fejer L1 Fourier uniqueness theorem, and transport the resulting
torus a.e. equality back to the restricted source. -/
theorem l1_uniqueness_oneHD {d : Nat}
    {alpha : RealVec d} {S : Set (RealVec d)}
    (hSmeas : MeasurableSet S) (hSsub : S ⊆ unitCubeHD d)
    (hSlt : volume S < ENNReal.ofReal 1)
    {f : RealVec d → Complex} (hf : Integrable f (volume.restrict S))
    (hzero : ∀ n ∈ integerFrequencySetHD alpha 1,
      fourierSampleOnHD S f (fun i => (n i : Real)) = 0) :
    f =ᵐ[volume.restrict S] 0 := by
  let F : Torus d → Complex := torusRepresentativeHD S f
  have hFint : Integrable F volume := by
    simpa only [F] using integrable_torusRepresentativeHD hSmeas hSsub hf
  have hindex (n : IntVec d) : n ∈ integerFrequencySetHD alpha 1 := by
    change Int.fract (dotIntReal n alpha) ∈ Set.Ico (1 - 1) 1
    simpa only [sub_self] using
      (show Int.fract (dotIntReal n alpha) ∈ Set.Ico 0 1 from
        ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩)
  have hselected := torusRepresentativeHD_selectedCoeffs_zero
    hSmeas hSsub hf hzero
  have hcoeff (n : IntVec d) : UnitAddTorus.mFourierCoeff F n = 0 := by
    simpa only [F] using hselected n (hindex n)
  have hFzero : F =ᵐ[volume] (fun _ ↦ (0 : Complex)) :=
    ae_zero_of_mFourierCoeff_zero_L1 hFint hcoeff
  have hFzero' : torusRepresentativeHD S f =ᵐ[volume] 0 := by
    filter_upwards [hFzero] with x hx
    simpa [F] using hx
  exact ae_zero_restrict_of_torusRepresentativeHD hSmeas hSsub hf
    hFzero'

/- Unfold the universal predicate at zero.  Its strict volume
premise simplifies to `volume S < 0`, contradicting nonnegativity; neither the
frequency set nor the sample hypothesis is used. -/
theorem l1_uniqueness_zeroHD {d : Nat} (Lambda : Set (IntVec d)) :
    UniversalL1UniquenessBelowHD Lambda 0 := by
  unfold UniversalL1UniquenessBelowHD
  intro S hSmeas hSsub hSlt f hf hzero
  rw [ENNReal.ofReal_zero] at hSlt
  exact False.elim ((not_lt_of_ge (bot_le : 0 ≤ volume S)) hSlt)

end Internal

/- Unfold the universal predicate and split exhaustively into
`v=0`, `v=1`, and `0<v<1`.  Apply the three committed endpoint/interior
theorems without adding any positivity hypothesis to the public statement. -/
theorem integerFrequencySetHD_universalL1 {d : Nat}
    (alpha : RealVec d) (hAlpha : RationallyIndependentWithOne alpha)
    (v : Real) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    UniversalL1UniquenessBelowHD (integerFrequencySetHD alpha v) v := by
  unfold UniversalL1UniquenessBelowHD
  intro S hSmeas hSsub hSlt f hf hzero
  by_cases hvzero : v = 0
  · subst v
    exact Internal.l1_uniqueness_zeroHD (integerFrequencySetHD alpha 0)
      S hSmeas hSsub hSlt f hf hzero
  by_cases hvone : v = 1
  · subst v
    exact Internal.l1_uniqueness_oneHD hSmeas hSsub hSlt hf hzero
  · have hv0' : 0 < v := lt_of_le_of_ne hv0 (Ne.symm hvzero)
    have hv1' : v < 1 := lt_of_le_of_ne hv1 hvone
    exact Internal.l1_uniqueness_interiorHD hAlpha hv0' hv1'
      hSmeas hSsub hSlt hf hzero

end IntegerFrequenciesHD
