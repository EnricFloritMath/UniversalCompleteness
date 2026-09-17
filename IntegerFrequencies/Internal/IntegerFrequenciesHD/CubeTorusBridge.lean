import IntegerFrequenciesHD.DefinitionsAndTarget
import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# Closed-cube / product-torus bridge

This file owns the canonical `(0,1]^d` representative, null lower faces,
restricted-L1 transport, Fourier-sign transport, and Haar translations.
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

/- Thin wrapper around
`UnitAddTorus.measurePreserving_equivPiIoc` at the zero origin. -/
theorem measurePreserving_torusIocEquivHD (d : Nat) :
    MeasurePreserving (torusIocEquivHD d) volume
      (Measure.comap Subtype.val volume) := by
  exact UnitAddTorus.measurePreserving_equivPiIoc
    (fun _ : Fin d => (0 : Real))

/- Project the subtype property produced by the measurable
equivalence. -/
theorem torusToCubeHD_mem {d : Nat} (z : Torus d) :
    torusToCubeHD z ∈ iocUnitCubeHD d := by
  exact (torusIocEquivHD d z).property

/- Use the inverse law for `torusIocEquivHD` and the coordinate
formula for its inverse. -/
theorem cubeToTorusHD_torusToCubeHD {d : Nat} (z : Torus d) :
    cubeToTorusHD (torusToCubeHD z) = z := by
  change (torusIocEquivHD d).symm (torusIocEquivHD d z) = z
  exact (torusIocEquivHD d).symm_apply_apply z

/- Apply `apply_symm_apply` to the subtype `⟨x,hx⟩`, then
project the equality of underlying real vectors. -/
theorem torusToCubeHD_cubeToTorusHD {d : Nat} (x : RealVec d)
    (hx : x ∈ iocUnitCubeHD d) :
    torusToCubeHD (cubeToTorusHD x) = x := by
  let y : {x : RealVec d // x ∈ iocUnitCubeHD d} := ⟨x, hx⟩
  have hy := (torusIocEquivHD d).apply_symm_apply y
  exact congrArg Subtype.val hy

/- The removed set is contained in the finite union of coordinate
hyperplanes `{x | x i = 0}`, each of product Lebesgue measure zero. -/
theorem unitCubeHD_diff_ioc_null (d : Nat) :
    volume (unitCubeHD d \ iocUnitCubeHD d) = 0 := by
  have hsub : iocUnitCubeHD d ⊆ unitCubeHD d := by
    intro x hx i
    exact ⟨(hx i).1.le, by simpa using (hx i).2⟩
  have hmeas : MeasurableSet (iocUnitCubeHD d) := by
    simpa [iocUnitCubeHD, Set.pi] using
      (MeasurableSet.univ_pi (fun _ : Fin d => measurableSet_Ioc))
  rw [measure_sdiff hsub hmeas.nullMeasurableSet]
  · simp only [unitCubeHD, iocUnitCubeHD]
    rw [show {x : Fin d → Real | ∀ i, x i ∈ Icc 0 1} =
        Set.Icc (fun _ => (0 : Real)) (fun _ => (1 : Real)) by
          ext x
          constructor
          · intro hx
            exact ⟨fun i => (hx i).1, fun i => (hx i).2⟩
          · rintro ⟨hx0, hx1⟩ i
            exact ⟨hx0 i, hx1 i⟩]
    rw [show {x : Fin d → Real | ∀ i, x i ∈ Ioc 0 (0 + 1)} =
        Set.univ.pi (fun _ : Fin d => Ioc (0 : Real) 1) by
          ext x
          simp [Set.mem_pi]]
    rw [Real.volume_Icc_pi, Real.volume_pi_Ioc]
    simp
  · simp only [iocUnitCubeHD]
    rw [show {x : Fin d → Real | ∀ i, x i ∈ Ioc 0 (0 + 1)} =
        Set.univ.pi (fun _ : Fin d => Ioc (0 : Real) 1) by
          ext x
          simp [Set.mem_pi]]
    rw [Real.volume_pi_Ioc]
    simp

/- Remove the null subset supplied by `unitCubeHD_diff_ioc_null`, using
measurability of `S` for the measure-congruence step. -/
theorem volume_inter_iocUnitCubeHD {d : Nat} {S : Set (RealVec d)}
    (hSmeas : MeasurableSet S) (hSsub : S ⊆ unitCubeHD d) :
    volume (S ∩ iocUnitCubeHD d) = volume S := by
  have hnull : volume (S \ iocUnitCubeHD d) = 0 := by
    refine measure_mono_null (s := S \ iocUnitCubeHD d)
      (t := unitCubeHD d \ iocUnitCubeHD d) ?_
      (unitCubeHD_diff_ioc_null d)
    intro x hx
    exact ⟨hSsub hx.1, hx.2⟩
  have hset : S ∩ iocUnitCubeHD d = S \ (S \ iocUnitCubeHD d) := by
    ext x
    simp
  rw [hset, measure_sdiff_null hnull]

/- Express the carrier as the measurable preimage of the
normalized measurable carrier under the measurable equivalence. -/
theorem measurableSet_torusCarrierHD {d : Nat} {S : Set (RealVec d)}
    (hSmeas : MeasurableSet S) : MeasurableSet (torusCarrierHD S) := by
  have hioc : MeasurableSet (iocUnitCubeHD d) := by
    simpa [iocUnitCubeHD, Set.pi] using
      (MeasurableSet.univ_pi (fun _ : Fin d => measurableSet_Ioc))
  have hrep : Measurable (torusToCubeHD : Torus d → RealVec d) := by
    change Measurable (fun z : Torus d =>
      ((torusIocEquivHD d z).1 : RealVec d))
    exact measurable_subtype_coe.comp (torusIocEquivHD d).measurable
  exact (hSmeas.inter hioc).preimage hrep

private theorem measurableEmbedding_torusToCubeHD (d : Nat) :
    MeasurableEmbedding (torusToCubeHD : Torus d → RealVec d) := by
  have hioc : MeasurableSet (iocUnitCubeHD d) := by
    simpa [iocUnitCubeHD, Set.pi] using
      (MeasurableSet.univ_pi (fun _ : Fin d => measurableSet_Ioc))
  change MeasurableEmbedding (Subtype.val ∘ torusIocEquivHD d)
  exact (MeasurableEmbedding.subtype_coe hioc).comp
    (torusIocEquivHD d).measurableEmbedding

private theorem measurePreserving_torusToCubeHD (d : Nat) :
    MeasurePreserving (torusToCubeHD : Torus d → RealVec d) volume
      (volume.restrict (iocUnitCubeHD d)) := by
  have hioc : MeasurableSet (iocUnitCubeHD d) := by
    simpa [iocUnitCubeHD, Set.pi] using
      (MeasurableSet.univ_pi (fun _ : Fin d => measurableSet_Ioc))
  have hcoe : MeasurePreserving
      (Subtype.val : {x : RealVec d // x ∈ iocUnitCubeHD d} → RealVec d)
      (Measure.comap Subtype.val volume)
      (volume.restrict (iocUnitCubeHD d)) := by
    refine ⟨measurable_subtype_coe, ?_⟩
    exact map_comap_subtype_coe hioc volume
  have hcomp := hcoe.comp (measurePreserving_torusIocEquivHD d)
  change MeasurePreserving (Subtype.val ∘ torusIocEquivHD d) volume
    (volume.restrict (iocUnitCubeHD d))
  exact hcomp

/- Combine measure preservation of the representative
equivalence with the exact null-face volume identity. -/
theorem volume_torusCarrierHD {d : Nat} {S : Set (RealVec d)}
    (hSmeas : MeasurableSet S) (hSsub : S ⊆ unitCubeHD d) :
    volume (torusCarrierHD S) = volume S := by
  have hioc : MeasurableSet (iocUnitCubeHD d) := by
    simpa [iocUnitCubeHD, Set.pi] using
      (MeasurableSet.univ_pi (fun _ : Fin d => measurableSet_Ioc))
  have hnorm : MeasurableSet (normalizedCarrierHD S) :=
    hSmeas.inter hioc
  calc
    volume (torusCarrierHD S) =
        (volume.restrict (iocUnitCubeHD d)) (normalizedCarrierHD S) := by
      exact (measurePreserving_torusToCubeHD d).measure_preimage
        hnorm.nullMeasurableSet
    _ = volume (normalizedCarrierHD S) := by
      rw [Measure.restrict_apply hnorm]
      congr 1
      exact inter_eq_left.mpr (by
        intro x hx
        exact hx.2)
    _ = volume S := volume_inter_iocUnitCubeHD hSmeas hSsub

/- Pass restricted integrability to the indicator zero extension,
remove null lower faces, and compose with the measure-preserving equivalence. -/
theorem integrable_torusRepresentativeHD {d : Nat} {S : Set (RealVec d)}
    {f : RealVec d → Complex} (hSmeas : MeasurableSet S)
    (hSsub : S ⊆ unitCubeHD d)
    (hf : Integrable f (volume.restrict S)) :
    Integrable (torusRepresentativeHD S f) volume := by
  have hioc : MeasurableSet (iocUnitCubeHD d) := by
    simpa [iocUnitCubeHD, Set.pi] using
      (MeasurableSet.univ_pi (fun _ : Fin d => measurableSet_Ioc))
  have hnorm : MeasurableSet (normalizedCarrierHD S) :=
    hSmeas.inter hioc
  have hfNorm : Integrable f (volume.restrict (normalizedCarrierHD S)) :=
    hf.mono_measure (Measure.restrict_mono Set.inter_subset_left le_rfl)
  have hzero : Integrable (zeroExtensionHD S f) volume := by
    rw [zeroExtensionHD]
    exact (integrable_indicator_iff hnorm).2 hfNorm
  have hzeroIoc :
      Integrable (zeroExtensionHD S f) (volume.restrict (iocUnitCubeHD d)) :=
    hzero.mono_measure Measure.restrict_le_self
  change Integrable (zeroExtensionHD S f ∘ torusToCubeHD) volume
  exact ((measurePreserving_torusToCubeHD d).integrable_comp
    hzeroIoc.aestronglyMeasurable).2 hzeroIoc

/- Unfold `torusCarrierHD`, `torusRepresentativeHD`, and the
indicator, then apply `Set.indicator_of_notMem`. -/
theorem torusRepresentativeHD_eq_zero_off {d : Nat} (S : Set (RealVec d))
    (f : RealVec d → Complex) {z : Torus d} (hz : z ∉ torusCarrierHD S) :
    torusRepresentativeHD S f z = 0 := by
  have hz' : torusToCubeHD z ∉ normalizedCarrierHD S := hz
  change (normalizedCarrierHD S).indicator f (torusToCubeHD z) =
    (0 : Complex)
  rw [Set.indicator_of_notMem hz']

private theorem mFourier_neg_cubeToTorusHD {d : Nat}
    (n : IntVec d) (x : RealVec d) :
    UnitAddTorus.mFourier (-n) (cubeToTorusHD x) =
      starRingEnd Complex
        (fourierCharHD (fun i => (n i : Real)) x) := by
  unfold fourierCharHD
  rw [← Complex.exp_conj]
  simp only [UnitAddTorus.mFourier, cubeToTorusHD,
    ContinuousMap.coe_mk, Pi.neg_apply, fourier_coe_apply]
  rw [← Complex.exp_sum]
  congr 1
  rw [map_mul, map_mul]
  rw [Complex.conj_ofReal, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  rw [Finset.mul_sum]
  ring

/- Transport the coefficient integral through the canonical
equivalence, unfold the indicator, remove null faces, and normalize the product
character to the negative article Fourier sample. -/
theorem mFourierCoeff_torusRepresentativeHD {d : Nat} {S : Set (RealVec d)}
    {f : RealVec d → Complex} (hSmeas : MeasurableSet S)
    (hSsub : S ⊆ unitCubeHD d)
    (hf : Integrable f (volume.restrict S)) (n : IntVec d) :
    UnitAddTorus.mFourierCoeff (torusRepresentativeHD S f) n =
      fourierSampleOnHD S f (fun i => (n i : Real)) := by
  let phase : RealVec d → Complex := fun x =>
    starRingEnd Complex (fourierCharHD (fun i => (n i : Real)) x)
  let g : RealVec d → Complex := fun x => phase x * zeroExtensionHD S f x
  have hpoint (z : Torus d) :
      UnitAddTorus.mFourier (-n) z • torusRepresentativeHD S f z =
        g (torusToCubeHD z) := by
    have hchar : UnitAddTorus.mFourier (-n) z =
        phase (torusToCubeHD z) := by
      calc
        UnitAddTorus.mFourier (-n) z =
            UnitAddTorus.mFourier (-n)
              (cubeToTorusHD (torusToCubeHD z)) := by
          congr 1
          exact (cubeToTorusHD_torusToCubeHD z).symm
        _ = phase (torusToCubeHD z) :=
          mFourier_neg_cubeToTorusHD n (torusToCubeHD z)
    rw [hchar]
    rfl
  have hioc : MeasurableSet (iocUnitCubeHD d) := by
    simpa [iocUnitCubeHD, Set.pi] using
      (MeasurableSet.univ_pi (fun _ : Fin d => measurableSet_Ioc))
  have hnorm : MeasurableSet (normalizedCarrierHD S) :=
    hSmeas.inter hioc
  have hnormSub : normalizedCarrierHD S ⊆ iocUnitCubeHD d :=
    Set.inter_subset_right
  have hnull : volume (S \ iocUnitCubeHD d) = 0 := by
    refine measure_mono_null (s := S \ iocUnitCubeHD d)
      (t := unitCubeHD d \ iocUnitCubeHD d) ?_
      (unitCubeHD_diff_ioc_null d)
    intro x hx
    exact ⟨hSsub hx.1, hx.2⟩
  have hnormSet :
      normalizedCarrierHD S = S \ (S \ iocUnitCubeHD d) := by
    ext x
    simp [normalizedCarrierHD]
  have hnormAe : normalizedCarrierHD S =ᵐ[volume] S := by
    rw [hnormSet]
    exact sdiff_null_ae_eq_self hnull
  have hrestrict :
      volume.restrict (normalizedCarrierHD S) = volume.restrict S :=
    Measure.restrict_congr_set hnormAe
  have hmasked : g = (normalizedCarrierHD S).indicator
      (fun x => phase x * f x) := by
    funext x
    simp only [g, zeroExtensionHD]
    exact (Set.indicator_mul_right (normalizedCarrierHD S) phase f).symm
  rw [UnitAddTorus.mFourierCoeff]
  calc
    (∫ z : Torus d,
        UnitAddTorus.mFourier (-n) z • torusRepresentativeHD S f z
          ∂volume) = ∫ z : Torus d, g (torusToCubeHD z) ∂volume :=
      integral_congr_ae (ae_of_all _ hpoint)
    _ = ∫ x : RealVec d, g x ∂(volume.restrict (iocUnitCubeHD d)) := by
      exact (measurePreserving_torusToCubeHD d).integral_comp
        (measurableEmbedding_torusToCubeHD d) g
    _ = ∫ x in normalizedCarrierHD S, phase x * f x := by
      rw [hmasked, setIntegral_indicator hnorm,
        inter_eq_right.mpr hnormSub]
    _ = ∫ x in S, phase x * f x := by rw [hrestrict]
    _ = fourierSampleOnHD S f (fun i => (n i : Real)) := by
      rw [fourierSampleOnHD]
      apply integral_congr_ae
      exact ae_of_all _ fun x => by
        dsimp only [phase]
        rw [mul_comm]

private theorem integral_norm_torusRepresentativeHD {d : Nat}
    {S : Set (RealVec d)} {f : RealVec d → Complex}
    (hSmeas : MeasurableSet S) (hSsub : S ⊆ unitCubeHD d)
    (hf : Integrable f (volume.restrict S)) :
    (∫ z : Torus d, ‖torusRepresentativeHD S f z‖ ∂volume) =
      ∫ x in S, ‖f x‖ := by
  have hioc : MeasurableSet (iocUnitCubeHD d) := by
    simpa [iocUnitCubeHD, Set.pi] using
      (MeasurableSet.univ_pi (fun _ : Fin d => measurableSet_Ioc))
  have hnorm : MeasurableSet (normalizedCarrierHD S) :=
    hSmeas.inter hioc
  have hnormSub : normalizedCarrierHD S ⊆ iocUnitCubeHD d :=
    Set.inter_subset_right
  have hnull : volume (S \ iocUnitCubeHD d) = 0 := by
    refine measure_mono_null (s := S \ iocUnitCubeHD d)
      (t := unitCubeHD d \ iocUnitCubeHD d) ?_
      (unitCubeHD_diff_ioc_null d)
    intro x hx
    exact ⟨hSsub hx.1, hx.2⟩
  have hnormSet :
      normalizedCarrierHD S = S \ (S \ iocUnitCubeHD d) := by
    ext x
    simp [normalizedCarrierHD]
  have hnormAe : normalizedCarrierHD S =ᵐ[volume] S := by
    rw [hnormSet]
    exact sdiff_null_ae_eq_self hnull
  have hrestrict :
      volume.restrict (normalizedCarrierHD S) = volume.restrict S :=
    Measure.restrict_congr_set hnormAe
  calc
    (∫ z : Torus d, ‖torusRepresentativeHD S f z‖ ∂volume) =
        ∫ z : Torus d, ‖zeroExtensionHD S f (torusToCubeHD z)‖ ∂volume :=
      rfl
    _ = ∫ x : RealVec d, ‖zeroExtensionHD S f x‖
          ∂(volume.restrict (iocUnitCubeHD d)) := by
      exact (measurePreserving_torusToCubeHD d).integral_comp
        (measurableEmbedding_torusToCubeHD d)
        (fun x : RealVec d => ‖zeroExtensionHD S f x‖)
    _ = ∫ x in normalizedCarrierHD S, ‖f x‖ := by
      simp_rw [zeroExtensionHD, norm_indicator_eq_indicator_norm]
      rw [setIntegral_indicator hnorm, inter_eq_right.mpr hnormSub]
    _ = ∫ x in S, ‖f x‖ := by rw [hrestrict]

/- Copy the proved norm-integral route: a.e. zero on the torus
makes the norm integral zero; transport it back and invoke nonnegative
integral-zero characterization on `volume.restrict S`. -/
theorem ae_zero_restrict_of_torusRepresentativeHD {d : Nat}
    {S : Set (RealVec d)} {f : RealVec d → Complex}
    (hSmeas : MeasurableSet S) (hSsub : S ⊆ unitCubeHD d)
    (hf : Integrable f (volume.restrict S))
    (hzero : torusRepresentativeHD S f =ᵐ[volume] 0) :
    f =ᵐ[volume.restrict S] 0 := by
  have hnormzeroTorus :
      (fun z => ‖torusRepresentativeHD S f z‖) =ᵐ[volume]
        (fun _ => (0 : Real)) := by
    filter_upwards [hzero] with z hz
    simpa using congrArg norm hz
  have htorusIntegralZero :
      (∫ z : Torus d, ‖torusRepresentativeHD S f z‖ ∂volume) = 0 := by
    simpa using integral_congr_ae hnormzeroTorus
  have hrestrictIntegralZero : (∫ x in S, ‖f x‖) = 0 := by
    rw [← integral_norm_torusRepresentativeHD hSmeas hSsub hf]
    exact htorusIntegralZero
  have hnormzero :
      (fun x => ‖f x‖) =ᵐ[volume.restrict S] (fun _ => (0 : Real)) :=
    (integral_eq_zero_iff_of_nonneg_ae
      (ae_of_all _ fun x => norm_nonneg (f x)) hf.norm).1
        hrestrictIntegralZero
  filter_upwards [hnormzero] with x hx
  have hxnorm : ‖f x‖ = 0 := by simpa using hx
  simpa using (norm_eq_zero.mp hxnorm)

/- Invoke right-translation invariance of the normalized additive
Haar measure. -/
theorem measurePreserving_torus_add {d : Nat} (a : Torus d) :
    MeasurePreserving (fun x : Torus d => x + a) volume volume := by
  exact measurePreserving_add_right volume a

/- Apply the addition result to `-a` and simplify subtraction. -/
theorem measurePreserving_torus_sub {d : Nat} (a : Torus d) :
    MeasurePreserving (fun x : Torus d => x - a) volume volume := by
  simpa [sub_eq_add_neg] using measurePreserving_torus_add (-a)

end IntegerFrequenciesHD.Internal
