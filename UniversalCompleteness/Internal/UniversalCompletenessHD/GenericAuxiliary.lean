import UniversalCompletenessHD.Definitions

/-!
# Generic auxiliary interfaces and `Z^d` tiling

The proofs here establish the auxiliary tiling interfaces and preserve the
absolute-summability ordering needed downstream.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace UniversalCompletenessHD.Internal

local instance auxMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance auxIsAddHaarMeasureUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance auxIsProbabilityMeasureUnitAddCircle :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/- Re-export the exact native subtype/comap measure-preserving
equivalence from the proved higher-dimensional package. -/
theorem measurePreserving_torusIocEquivHD (d : Nat) :
    MeasurePreserving (torusIocEquivHD d) volume
      (Measure.comap Subtype.val volume) := by
  exact IntegerFrequenciesHD.Internal.measurePreserving_torusIocEquivHD d

/- Compose the subtype equivalence with `Subtype.val` and use
`map_comap_subtype_coe`; the ambient target is literally restricted volume. -/
theorem measurePreserving_torusToCubeHD_ambient (d : Nat) :
    MeasurePreserving (torusToCubeHD : Torus d → RealVec d) volume
      (volume.restrict (iocUnitCubeHD d)) := by
  have hioc : MeasurableSet (iocUnitCubeHD d) := by
    simpa [iocUnitCubeHD, IntegerFrequenciesHD.Internal.iocUnitCubeHD, Set.pi] using
      (MeasurableSet.univ_pi (fun _ : Fin d ↦ measurableSet_Ioc))
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

/- Right translation preserves normalized additive Haar measure. -/
theorem measurePreserving_torus_add {d : Nat} (a : Torus d) :
    MeasurePreserving (fun x : Torus d ↦ x + a) volume volume := by
  exact IntegerFrequenciesHD.Internal.measurePreserving_torus_add a

/- Apply the addition result to `-a` and simplify subtraction. -/
theorem measurePreserving_torus_sub {d : Nat} (a : Torus d) :
    MeasurePreserving (fun x : Torus d ↦ x - a) volume volume := by
  exact IntegerFrequenciesHD.Internal.measurePreserving_torus_sub a

/- The coordinatewise integer cast identifies `Z^d` with the integer span of
the standard basis.  Keeping this equivalence private makes the fundamental-
domain reindexing below explicit without adding a project API. -/
private noncomputable def intVecEquivZSpan (d : Nat) :
    IntVec d ≃ Submodule.span Int
      (Set.range (Pi.basisFun Real (Fin d))) := by
  let b : Module.Basis (Fin d) Real (RealVec d) :=
    Pi.basisFun Real (Fin d)
  let f : IntVec d → Submodule.span Int (Set.range b) := fun j ↦
    ⟨fun i ↦ (j i : Real), by
      rw [b.mem_span_iff_repr_mem Int]
      intro i
      refine ⟨j i, ?_⟩
      simp [b]⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro j k h
    funext i
    have hi : (j i : Real) = (k i : Real) :=
      congrFun (congrArg Subtype.val h) i
    exact_mod_cast hi
  · intro x
    have hx := (b.mem_span_iff_repr_mem Int x).mp x.property
    choose j hj using hx
    refine ⟨j, Subtype.ext ?_⟩
    funext i
    simpa [f, b] using hj i

/- Adapt the scalar fundamental-domain theorem to `(m,m+1]`;
the endpoint change is justified by singleton nullity. -/
private theorem lintegral_int_ioc_tiling
    (F : Real → ENNReal) (hF : AEMeasurable F volume) :
    (∫⁻ x : Real, F x ∂volume) =
      ∑' m : Int, ∫⁻ u in Set.Ioc (0 : Real) 1,
        F ((m : Real) + u) ∂volume := by
  let f : Int → AddSubgroup.zmultiples (1 : Real) :=
    Set.codRestrict (fun n : Int ↦ n • (1 : Real))
      (AddSubgroup.zmultiples (1 : Real)) (by
        intro n
        exact ⟨n, rfl⟩)
  let e : Int ≃ AddSubgroup.zmultiples (1 : Real) :=
    Equiv.ofBijective f
      (Equiv.ofInjective (fun n : Int ↦ n • (1 : Real))
        (zsmul_left_strictMono (show (0 : Real) < 1 by norm_num)).injective).bijective
  rw [(isAddFundamentalDomain_Ioc (show (0 : Real) < 1 by norm_num)
    0 volume).lintegral_eq_tsum'' F]
  simp only [zero_add]
  rw [← (e.tsum_eq
    (fun g ↦ ∫⁻ x : Real in Ioc (0 : Real) 1, F (g +ᵥ x) ∂volume))]
  apply tsum_congr
  intro m
  simp [e, f, AddSubgroup.vadd_def, vadd_eq_add]

/- Iterate the scalar tiling over finite coordinates using
Tonelli, then identify the nested integer family with `IntVec d`. -/
private theorem lintegral_intVec_iocSubtype_tiling {d : Nat}
    (F : RealVec d → ENNReal) (hF : AEMeasurable F volume) :
    (∫⁻ x : RealVec d, F x ∂volume) =
      ∑' j : IntVec d,
        ∫⁻ u : {x : RealVec d // x ∈ iocUnitCubeHD d},
          F (fun i ↦ (j i : Real) + (u : RealVec d) i)
            ∂(Measure.comap Subtype.val volume) := by
  let b : Module.Basis (Fin d) Real (RealVec d) :=
    Pi.basisFun Real (Fin d)
  let icoCube : Set (RealVec d) :=
    Set.univ.pi (fun _ : Fin d ↦ Ico (0 : Real) 1)
  let iocCube : Set (RealVec d) :=
    Set.univ.pi (fun _ : Fin d ↦ Ioc (0 : Real) 1)
  let e : IntVec d ≃
      (Submodule.span Int (Set.range b)).toAddSubgroup := by
    simpa [b] using intVecEquivZSpan d
  have hioc : iocUnitCubeHD d = iocCube := by
    ext x
    simp [iocUnitCubeHD, IntegerFrequenciesHD.Internal.iocUnitCubeHD,
      iocCube, Set.mem_pi]
  have hiocMeas : MeasurableSet (iocUnitCubeHD d) := by
    rw [hioc]
    exact MeasurableSet.univ_pi (fun _ : Fin d ↦ measurableSet_Ioc)
  have hae : icoCube =ᵐ[volume] iocCube := by
    exact Measure.univ_pi_Ico_ae_eq_Icc.trans
      Measure.univ_pi_Ioc_ae_eq_Icc.symm
  have hrestrict : volume.restrict icoCube =
      volume.restrict (iocUnitCubeHD d) := by
    rw [hioc]
    exact Measure.restrict_congr_set hae
  letI : Countable
      (Submodule.span Int (Set.range b)).toAddSubgroup :=
    Countable.of_equiv (IntVec d) e
  have hfd : IsAddFundamentalDomain
      (Submodule.span Int (Set.range b)).toAddSubgroup icoCube volume := by
    simpa [b, icoCube, ZSpan.fundamentalDomain_pi_basisFun] using
      ZSpan.isAddFundamentalDomain' b volume
  rw [hfd.lintegral_eq_tsum'' F]
  rw [← (e.tsum_eq
    (fun g ↦ ∫⁻ x : RealVec d in icoCube, F (g +ᵥ x) ∂volume))]
  apply tsum_congr
  intro j
  rw [MeasureTheory.lintegral_subtype_comap hiocMeas
    (fun x ↦ F (fun i ↦ (j i : Real) + x i))]
  change (∫⁻ x : RealVec d in icoCube,
      F (((e j : (Submodule.span Int (Set.range b)).toAddSubgroup) :
          RealVec d) + x) ∂volume) =
    ∫⁻ x : RealVec d in iocUnitCubeHD d,
      F (fun i ↦ (j i : Real) + x i) ∂volume
  rw [hrestrict]
  congr 1

/- Transport every native subtype cell through `measurePreserving_torusIocEquivHD`
and normalize the integer-translate map. -/
theorem lintegral_intVec_tiling {d : Nat}
    (F : RealVec d → ENNReal) (hF : AEMeasurable F volume) :
    (∫⁻ x : RealVec d, F x ∂volume) =
      ∑' j : IntVec d, ∫⁻ u : Torus d,
        F (intVecTranslate j u) ∂volume := by
  rw [lintegral_intVec_iocSubtype_tiling F hF]
  apply tsum_congr
  intro j
  symm
  have htransport :=
    (measurePreserving_torusIocEquivHD d).lintegral_comp_emb
      (torusIocEquivHD d).measurableEmbedding
      (fun u : {x : RealVec d // x ∈ iocUnitCubeHD d} ↦
        F (fun i ↦ (j i : Real) + (u : RealVec d) i))
  convert htransport using 1
  apply MeasureTheory.lintegral_congr
  intro u
  congr 1

private theorem quasiMeasurePreserving_intVecTranslate {d : Nat}
    (j : IntVec d) : Measure.QuasiMeasurePreserving
      (intVecTranslate j) volume volume := by
  have hrep : Measure.QuasiMeasurePreserving
      (torusToCubeHD : Torus d → RealVec d) volume volume :=
    (measurePreserving_torusToCubeHD_ambient d).quasiMeasurePreserving.mono_right
      Measure.restrict_le_self.absolutelyContinuous
  have hadd :=
    (MeasureTheory.measurePreserving_add_left volume (intCast j)).quasiMeasurePreserving
  convert hadd.comp hrep using 1
  ext u i
  rfl

/- Apply the ENNReal tiling to `enorm F` and convert the finite
tsum to the real integrals of norms.  This certificate must precede Bochner
sum/integral interchange. -/
theorem summable_integral_norm_intVec_tiling {d : Nat}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
    (F : RealVec d → E) (hF : Integrable F volume) :
    Summable (fun j : IntVec d ↦
      ∫ u : Torus d, ‖F (intVecTranslate j u)‖ ∂volume) := by
  have htile := lintegral_intVec_tiling
    (fun x : RealVec d ↦ ‖F x‖ₑ) hF.aestronglyMeasurable.enorm
  have hne : (∑' j : IntVec d,
      ∫⁻ u : Torus d, ‖F (intVecTranslate j u)‖ₑ ∂volume) ≠ ∞ := by
    rw [← htile]
    exact hF.2.ne
  have hsum := ENNReal.summable_toReal hne
  convert hsum with j
  rw [MeasureTheory.integral_norm_eq_lintegral_enorm]
  exact hF.aestronglyMeasurable.comp_quasiMeasurePreserving
    (quasiMeasurePreserving_intVecTranslate j)

/- Use `summable_integral_norm_intVec_tiling` before the product fundamental-domain
Bochner integral decomposition. -/
theorem hasSum_integral_intVec_tiling {d : Nat}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
    (F : RealVec d → E) (hF : Integrable F volume) :
    HasSum
      (fun j : IntVec d ↦ ∫ u : Torus d, F (intVecTranslate j u) ∂volume)
      (∫ x : RealVec d, F x ∂volume) := by
  have hnorm := summable_integral_norm_intVec_tiling F hF
  have hcells : Summable (fun j : IntVec d ↦
      ∫ u : Torus d, F (intVecTranslate j u) ∂volume) := by
    apply hnorm.of_norm_bounded
    intro j
    exact MeasureTheory.norm_integral_le_integral_norm _
  let b : Module.Basis (Fin d) Real (RealVec d) :=
    Pi.basisFun Real (Fin d)
  let icoCube : Set (RealVec d) :=
    Set.univ.pi (fun _ : Fin d ↦ Ico (0 : Real) 1)
  let iocCube : Set (RealVec d) :=
    Set.univ.pi (fun _ : Fin d ↦ Ioc (0 : Real) 1)
  let e : IntVec d ≃
      (Submodule.span Int (Set.range b)).toAddSubgroup := by
    simpa [b] using intVecEquivZSpan d
  have hioc : iocUnitCubeHD d = iocCube := by
    ext x
    simp [iocUnitCubeHD, IntegerFrequenciesHD.Internal.iocUnitCubeHD,
      iocCube, Set.mem_pi]
  have hiocMeas : MeasurableSet (iocUnitCubeHD d) := by
    rw [hioc]
    exact MeasurableSet.univ_pi (fun _ : Fin d ↦ measurableSet_Ioc)
  have hae : icoCube =ᵐ[volume] iocCube := by
    exact Measure.univ_pi_Ico_ae_eq_Icc.trans
      Measure.univ_pi_Ioc_ae_eq_Icc.symm
  have hrestrict : volume.restrict icoCube =
      volume.restrict (iocUnitCubeHD d) := by
    rw [hioc]
    exact Measure.restrict_congr_set hae
  letI : Countable
      (Submodule.span Int (Set.range b)).toAddSubgroup :=
    Countable.of_equiv (IntVec d) e
  have hfd : IsAddFundamentalDomain
      (Submodule.span Int (Set.range b)).toAddSubgroup icoCube volume := by
    simpa [b, icoCube, ZSpan.fundamentalDomain_pi_basisFun] using
      ZSpan.isAddFundamentalDomain' b volume
  have hcell (j : IntVec d) :
      (∫ x : RealVec d in icoCube, F (e j +ᵥ x) ∂volume) =
        ∫ u : Torus d, F (intVecTranslate j u) ∂volume := by
    have htransport :=
      (measurePreserving_torusIocEquivHD d).integral_comp
        (torusIocEquivHD d).measurableEmbedding
        (fun u : {x : RealVec d // x ∈ iocUnitCubeHD d} ↦
          F (fun i ↦ (j i : Real) + (u : RealVec d) i))
    calc
      (∫ x : RealVec d in icoCube, F (e j +ᵥ x) ∂volume) =
          ∫ x : RealVec d in iocUnitCubeHD d,
            F (fun i ↦ (j i : Real) + x i) ∂volume := by
        rw [hrestrict]
        congr 1
      _ = ∫ u : {x : RealVec d // x ∈ iocUnitCubeHD d},
          F (fun i ↦ (j i : Real) + (u : RealVec d) i)
            ∂(Measure.comap Subtype.val volume) := by
        symm
        exact MeasureTheory.integral_subtype_comap hiocMeas
          (fun x : RealVec d ↦ F (fun i ↦ (j i : Real) + x i))
      _ = ∫ u : Torus d, F (intVecTranslate j u) ∂volume := by
        rw [← htransport]
        apply MeasureTheory.integral_congr_ae
        filter_upwards with u
        congr 1
  have htotal : (∫ x : RealVec d, F x ∂volume) =
      ∑' j : IntVec d, ∫ u : Torus d,
        F (intVecTranslate j u) ∂volume := by
    calc
      (∫ x : RealVec d, F x ∂volume) =
          ∑' g : (Submodule.span Int (Set.range b)).toAddSubgroup,
            ∫ x : RealVec d in icoCube, F (g +ᵥ x) ∂volume :=
        hfd.integral_eq_tsum'' F hF
      _ = ∑' j : IntVec d,
          ∫ x : RealVec d in icoCube, F (e j +ᵥ x) ∂volume := by
        rw [← e.tsum_eq]
      _ = ∑' j : IntVec d, ∫ u : Torus d,
          F (intVecTranslate j u) ∂volume := tsum_congr hcell
  rw [htotal]
  exact hcells.hasSum

/- Apply the ENNReal tiling to `enorm F`; every torus term is
zero by the simultaneous slice AE hypotheses, so the whole norm lintegral is
zero and hence `F=0` AE. -/
theorem ae_of_ae_all_intVec_slices {d : Nat}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
    (F : RealVec d → E) (hF : StronglyMeasurable F)
    (hslices : ∀ j : IntVec d,
      (fun u : Torus d ↦ F (intVecTranslate j u)) =ᵐ[volume]
        (fun _ ↦ 0)) :
    F =ᵐ[volume] (fun _ ↦ 0) := by
  have hmeas : Measurable (fun x : RealVec d ↦ ‖F x‖ₑ) := hF.enorm
  have hzeroIntegral : (∫⁻ x : RealVec d, ‖F x‖ₑ ∂volume) = 0 := by
    rw [lintegral_intVec_tiling (fun x : RealVec d ↦ ‖F x‖ₑ)
      hmeas.aemeasurable]
    rw [ENNReal.tsum_eq_zero]
    intro j
    have hsliceNorm :
        (fun u : Torus d ↦ ‖F (intVecTranslate j u)‖ₑ) =ᵐ[volume]
          (fun _ ↦ 0) := by
      filter_upwards [hslices j] with u hu
      rw [hu]
      exact enorm_zero
    rw [MeasureTheory.lintegral_congr_ae hsliceNorm]
    exact MeasureTheory.lintegral_zero
  have hnormZero : (fun x : RealVec d ↦ ‖F x‖ₑ) =ᵐ[volume]
      (fun _ ↦ 0) :=
    (MeasureTheory.lintegral_eq_zero_iff hmeas).mp hzeroIntegral
  filter_upwards [hnormZero] with x hx
  have hxzero : ‖F x‖ₑ = 0 := by simpa using hx
  exact enorm_eq_zero.mp hxzero

/- Exact generic scalar quadratic-weight summability theorem. -/
theorem summable_one_add_int_sq_inv :
    Summable (fun q : Int ↦ (1 + (q : Real) ^ 2)⁻¹) := by
  exact Theorem12.Generic.summable_one_add_int_sq_inv

/- Thin wrapper around the proved multitorus two-sided
Birkhoff theorem, retaining the signed subtraction orbit and `2*N+1`. -/
theorem twoSided_average_torusTranslation {d : Nat} {alpha : RealVec d}
    (hAlpha : RationallyIndependentWithOneHD alpha)
    (phi : Torus d → Real) (hphi : Integrable phi volume) :
    ∀ᵐ x : Torus d ∂volume,
      Tendsto
        (fun N : Nat ↦ (2 * (N : Real) + 1)⁻¹ *
          ∑ k ∈ Finset.Icc (-(N : Int)) (N : Int),
            phi (x - k • alphaTorusHD alpha))
        atTop (nhds (∫ y, phi y ∂volume)) := by
  change IntegerFrequenciesHD.RationallyIndependentWithOne alpha at hAlpha
  have ha : alphaTorusHD alpha =
      IntegerFrequenciesHD.Internal.alphaTorus alpha := by
    rfl
  rw [ha]
  have h := IntegerFrequenciesHD.twoSided_average_torusTranslation
    (d := d) hAlpha phi hphi
  exact h

/- Exact adapter of the proved meromorphic Jensen density
comparison, with multiplicities owned by one counting-data record. -/
theorem jensen_density_comparison (F : Complex → Complex)
    (data : Theorem12.Generic.MeromorphicCountingData F)
    (hF0analytic : AnalyticAt Complex F 0) (hF0 : F 0 ≠ 0)
    (R : Nat → Real) (hRpos : ∀ m, 0 < R m)
    (hRtendsto : Tendsto R atTop atTop)
    (hclean : ∀ m z, ‖z‖ = R m → AnalyticAt Complex F z ∧ F z ≠ 0)
    (sigma rho tau : Real) (b : Nat → Real)
    (hb : Tendsto (fun m ↦ b m / R m) atTop (nhds 0))
    (hboundary : ∀ᶠ m in atTop,
      Theorem12.Generic.circleLogMean F (R m) ≤ 2 * tau * R m + b m)
    (hzero : ∀ epsilon : Real, 0 < epsilon → ∀ᶠ r : Real in atTop,
      2 * (sigma - epsilon) * r ≤
        (Theorem12.Generic.zeroCount data r : Real))
    (hpole : ∀ epsilon : Real, 0 < epsilon → ∀ᶠ r : Real in atTop,
      (Theorem12.Generic.poleCount data r : Real) ≤
        2 * (rho + epsilon) * r) :
    sigma ≤ rho + tau := by
  exact Theorem12.Generic.jensen_density_comparison F data hF0analytic hF0 R
    hRpos hRtendsto hclean sigma rho tau b hb hboundary hzero hpole

end UniversalCompletenessHD.Internal
