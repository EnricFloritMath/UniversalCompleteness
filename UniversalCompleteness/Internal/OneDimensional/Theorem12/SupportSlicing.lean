import Theorem12.Definitions
import Theorem12.GenericAuxiliary

noncomputable section

open MeasureTheory Set
open scoped BigOperators ComplexConjugate ENNReal Topology

namespace Theorem12.Internal

/- Proof idea: use Mathlib's transparent set indicator pointwise. -/
def zeroExtension (S : Set ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  S.indicator f

/- Proof idea: identify the restricted integral with the whole-line indicator integral, conjugate
the zero equality, and normalize conjugation of the exponential at the unchanged real frequency. -/
theorem conj_zeroExtension_positiveSample (alpha : ℝ) (beta : ℚ)
    (S : Set ℝ) (hSmeas : MeasurableSet S) (f : ℝ → ℂ)
    (hf : Integrable f (volume.restrict S)) (n : ℤ)
    (hsample : fourierSampleOn S f (frequency alpha beta n) = 0) :
    (∫ x : ℝ, conj (zeroExtension S f x) *
      Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I *
        (frequency alpha beta n : ℂ) * (x : ℂ)) ∂volume) = 0 := by
  rw [fourierSampleOn, ← integral_indicator hSmeas] at hsample
  calc
    (∫ x : ℝ, conj (zeroExtension S f x) *
        Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I *
          (frequency alpha beta n : ℂ) * (x : ℂ)) ∂volume) =
      ∫ x : ℝ, conj (S.indicator
        (fun y => f y * Complex.exp (-((2 * Real.pi : ℝ) : ℂ) * Complex.I *
          (frequency alpha beta n : ℂ) * (y : ℂ))) x) ∂volume := by
        apply integral_congr_ae
        filter_upwards [] with x
        symm
        by_cases hx : x ∈ S
        · simp only [Set.indicator_of_mem hx, zeroExtension, map_mul]
          rw [← Complex.exp_conj]
          congr 2
          simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]
          ring
        · simp [Set.indicator_of_notMem hx, zeroExtension]
    _ = conj (∫ x : ℝ, S.indicator
        (fun y => f y * Complex.exp (-((2 * Real.pi : ℝ) : ℂ) * Complex.I *
          (frequency alpha beta n : ℂ) * (y : ℂ))) x ∂volume) := integral_conj
    _ = 0 := by rw [hsample]; simp

/- Proof idea: store the chosen representative together with strong measurability, integrability,
AE identification, every positive sample, support-measure control, and recovery of the input. -/
structure PositiveInputData (alpha : ℝ) (beta : ℚ) (S : Set ℝ) (f : ℝ → ℂ) where
  g : ℝ → ℂ
  stronglyMeasurable_g : StronglyMeasurable g
  integrable_g : Integrable g volume
  ae_eq_conj_zeroExtension :
    g =ᵐ[volume] (fun x => conj (zeroExtension S f x))
  positiveSamples : ∀ n : ℤ,
    (∫ x : ℝ, g x * Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I *
      (frequency alpha beta n : ℂ) * (x : ℂ)) ∂volume) = 0
  support_measure_eq :
    volume {x : ℝ | g x ≠ 0} = volume {x : ℝ | zeroExtension S f x ≠ 0}
  support_measure_le : volume {x : ℝ | g x ≠ 0} ≤ volume S
  recovery : g =ᵐ[volume] (fun _ => 0) →
    f =ᵐ[volume.restrict S] (fun _ => 0)

/- Proof idea: take a strongly measurable representative of the conjugated zero extension, transfer
integrability and samples by AE congruence, identify support measures, bound by `S`, and recover `f`. -/
theorem exists_positiveInputData (alpha : ℝ) (beta : ℚ) (S : Set ℝ)
    (hSmeas : MeasurableSet S) (hSlt : volume S < 1) (f : ℝ → ℂ)
    (hf : Integrable f (volume.restrict S))
    (hsample : ∀ n : ℤ,
      fourierSampleOn S f (frequency alpha beta n) = 0) :
    Nonempty (PositiveInputData alpha beta S f) := by
  let raw : ℝ → ℂ := fun x => conj (zeroExtension S f x)
  have hzero : Integrable (zeroExtension S f) volume := by
    simpa only [zeroExtension] using (integrable_indicator_iff hSmeas).2 hf
  have hraw : Integrable raw volume := by
    have hc := Complex.conjCLE.toContinuousLinearMap.integrable_comp hzero
    change Integrable (fun x => Complex.conjCLE (zeroExtension S f x)) volume
    exact hc
  let g : ℝ → ℂ := hraw.aestronglyMeasurable.mk raw
  have hraw_g : raw =ᵐ[volume] g :=
    hraw.aestronglyMeasurable.ae_eq_mk
  refine ⟨{
    g := g
    stronglyMeasurable_g := ?_
    integrable_g := ?_
    ae_eq_conj_zeroExtension := ?_
    positiveSamples := ?_
    support_measure_eq := ?_
    support_measure_le := ?_
    recovery := ?_ }⟩
  · exact hraw.aestronglyMeasurable.stronglyMeasurable_mk
  · exact hraw.congr hraw_g
  · exact hraw_g.symm
  · intro n
    calc
      (∫ x : ℝ, g x * Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I *
        (frequency alpha beta n : ℂ) * (x : ℂ)) ∂volume) =
          ∫ x : ℝ, raw x * Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I *
            (frequency alpha beta n : ℂ) * (x : ℂ)) ∂volume := by
        apply integral_congr_ae
        filter_upwards [hraw_g] with x hx
        rw [← hx]
      _ = 0 := conj_zeroExtension_positiveSample alpha beta S hSmeas f hf n
        (hsample n)
  · calc
      volume {x : ℝ | g x ≠ 0} = volume {x : ℝ | raw x ≠ 0} := by
        apply measure_congr
        filter_upwards [hraw_g] with x hx
        apply propext
        change (g x ≠ 0) ↔ (raw x ≠ 0)
        rw [← hx]
      _ = volume {x : ℝ | zeroExtension S f x ≠ 0} := by
        congr 1
        ext x
        simp only [Set.mem_setOf_eq, raw]
        exact not_congr (map_eq_zero (starRingEnd ℂ))
  · calc
      volume {x : ℝ | g x ≠ 0} = volume {x : ℝ | raw x ≠ 0} := by
        apply measure_congr
        filter_upwards [hraw_g] with x hx
        apply propext
        change (g x ≠ 0) ↔ (raw x ≠ 0)
        rw [← hx]
      _ = volume {x : ℝ | zeroExtension S f x ≠ 0} := by
        congr 1
        ext x
        simp only [Set.mem_setOf_eq, raw]
        exact not_congr (map_eq_zero (starRingEnd ℂ))
      _ ≤ volume S := by
        apply measure_mono
        intro x hx
        by_contra hxS
        apply hx
        simp [zeroExtension, Set.indicator_of_notMem hxS]
  · intro hgzero
    have hrawzero : raw =ᵐ[volume] (fun _ => 0) := hraw_g.trans hgzero
    have hrawzeroS : raw =ᵐ[volume.restrict S] (fun _ => 0) :=
      ae_mono Measure.restrict_le_self hrawzero
    have hind : zeroExtension S f =ᵐ[volume.restrict S] f :=
      indicator_ae_eq_restrict hSmeas
    filter_upwards [hrawzeroS, hind] with x hxraw hxind
    dsimp only [raw] at hxraw
    rw [hxind] at hxraw
    simpa only [map_eq_zero] using hxraw

/- Proof idea: evaluate the fixed representative at the integer plus the canonical unit representative. -/
def slice {alpha : ℝ} {beta : ℚ} {S : Set ℝ} {f : ℝ → ℂ}
    (data : PositiveInputData alpha beta S f) (j : ℤ)
    (u : AddCircle (1 : ℝ)) : ℂ :=
  data.g ((j : ℝ) + Theorem12.Generic.unitRep u)

/- Proof idea: restrict `data.integrable_g` to the cell `[j,j+1)`, translate it to `[0,1)`,
and use the unit-representative integration adapter. -/
theorem integrable_slice {alpha : ℝ} {beta : ℚ} {S : Set ℝ} {f : ℝ → ℂ}
    (data : PositiveInputData alpha beta S f) (j : ℤ) :
    Integrable (slice data j) AddCircle.haarAddCircle := by
  have hunit : Measurable Theorem12.Generic.unitRep := by
    refine measurable_of_continuousOn_compl_singleton
      (0 : AddCircle (1 : ℝ)) ?_
    intro x hx
    have hequiv : ContinuousAt
        (AddCircle.equivIco (1 : ℝ) 0) x :=
      AddCircle.continuousAt_equivIco (1 : ℝ) 0 hx
    exact (continuousAt_subtype_val.comp hequiv).continuousWithinAt
  have hmap : Measure.map Theorem12.Generic.unitRep
      AddCircle.haarAddCircle = volume.restrict (Set.Ico (0 : ℝ) 1) := by
    ext A hA
    rw [Measure.map_apply hunit hA,
      Theorem12.Generic.measure_unitRep_preimage A hA,
      Measure.restrict_apply hA]
  have hmp : MeasurePreserving Theorem12.Generic.unitRep
      AddCircle.haarAddCircle (volume.restrict (Set.Ico (0 : ℝ) 1)) :=
    ⟨hunit, hmap⟩
  have hg : Integrable (fun u : ℝ => data.g ((j : ℝ) + u))
      (volume.restrict (Set.Ico (0 : ℝ) 1)) :=
    (data.integrable_g.comp_add_left (j : ℝ)).integrableOn
  change Integrable
    ((fun u : ℝ => data.g ((j : ℝ) + u)) ∘ Theorem12.Generic.unitRep)
      AddCircle.haarAddCircle
  exact (hmp.integrable_comp hg.aestronglyMeasurable).2 hg

/- Proof idea: take the nonzero set of the slice of the fixed representative. -/
def sliceSupport {alpha : ℝ} {beta : ℚ} {S : Set ℝ} {f : ℝ → ℂ}
    (data : PositiveInputData alpha beta S f) (j : ℤ) :
    Set (AddCircle (1 : ℝ)) :=
  {u | slice data j u ≠ 0}

/- Proof idea: compose `data.stronglyMeasurable_g` with the cell map and take the preimage of
the open complement of the singleton zero. -/
theorem measurableSet_sliceSupport {alpha : ℝ} {beta : ℚ} {S : Set ℝ}
    {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f) (j : ℤ) :
    MeasurableSet (sliceSupport data j) := by
  have hunit : Measurable Theorem12.Generic.unitRep := by
    refine measurable_of_continuousOn_compl_singleton
      (0 : AddCircle (1 : ℝ)) ?_
    intro x hx
    have hequiv : ContinuousAt
        (AddCircle.equivIco (1 : ℝ) 0) x :=
      AddCircle.continuousAt_equivIco (1 : ℝ) 0 hx
    exact (continuousAt_subtype_val.comp hequiv).continuousWithinAt
  have harg : Measurable
      (fun u : AddCircle (1 : ℝ) =>
        (j : ℝ) + Theorem12.Generic.unitRep u) :=
    hunit.const_add (j : ℝ)
  have hs : StronglyMeasurable (slice data j) := by
    exact data.stronglyMeasurable_g.comp_measurable harg
  exact (measurableSet_singleton (0 : ℂ)).compl.preimage hs.measurable

/- Proof idea: measure the actual nonzero set of the one fixed representative `data.g`. -/
def supportMassENN {alpha : ℝ} {beta : ℚ} {S : Set ℝ} {f : ℝ → ℂ}
    (data : PositiveInputData alpha beta S f) : ENNReal :=
  volume {x : ℝ | data.g x ≠ 0}

/- Proof idea: apply integer tiling to the indicator of `{x | data.g x ≠ 0}` and identify each cell. -/
theorem tsum_sliceSupport_measure {alpha : ℝ} {beta : ℚ} {S : Set ℝ}
    {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f) :
    (∑' j : ℤ, AddCircle.haarAddCircle (sliceSupport data j)) =
      supportMassENN data := by
  let A : Set ℝ := {x : ℝ | data.g x ≠ 0}
  have hA : MeasurableSet A := by
    exact (measurableSet_singleton (0 : ℂ)).compl.preimage
      data.stronglyMeasurable_g.measurable
  have htile := Theorem12.Generic.lintegral_int_tiling
    (A.indicator (1 : ℝ → ENNReal))
    (measurable_const.indicator hA)
  rw [lintegral_indicator_one hA] at htile
  have hcell : ∀ j : ℤ,
      (∫⁻ u : AddCircle (1 : ℝ),
        A.indicator (1 : ℝ → ENNReal)
          ((j : ℝ) + Theorem12.Generic.unitRep u)
          ∂AddCircle.haarAddCircle) =
        AddCircle.haarAddCircle (sliceSupport data j) := by
    intro j
    rw [← lintegral_indicator_one (measurableSet_sliceSupport data j)]
    apply lintegral_congr
    intro u
    by_cases h : data.g ((j : ℝ) + Theorem12.Generic.unitRep u) ≠ 0
    · simp [A, sliceSupport, slice, h]
    · simp [A, sliceSupport, slice, h]
  rw [show supportMassENN data = volume A by rfl]
  calc
    (∑' j : ℤ, AddCircle.haarAddCircle (sliceSupport data j)) =
        ∑' j : ℤ, ∫⁻ u : AddCircle (1 : ℝ),
          A.indicator (1 : ℝ → ENNReal)
            ((j : ℝ) + Theorem12.Generic.unitRep u)
            ∂AddCircle.haarAddCircle := by
      congr 1
      funext j
      exact (hcell j).symm
    _ = volume A := htile.symm

/- Proof idea: apply integer tiling to `‖data.g‖`, use `data.integrable_g` for finiteness, and
convert the nonnegative ENNReal family to a real `HasSum` certificate. -/
theorem hasSum_integral_norm_slice {alpha : ℝ} {beta : ℚ} {S : Set ℝ}
    {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f) :
    HasSum
      (fun j : ℤ => ∫ u : AddCircle (1 : ℝ),
        ‖slice data j u‖ ∂AddCircle.haarAddCircle)
      (∫ x : ℝ, ‖data.g x‖ ∂volume) := by
  simpa only [slice] using
    Theorem12.Generic.integral_int_tiling_of_integrable
      (fun x : ℝ => ‖data.g x‖) data.integrable_g.norm

/- Proof idea: combine `data.support_measure_le` with the strict bound on `volume S`. -/
theorem supportMassENN_lt_one {alpha : ℝ} {beta : ℚ} {S : Set ℝ}
    {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f)
    (hSlt : volume S < 1) : supportMassENN data < 1 := by
  exact lt_of_le_of_lt data.support_measure_le hSlt

/- Proof idea: a value strictly below one cannot equal infinity. -/
theorem supportMassENN_ne_top {alpha : ℝ} {beta : ℚ} {S : Set ℝ}
    {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f)
    (hSlt : volume S < 1) : supportMassENN data ≠ ∞ := by
  intro htop
  have hlt := supportMassENN_lt_one data hSlt
  rw [htop] at hlt
  exact (not_lt_of_ge le_top) hlt

/- Proof idea: transparently convert the ENNReal support mass with `ENNReal.toReal`. -/
def supportMass {alpha : ℝ} {beta : ℚ} {S : Set ℝ} {f : ℝ → ℂ}
    (data : PositiveInputData alpha beta S f) : ℝ :=
  (supportMassENN data).toReal

/- Proof idea: apply `ENNReal.ofReal_toReal` using the non-top result `supportMassENN_ne_top`. -/
theorem ofReal_supportMass {alpha : ℝ} {beta : ℚ} {S : Set ℝ}
    {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f)
    (hSlt : volume S < 1) :
    ENNReal.ofReal (supportMass data) = supportMassENN data := by
  exact ENNReal.ofReal_toReal (supportMassENN_ne_top data hSlt)

/- Proof idea: use nonnegativity of `toReal` and transport `supportMassENN_lt_one` through the finite
round-trip bridge `ofReal_supportMass`. -/
theorem supportMass_mem_Ico {alpha : ℝ} {beta : ℚ} {S : Set ℝ}
    {f : ℝ → ℂ} (data : PositiveInputData alpha beta S f)
    (hSlt : volume S < 1) : supportMass data ∈ Set.Ico (0 : ℝ) 1 := by
  constructor
  · exact ENNReal.toReal_nonneg
  · rw [supportMass, ← ENNReal.toReal_one,
      ENNReal.toReal_lt_toReal (supportMassENN_ne_top data hSlt)
        ENNReal.one_ne_top]
    exact supportMassENN_lt_one data hSlt

end Theorem12.Internal
