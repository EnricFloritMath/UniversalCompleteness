import AsymptoticallyIntegerHD.Completeness
import AsymptoticallyIntegerHD.Definitions
import AsymptoticallyIntegerHD.InfiniteAssembly

/-!
# From a small annihilator to genuine restricted-L2 noncompleteness

The declarations below turn the small annihilator into failure of
restricted-L2 completeness.
-/

noncomputable section

open MeasureTheory Set Topology
open scoped ENNReal

namespace AsymptoticallyIntegerHD

/-!
`SmallAnnihilatorHD.conj_memLp_restrict`. Dependency: `SmallAnnihilatorHD`.
Proof idea: restrict `W.F_memLp`, apply complex conjugation, and normalize the
raw function.  Finite measure of `W.S` is not needed.
-/
theorem SmallAnnihilatorHD.conj_memLp_restrict {d : Nat}
    {delta : IntVec d → RealVec d} {mu : Real}
    (W : SmallAnnihilatorHD delta mu) :
    MemLp (fun x : RealVec d => starRingEnd Complex (W.F x))
      (2 : ENNReal) (volume.restrict W.S) := by
  change MemLp (star W.F) (2 : ENNReal) (volume.restrict W.S)
  exact (W.F_memLp.mono_measure Measure.restrict_le_self).star

/-!
`SmallAnnihilatorHD.toRestrictedLp`. Dependency: `SmallAnnihilatorHD.conj_memLp_restrict`.
The actual restricted-L2 class represented by the conjugate of the unique
annihilator witness.
-/
def SmallAnnihilatorHD.toRestrictedLp {d : Nat}
    {delta : IntVec d → RealVec d} {mu : Real}
    (W : SmallAnnihilatorHD delta mu) :
    Lp Complex (2 : ENNReal) (volume.restrict W.S) :=
  W.conj_memLp_restrict.toLp
    (fun x : RealVec d => starRingEnd Complex (W.F x))

/- Proof idea: obtain vanishing on `volume.restrict W.S`, conjugate back, combine
with a.e. support on the complementary restriction, and contradict ambient
a.e. nonzeroness. -/
theorem SmallAnnihilatorHD.toRestrictedLp_ne_zero {d : Nat}
    {delta : IntVec d → RealVec d} {mu : Real}
    (W : SmallAnnihilatorHD delta mu) :
    W.toRestrictedLp ≠ 0 := by
  intro hzero
  have hcoeZero :
      (⇑W.toRestrictedLp : RealVec d → Complex) =ᵐ[volume.restrict W.S] 0 := by
    rw [hzero]
    exact Lp.coeFn_zero Complex (2 : ENNReal) (volume.restrict W.S)
  have hstarZero :
      (fun x : RealVec d ↦ starRingEnd Complex (W.F x))
        =ᵐ[volume.restrict W.S] 0 :=
    W.conj_memLp_restrict.coeFn_toLp.symm.trans hcoeZero
  have hFZeroOn : W.F =ᵐ[volume.restrict W.S] 0 := by
    filter_upwards [hstarZero] with x hx
    have h := congrArg (starRingEnd Complex) hx
    simpa using h
  have hFZeroOff : W.F =ᵐ[volume.restrict W.Sᶜ] 0 := by
    filter_upwards [ae_restrict_of_ae W.F_supported,
      ae_restrict_mem W.S_measurable.compl] with x hx hxc
    exact hx hxc
  exact W.F_ae_ne_zero
    (ae_of_ae_restrict_of_ae_restrict_compl W.S hFZeroOn hFZeroOff)

/- Proof idea: unfold the restricted inner product.  Conjugate-linearity in the
first argument produces the positive integrand
`W.F x * fourierChar (frequency delta n) x`; support converts the restricted
integral to `inverseSample`, then `W.samples_zero n` closes the goal. -/
theorem SmallAnnihilatorHD.inner_restrictedExponential_eq_zero {d : Nat}
    {delta : IntVec d → RealVec d} {mu : Real}
    (W : SmallAnnihilatorHD delta mu) (n : IntVec d) :
    inner Complex W.toRestrictedLp
      (restrictedExponential W.S W.S_measurable W.measure_ne_top
        (frequency delta n)) = 0 := by
  rw [MeasureTheory.L2.inner_def]
  have hcoeF :
      (⇑W.toRestrictedLp : RealVec d → Complex) =ᵐ[volume.restrict W.S]
        (fun x : RealVec d ↦ starRingEnd Complex (W.F x)) :=
    W.conj_memLp_restrict.coeFn_toLp
  have hcoeExp :
      (⇑(restrictedExponential W.S W.S_measurable W.measure_ne_top
          (frequency delta n)) : RealVec d → Complex)
        =ᵐ[volume.restrict W.S] fourierChar (frequency delta n) :=
    (Internal.restrictedExponential_memLp W.S W.S_measurable W.measure_ne_top
      (frequency delta n)).coeFn_toLp
  calc
    (∫ x : RealVec d, inner Complex (W.toRestrictedLp x)
        (restrictedExponential W.S W.S_measurable W.measure_ne_top
          (frequency delta n) x) ∂(volume.restrict W.S)) =
        ∫ x in W.S, W.F x * fourierChar (frequency delta n) x := by
      apply integral_congr_ae
      filter_upwards [hcoeF, hcoeExp] with x hxF hxExp
      rw [hxF, hxExp]
      simp [mul_comm]
    _ = ∫ x : RealVec d, W.F x * fourierChar (frequency delta n) x := by
      apply setIntegral_eq_integral_of_ae_compl_eq_zero
      filter_upwards [W.F_supported] with x hx hnot
      rw [hx hnot, zero_mul]
    _ = inverseSample W.F (frequency delta n) := by
      rw [inverseSample, inverseSampleOn, setIntegral_univ]
    _ = 0 := W.samples_zero n

/- Proof idea: use density and the continuous inner functional, establish zero on
generators by `SmallAnnihilatorHD.inner_restrictedExponential_eq_zero`, extend by `Submodule.span_induction`, and contradict
`SmallAnnihilatorHD.toRestrictedLp_ne_zero`.  No projection or algebraic-span closedness is assumed. -/
theorem not_complete_of_annihilator_hd {d : Nat}
    {delta : IntVec d → RealVec d} {mu : Real}
    (W : SmallAnnihilatorHD delta mu) :
    ¬ ExponentialCompleteInL2HD
      (frequencySet delta) W.S W.S_measurable W.measure_ne_top := by
  intro hcomplete
  apply W.toRestrictedLp_ne_zero
  apply hcomplete.eq_zero_of_inner_left Complex
  intro v hv
  change v ∈ exponentialSpan (frequencySet delta) W.S W.S_measurable
    W.measure_ne_top at hv
  change v ∈ Submodule.span Complex
    {f | ∃ xi ∈ frequencySet delta,
      f = restrictedExponential W.S W.S_measurable W.measure_ne_top xi} at hv
  induction hv using Submodule.span_induction with
  | mem f hf =>
      rcases hf with ⟨xi, ⟨n, rfl⟩, rfl⟩
      exact W.inner_restrictedExponential_eq_zero n
  | zero => simp
  | add x y _ _ hx hy => simp [inner_add_right, hx, hy]
  | smul c x _ hx => simp [inner_smul_right, hx]

end AsymptoticallyIntegerHD
