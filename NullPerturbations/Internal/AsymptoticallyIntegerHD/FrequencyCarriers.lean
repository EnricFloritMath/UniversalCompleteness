import AsymptoticallyIntegerHD.Definitions
import AsymptoticallyIntegerHD.DyadicBlocks
import AsymptoticallyIntegerHD.BlockMultipliers

/-! # Finite vector translations and frequency carriers

This module constructs finite vector translations and frequency carriers
and proves their analytic properties.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Pointwise

namespace AsymptoticallyIntegerHD

namespace Internal

/-- Translation with positive Fourier-sample multiplier. -/
def vectorTranslate {d : Nat} (a : RealVec d) (F : RealVec d → Complex)
    (x : RealVec d) : Complex := F (x - a)

/-- Move a carrier near an integer origin back to the cube. -/
def recenterAtIntegerVector {d : Nat} (M : IntVec d)
    (F : RealVec d → Complex) (x : RealVec d) : Complex :=
  F (integerEmbed M + x)

private theorem fourierChar_add_space {d : Nat} (xi x y : RealVec d) :
    fourierChar xi (x + y) = fourierChar xi x * fourierChar xi y := by
  unfold fourierChar
  rw [← Complex.exp_add]
  congr 1
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  push_cast
  ring

private theorem fourierChar_norm {d : Nat} (xi x : RealVec d) :
    ‖fourierChar xi x‖ = 1 := by
  unfold fourierChar
  rw [Complex.norm_exp]
  norm_num

private theorem integrable_mul_fourierChar {d : Nat}
    (F : RealVec d → Complex) (hF : Integrable F volume) (xi : RealVec d) :
    Integrable (fun x => F x * fourierChar xi x) volume := by
  apply hF.mul_bdd (c := 1)
  · exact (show Continuous (fun x => fourierChar xi x) by
      unfold fourierChar
      fun_prop).aestronglyMeasurable
  · filter_upwards [] with x
    rw [fourierChar_norm]

private theorem inverseSample_vectorTranslate {d : Nat} (a : RealVec d)
    (F : RealVec d → Complex) (xi : RealVec d) :
    inverseSample (vectorTranslate a F) xi =
      fourierChar xi a * inverseSample F xi := by
  simp only [inverseSample, inverseSampleOn, Measure.restrict_univ]
  calc
    (∫ x : RealVec d, vectorTranslate a F x * fourierChar xi x) =
        ∫ x : RealVec d, F x * fourierChar xi (x + a) := by
      simpa [vectorTranslate, sub_eq_add_neg, add_assoc] using
        (integral_add_right_eq_self
          (fun x : RealVec d => F x * fourierChar xi (x + a)) (-a))
    _ = ∫ x : RealVec d,
        fourierChar xi a * (F x * fourierChar xi x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [fourierChar_add_space]
      ring
    _ = fourierChar xi a *
        (∫ x : RealVec d, F x * fourierChar xi x) := by
      rw [integral_const_mul]

private theorem vectorTranslate_supported {d : Nat}
    (a : RealVec d) (A : Set (RealVec d)) (F : RealVec d → Complex)
    (hFsupport : AESupportedIn F A) :
    AESupportedIn (vectorTranslate a F) (a +ᵥ A) := by
  have hpres : MeasurePreserving (fun x : RealVec d => x + (-a)) volume volume :=
    measurePreserving_add_right volume (-a)
  have hpull := hpres.quasiMeasurePreserving.tendsto_ae.eventually hFsupport
  filter_upwards [hpull] with x hx
  intro hxout
  apply hx
  intro hin
  apply hxout
  apply Set.mem_vadd_set.mpr
  refine ⟨x - a, hin, ?_⟩
  change a + (x - a) = x
  abel

private theorem norm_sq_finsetSum_of_pairwise_zero {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → Complex)
    (hz : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → f i = 0 ∨ f j = 0) :
    ‖∑ i ∈ s, f i‖ ^ 2 = ∑ i ∈ s, ‖f i‖ ^ 2 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s has ih =>
      by_cases ha : f a = 0
      · simp [has, ha, ih (fun i hi j hj hij => hz i (Finset.mem_insert_of_mem hi)
          j (Finset.mem_insert_of_mem hj) hij)]
      · have hrest : ∀ j ∈ s, f j = 0 := by
          intro j hj
          rcases hz a (Finset.mem_insert_self a s) j (Finset.mem_insert_of_mem hj)
              (by exact fun h => has (h ▸ hj)) with h | h
          · exact (ha h).elim
          · exact h
        have hsum : ∑ j ∈ s, f j = 0 := Finset.sum_eq_zero (fun j hj => hrest j hj)
        have hsumNorm : ∑ j ∈ s, ‖f j‖ ^ 2 = 0 := by
          apply Finset.sum_eq_zero
          intro j hj
          rw [hrest j hj, norm_zero, zero_pow (by norm_num : (2 : Nat) ≠ 0)]
        simp [has, hsum, hsumNorm]

/-- Restricted analysis, sample phase, and norm recentering. -/
theorem recenter_analysis_data {d : Nat} {M : IntVec d}
    {F : RealVec d → Complex} {omega : Set (RealVec d)}
    (homega : omega ⊆ unitCube d)
    (hstrong : AEStronglyMeasurable F volume)
    (hmem : MemLp F (2 : ENNReal) volume)
    (hsupp : AESupportedIn F (integerEmbed M +ᵥ omega)) :
    AEStronglyMeasurable (recenterAtIntegerVector M F)
        (volume.restrict (unitCube d)) ∧
      MemLp (recenterAtIntegerVector M F) (2 : ENNReal)
        (volume.restrict (unitCube d)) ∧
      (∀ xi, inverseSample F xi =
        fourierChar xi (integerEmbed M) *
          inverseSampleOn (unitCube d) (recenterAtIntegerVector M F) xi) ∧
      sqNormOn (unitCube d) (recenterAtIntegerVector M F) =
        sqNormOn Set.univ F := by
  have hpres : MeasurePreserving
      (fun x : RealVec d => integerEmbed M + x) volume volume :=
    measurePreserving_add_left volume (integerEmbed M)
  have hmeas : AEStronglyMeasurable
      (fun x : RealVec d => F (integerEmbed M + x)) volume :=
    hstrong.comp_measurePreserving hpres
  have hlp : MemLp (fun x : RealVec d => F (integerEmbed M + x))
      (2 : ENNReal) volume := hmem.comp_measurePreserving hpres
  have hpull : ∀ᵐ x : RealVec d ∂volume,
      integerEmbed M + x ∉ integerEmbed M +ᵥ omega →
        F (integerEmbed M + x) = 0 :=
    hpres.quasiMeasurePreserving.tendsto_ae.eventually hsupp
  have hrecSupp : AESupportedIn (recenterAtIntegerVector M F) (unitCube d) := by
    filter_upwards [hpull] with x hx
    intro hxout
    apply hx
    intro hmem
    have hxOmega : x ∈ omega := by
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hmem
      simpa using hmem
    exact hxout (homega hxOmega)
  have hsample (xi : RealVec d) : inverseSample F xi =
      fourierChar xi (integerEmbed M) *
        inverseSampleOn (unitCube d) (recenterAtIntegerVector M F) xi := by
    have hrestrict :
        inverseSampleOn (unitCube d) (recenterAtIntegerVector M F) xi =
          inverseSample (recenterAtIntegerVector M F) xi := by
      unfold inverseSample
      unfold inverseSampleOn
      rw [setIntegral_univ]
      apply setIntegral_eq_integral_of_ae_compl_eq_zero
      filter_upwards [hrecSupp] with x hx
      intro hxout
      rw [hx hxout, zero_mul]
    have htranslate : inverseSample (recenterAtIntegerVector M F) xi =
        fourierChar xi (-(integerEmbed M)) * inverseSample F xi := by
      rw [show recenterAtIntegerVector M F = vectorTranslate (-(integerEmbed M)) F by
        funext x
        simp only [recenterAtIntegerVector, vectorTranslate]
        congr 1
        abel]
      exact inverseSample_vectorTranslate (-(integerEmbed M)) F xi
    have hphase : fourierChar xi (integerEmbed M) *
        fourierChar xi (-(integerEmbed M)) = 1 := by
      rw [← fourierChar_add_space]
      simp [fourierChar]
    rw [hrestrict]
    calc
      inverseSample F xi = (1 : Complex) * inverseSample F xi := by simp
      _ = (fourierChar xi (integerEmbed M) *
          fourierChar xi (-(integerEmbed M))) * inverseSample F xi := by
        rw [hphase]
      _ = fourierChar xi (integerEmbed M) *
          inverseSample (recenterAtIntegerVector M F) xi := by
        rw [htranslate]
        ring
  have hnorm : sqNormOn (unitCube d) (recenterAtIntegerVector M F) =
      sqNormOn Set.univ F := by
    rw [sqNormOn, sqNormOn, setIntegral_univ]
    rw [setIntegral_eq_integral_of_ae_compl_eq_zero]
    · exact integral_add_left_eq_self
        (fun x : RealVec d => ‖F x‖ ^ 2) (integerEmbed M)
    · filter_upwards [hrecSupp] with x hx
      intro hxout
      rw [hx hxout, norm_zero, zero_pow (by norm_num : (2 : Nat) ≠ 0)]
  exact ⟨hmeas.mono_measure Measure.restrict_le_self, hlp.restrict _,
    hsample, hnorm⟩

/-- Finite integer-vector shift operator. -/
def shiftPolynomialCarrier {d : Nat} (c : Finsupp (IntVec d) Complex)
    (F : RealVec d → Complex) (x : RealVec d) : Complex :=
  c.support.sum fun a => c a * vectorTranslate (integerEmbed a) F x

end Internal

/-- Fourier sample of a finite shift operator. -/
theorem inverseSample_shiftPolynomialCarrier {d : Nat}
    {c : Finsupp (IntVec d) Complex} {F : RealVec d → Complex}
    (hF : Integrable F volume) (xi : RealVec d) :
    inverseSample (Internal.shiftPolynomialCarrier c F) xi =
      (c.support.sum fun a => c a * fourierChar xi (integerEmbed a)) *
        inverseSample F xi := by
  have hterm : ∀ a ∈ c.support, Integrable
      (fun x : RealVec d => c a * Internal.vectorTranslate (integerEmbed a) F x *
        fourierChar xi x) volume := by
    intro a ha
    have htrans : Integrable (Internal.vectorTranslate (integerEmbed a) F) volume := by
      change Integrable (fun x : RealVec d => F (x - integerEmbed a)) volume
      exact hF.comp_sub_right (integerEmbed a)
    simpa only [mul_assoc] using
      (Internal.integrable_mul_fourierChar _ htrans xi).const_mul (c a)
  unfold inverseSample
  unfold inverseSampleOn
  simp only [setIntegral_univ]
  simp only [Internal.shiftPolynomialCarrier, Finset.sum_mul]
  rw [integral_finsetSum c.support hterm]
  simp_rw [mul_assoc, integral_const_mul]
  have hsample (a : IntVec d) :
      (∫ x : RealVec d,
        Internal.vectorTranslate (integerEmbed a) F x * fourierChar xi x) =
        fourierChar xi (integerEmbed a) *
          ∫ x : RealVec d, F x * fourierChar xi x := by
    simpa only [inverseSample, inverseSampleOn, setIntegral_univ] using
      (Internal.inverseSample_vectorTranslate (integerEmbed a) F xi)
  simp_rw [hsample]

/-- Block-coefficient specialization of `inverseSample_shiftPolynomialCarrier`. -/
theorem inverseSample_blockShiftCarrier {d : Nat} (hd : 0 < d)
    {delta : IntVec d → RealVec d} {hdelta : TendsToZeroAtIntVecInfinity delta}
    {data : Internal.ModifiedFrequencyData delta} {mu0 : Real}
    {P : Internal.BlockParameters hd delta hdelta data mu0}
    (EC : Internal.ExceptionalConstants hd delta hdelta data P)
    (j : Nat) (r : Fin d) {F : RealVec d → Complex}
    (hF : Integrable F volume) (xi : RealVec d) :
    inverseSample (Internal.shiftPolynomialCarrier
      (Internal.blockShiftFinset data EC j r).coeff F) xi =
        blockMultiplier data j r xi * inverseSample F xi := by
  rw [inverseSample_shiftPolynomialCarrier hF]
  rw [(Internal.blockShiftFinset data EC j r).evaluation xi]

namespace Internal

/-- Seed-only polynomial translations along the first axis. -/
def axisPolynomialCarrierAtStep {d : Nat} (hd : 0 < d) (h : Real)
    (p : Polynomial Complex) (Phi : RealVec d → Complex)
    (x : RealVec d) : Complex :=
  p.support.sum fun k =>
    p.coeff k * vectorTranslate (((k : Real) * h) •
      basisVector (firstCoordinate hd)) Phi x

end Internal

/-- Fourier multiplier of the seed axis polynomial. -/
theorem inverseSample_axisPolynomialCarrierAtStep {d : Nat} (hd : 0 < d)
    (h : Real) (p : Polynomial Complex) {Phi : RealVec d → Complex}
    (hPhi : Integrable Phi volume) (xi : RealVec d) :
    inverseSample (Internal.axisPolynomialCarrierAtStep hd h p Phi) xi =
      p.eval (fourierChar xi (h • basisVector (Internal.firstCoordinate hd))) *
        inverseSample Phi xi := by
  have hterm : ∀ k ∈ p.support, Integrable
      (fun x : RealVec d => p.coeff k *
        Internal.vectorTranslate (((k : Real) * h) •
          basisVector (Internal.firstCoordinate hd)) Phi x * fourierChar xi x)
        volume := by
    intro k hk
    have htrans : Integrable
        (Internal.vectorTranslate (((k : Real) * h) •
          basisVector (Internal.firstCoordinate hd)) Phi) volume := by
      change Integrable (fun x : RealVec d =>
        Phi (x - ((k : Real) * h) •
          basisVector (Internal.firstCoordinate hd))) volume
      exact hPhi.comp_sub_right
        (((k : Real) * h) • basisVector (Internal.firstCoordinate hd))
    simpa only [mul_assoc] using
      (Internal.integrable_mul_fourierChar _ htrans xi).const_mul (p.coeff k)
  have hphase (k : Nat) :
      fourierChar xi (((k : Real) * h) •
          basisVector (Internal.firstCoordinate hd)) =
        fourierChar xi (h • basisVector (Internal.firstCoordinate hd)) ^ k := by
    unfold fourierChar
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    simp only [Pi.smul_apply, smul_eq_mul]
    have hsum :
        (∑ x : Fin d, (xi x : Complex) *
          ((((k : Real) * h) * basisVector (Internal.firstCoordinate hd) x : Real) :
            Complex)) =
          (k : Complex) * ∑ x : Fin d, (xi x : Complex) *
            (((h * basisVector (Internal.firstCoordinate hd) x : Real)) : Complex) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      push_cast
      ring
    rw [hsum]
    ring
  unfold inverseSample
  unfold inverseSampleOn
  simp only [setIntegral_univ]
  simp only [Internal.axisPolynomialCarrierAtStep, Finset.sum_mul]
  rw [integral_finsetSum p.support hterm]
  simp_rw [mul_assoc, integral_const_mul]
  have hsample (k : Nat) :
      (∫ x : RealVec d,
        Internal.vectorTranslate (((k : Real) * h) •
          basisVector (Internal.firstCoordinate hd)) Phi x * fourierChar xi x) =
        fourierChar xi (((k : Real) * h) •
          basisVector (Internal.firstCoordinate hd)) *
          ∫ x : RealVec d, Phi x * fourierChar xi x := by
    simpa only [inverseSample, inverseSampleOn, setIntegral_univ] using
      (Internal.inverseSample_vectorTranslate (((k : Real) * h) •
        basisVector (Internal.firstCoordinate hd)) Phi xi)
  simp_rw [hsample, hphase]
  rw [Polynomial.eval_eq_sum]
  simp only [Polynomial.sum]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  ring

namespace Internal

/-- Explicit carrier union for an axis-polynomial family. -/
def axisPolynomialCarrierSet {d : Nat} (hd : 0 < d) (h : Real)
    (p : Polynomial Complex) (A : Set (RealVec d)) : Set (RealVec d) :=
  ⋃ k ∈ p.support,
    (((k : Real) * h) • basisVector (firstCoordinate hd)) +ᵥ A

/-- Seed-axis carrier geometry and exact disjoint norm cost. -/
theorem axisPolynomialCarrier_geometry {d : Nat} (hd : 0 < d)
    (h : Real) (hh : 0 < h) (p : Polynomial Complex)
    {Phi : RealVec d → Complex} {A : Set (RealVec d)}
    (hAmeas : MeasurableSet A) (hPhiInt : Integrable Phi volume)
    (hPhiLp : MemLp Phi (2 : ENNReal) volume)
    (hPhiSupp : AESupportedIn Phi A)
    (hwidth : ∃ a b : Real, b - a < h ∧
      A ⊆ {x | a < x (firstCoordinate hd) ∧ x (firstCoordinate hd) < b}) :
    MeasurableSet (axisPolynomialCarrierSet hd h p A) ∧
      Set.Pairwise (↑p.support : Set Nat) (fun k l =>
        Disjoint
          ((((k : Real) * h) • basisVector (firstCoordinate hd)) +ᵥ A)
          ((((l : Real) * h) • basisVector (firstCoordinate hd)) +ᵥ A)) ∧
      AESupportedIn (axisPolynomialCarrierAtStep hd h p Phi)
        (axisPolynomialCarrierSet hd h p A) ∧
      volume (axisPolynomialCarrierSet hd h p A) ≤
        p.support.card * volume A ∧
      Integrable (axisPolynomialCarrierAtStep hd h p Phi) volume ∧
      MemLp (axisPolynomialCarrierAtStep hd h p Phi) (2 : ENNReal) volume ∧
      sqNormOn Set.univ (axisPolynomialCarrierAtStep hd h p Phi) =
        (p.support.sum fun k => ‖p.coeff k‖ ^ 2) * sqNormOn Set.univ Phi := by
  classical
  rcases hwidth with ⟨lower, upper, hwidth, hAslab⟩
  let shift : Nat → RealVec d := fun k =>
    ((k : Real) * h) • basisVector (firstCoordinate hd)
  have hsupportEach (k : Nat) :
      AESupportedIn (vectorTranslate (shift k) Phi) (shift k +ᵥ A) :=
    vectorTranslate_supported (shift k) A Phi hPhiSupp
  have hmeas : MeasurableSet (axisPolynomialCarrierSet hd h p A) := by
    simp only [axisPolynomialCarrierSet]
    exact MeasurableSet.biUnion p.support.countable_toSet
      (fun k _ => hAmeas.const_vadd _)
  have hpair : Set.Pairwise (↑p.support : Set Nat) (fun k l =>
      Disjoint (shift k +ᵥ A) (shift l +ᵥ A)) := by
    intro k hk l hl hkl
    rw [Set.disjoint_left]
    intro x hxk hxl
    rcases Set.mem_vadd_set.mp hxk with ⟨u, hu, hku⟩
    rcases Set.mem_vadd_set.mp hxl with ⟨v, hv, hlv⟩
    have huI := hAslab hu
    have hvI := hAslab hv
    have hku0 : (k : Real) * h + u (firstCoordinate hd) =
        x (firstCoordinate hd) := by
      have := congrFun hku (firstCoordinate hd)
      simpa [shift, basisVector] using this
    have hlv0 : (l : Real) * h + v (firstCoordinate hd) =
        x (firstCoordinate hd) := by
      have := congrFun hlv (firstCoordinate hd)
      simpa [shift, basisVector] using this
    rcases lt_or_gt_of_ne hkl with hlt | hgt
    · have hcast : (k : Real) + 1 ≤ (l : Real) := by
        exact_mod_cast Nat.succ_le_iff.mpr hlt
      have hmul : ((k : Real) + 1) * h ≤ (l : Real) * h :=
        mul_le_mul_of_nonneg_right hcast hh.le
      linarith [huI.2, hvI.1]
    · have hcast : (l : Real) + 1 ≤ (k : Real) := by
        exact_mod_cast Nat.succ_le_iff.mpr hgt
      have hmul : ((l : Real) + 1) * h ≤ (k : Real) * h :=
        mul_le_mul_of_nonneg_right hcast hh.le
      linarith [huI.1, hvI.2]
  have hsupport : AESupportedIn (axisPolynomialCarrierAtStep hd h p Phi)
      (axisPolynomialCarrierSet hd h p A) := by
    have hall : ∀ᵐ x : RealVec d ∂volume, ∀ k ∈ p.support,
        x ∉ shift k +ᵥ A → vectorTranslate (shift k) Phi x = 0 := by
      induction p.support using Finset.induction_on with
      | empty => simp
      | @insert k s hks ih =>
          filter_upwards [hsupportEach k, ih] with x hxk hxs
          simp only [Finset.mem_insert]
          intro l hl
          rcases hl with rfl | hl
          · exact hxk
          · exact hxs l hl
    filter_upwards [hall] with x hx
    intro hxout
    simp only [axisPolynomialCarrierAtStep]
    apply Finset.sum_eq_zero
    intro k hk
    have hout : x ∉ shift k +ᵥ A := by
      intro hmem
      apply hxout
      simp only [axisPolynomialCarrierSet, Set.mem_iUnion]
      exact ⟨k, ⟨hk, by simpa [shift] using hmem⟩⟩
    rw [hx k hk hout, mul_zero]
  have hmeasure : volume (axisPolynomialCarrierSet hd h p A) ≤
      p.support.card * volume A := by
    calc
      volume (axisPolynomialCarrierSet hd h p A) ≤
          ∑ k ∈ p.support, volume (shift k +ᵥ A) := by
        simpa only [axisPolynomialCarrierSet, shift] using
          (measure_biUnion_finset_le p.support
            (fun k => (((k : Real) * h) • basisVector (firstCoordinate hd)) +ᵥ A))
      _ = ∑ _k ∈ p.support, volume A := by
        apply Finset.sum_congr rfl
        intro k hk
        exact measure_vadd volume _ A
      _ = p.support.card * volume A := by simp
  have hIntEach (k : Nat) : Integrable
      (fun x => p.coeff k * vectorTranslate (shift k) Phi x) volume := by
    have ht : Integrable (vectorTranslate (shift k) Phi) volume := by
      change Integrable (fun x : RealVec d => Phi (x - shift k)) volume
      exact hPhiInt.comp_sub_right (shift k)
    exact ht.const_mul (p.coeff k)
  have hMemEach (k : Nat) : MemLp
      (fun x => p.coeff k * vectorTranslate (shift k) Phi x)
      (2 : ENNReal) volume := by
    have ht : MemLp (vectorTranslate (shift k) Phi) (2 : ENNReal) volume := by
      change MemLp (fun x : RealVec d => Phi (x + (-(shift k))))
        (2 : ENNReal) volume
      exact hPhiLp.comp_measurePreserving
        (measurePreserving_add_right volume (-(shift k)))
    exact ht.const_mul (p.coeff k)
  have hInt : Integrable (axisPolynomialCarrierAtStep hd h p Phi) volume := by
    have hsum := integrable_finsetSum' p.support (fun k _ => hIntEach k)
    apply hsum.congr
    filter_upwards [] with x
    simp only [axisPolynomialCarrierAtStep, shift, Finset.sum_apply]
  have hMem : MemLp (axisPolynomialCarrierAtStep hd h p Phi)
      (2 : ENNReal) volume := by
    have hsum : MemLp
        (∑ k ∈ p.support, fun x => p.coeff k * vectorTranslate (shift k) Phi x)
        (2 : ENNReal) volume := by
      induction p.support using Finset.induction_on with
      | empty => simp
      | @insert k s hks ih =>
          rw [Finset.sum_insert hks]
          exact (hMemEach k).add ih
    have hfun : axisPolynomialCarrierAtStep hd h p Phi =
        ∑ k ∈ p.support, fun x => p.coeff k * vectorTranslate (shift k) Phi x := by
      funext x
      simp only [axisPolynomialCarrierAtStep, shift, Finset.sum_apply]
    rw [hfun]
    exact hsum
  have hall : ∀ᵐ x : RealVec d ∂volume, ∀ k ∈ p.support,
      x ∉ shift k +ᵥ A → vectorTranslate (shift k) Phi x = 0 := by
    induction p.support using Finset.induction_on with
    | empty => simp
    | @insert k s hks ih =>
        filter_upwards [hsupportEach k, ih] with x hxk hxs
        simp only [Finset.mem_insert]
        intro l hl
        rcases hl with rfl | hl
        · exact hxk
        · exact hxs l hl
  have hpoint : ∀ᵐ x : RealVec d ∂volume,
      ‖axisPolynomialCarrierAtStep hd h p Phi x‖ ^ 2 =
        ∑ k ∈ p.support,
          ‖p.coeff k * vectorTranslate (shift k) Phi x‖ ^ 2 := by
    filter_upwards [hall] with x hx
    apply norm_sq_finsetSum_of_pairwise_zero
    intro i hi j hj hij
    by_cases hzi : vectorTranslate (shift i) Phi x = 0
    · exact Or.inl (by rw [hzi, mul_zero])
    by_cases hzj : vectorTranslate (shift j) Phi x = 0
    · exact Or.inr (by rw [hzj, mul_zero])
    exfalso
    have hxi : x ∈ shift i +ᵥ A := by
      by_contra hout
      exact hzi (hx i hi hout)
    have hxj : x ∈ shift j +ᵥ A := by
      by_contra hout
      exact hzj (hx j hj hout)
    exact (Set.disjoint_left.mp (hpair hi hj hij)) hxi hxj
  have hNormInt (k : Nat) : Integrable
      (fun x : RealVec d => ‖p.coeff k * vectorTranslate (shift k) Phi x‖ ^ 2)
      volume := (hMemEach k).integrable_norm_pow (by norm_num)
  have hterm (k : Nat) :
      (∫ x : RealVec d, ‖p.coeff k * vectorTranslate (shift k) Phi x‖ ^ 2) =
        ‖p.coeff k‖ ^ 2 * ∫ x : RealVec d, ‖Phi x‖ ^ 2 := by
    simp_rw [norm_mul, mul_pow]
    rw [integral_const_mul]
    congr 1
    change (∫ x : RealVec d, ‖Phi (x - shift k)‖ ^ 2) =
      ∫ x : RealVec d, ‖Phi x‖ ^ 2
    exact integral_add_right_eq_self
      (fun x : RealVec d => ‖Phi x‖ ^ 2) (-(shift k))
  refine ⟨hmeas, ?_, hsupport, hmeasure, hInt, hMem, ?_⟩
  · simpa only [shift] using hpair
  · rw [sqNormOn, sqNormOn, setIntegral_univ, setIntegral_univ]
    rw [integral_congr_ae hpoint]
    rw [integral_finsetSum p.support (fun k _ => hNormInt k)]
    simp_rw [hterm]
    rw [Finset.sum_mul]

/-- Explicit finite union supporting an integer-shift carrier. -/
def shiftPolynomialCarrierSet {d : Nat} (c : Finsupp (IntVec d) Complex)
    (M : IntVec d) (omega : Set (RealVec d)) : Set (RealVec d) :=
  ⋃ a ∈ c.support, integerEmbed (M + a) +ᵥ omega

/-- Support union, measure, and lattice-cube packing. -/
theorem shiftPolynomialCarrier_support_measure {d : Nat}
    (c : Finsupp (IntVec d) Complex) (M : IntVec d)
    {omega : Set (RealVec d)} {F : RealVec d → Complex}
    (homega : MeasurableSet omega)
    (homegaCube : omega ⊆ unitCube d)
    (hF : AESupportedIn F (integerEmbed M +ᵥ omega)) :
    MeasurableSet (shiftPolynomialCarrierSet c M omega) ∧
      AESupportedIn (shiftPolynomialCarrier c F)
        (shiftPolynomialCarrierSet c M omega) ∧
      volume (shiftPolynomialCarrierSet c M omega) ≤
        c.support.card * volume omega ∧
      Set.Pairwise (↑c.support : Set (IntVec d)) (fun a b =>
        Disjoint (integerEmbed (M + a) +ᵥ omega)
          (integerEmbed (M + b) +ᵥ omega)) := by
  classical
  have hEmbedAdd (a : IntVec d) :
      integerEmbed (M + a) = integerEmbed M + integerEmbed a := by
    ext i
    simp [integerEmbed]
  have hsupportEach (a : IntVec d) :
      AESupportedIn (vectorTranslate (integerEmbed a) F)
        (integerEmbed (M + a) +ᵥ omega) := by
    have h := vectorTranslate_supported (integerEmbed a)
      (integerEmbed M +ᵥ omega) F hF
    filter_upwards [h] with x hx
    intro hxout
    apply hx
    intro hmem
    apply hxout
    rcases Set.mem_vadd_set.mp hmem with ⟨y, hy, hxy⟩
    rcases Set.mem_vadd_set.mp hy with ⟨z, hz, hyz⟩
    apply Set.mem_vadd_set.mpr
    refine ⟨z, hz, ?_⟩
    change integerEmbed a + y = x at hxy
    change integerEmbed M + z = y at hyz
    rw [hEmbedAdd]
    calc
      (integerEmbed M + integerEmbed a) + z =
          integerEmbed a + (integerEmbed M + z) := by abel
      _ = integerEmbed a + y := by rw [hyz]
      _ = x := hxy
  have hmeas : MeasurableSet (shiftPolynomialCarrierSet c M omega) := by
    simp only [shiftPolynomialCarrierSet]
    exact MeasurableSet.biUnion c.support.countable_toSet
      (fun a _ => homega.const_vadd _)
  have hsupport : AESupportedIn (shiftPolynomialCarrier c F)
      (shiftPolynomialCarrierSet c M omega) := by
    have hall : ∀ᵐ x : RealVec d ∂volume, ∀ a ∈ c.support,
        x ∉ integerEmbed (M + a) +ᵥ omega →
          vectorTranslate (integerEmbed a) F x = 0 := by
      induction c.support using Finset.induction_on with
      | empty => simp
      | @insert a s has ih =>
          filter_upwards [hsupportEach a, ih] with x hxa hxs
          simp only [Finset.mem_insert]
          intro b hb
          rcases hb with rfl | hb
          · exact hxa
          · exact hxs b hb
    filter_upwards [hall] with x hx
    intro hxout
    simp only [shiftPolynomialCarrier]
    apply Finset.sum_eq_zero
    intro a ha
    have hout : x ∉ integerEmbed (M + a) +ᵥ omega := by
      intro hmem
      apply hxout
      simp only [shiftPolynomialCarrierSet, Set.mem_iUnion]
      exact ⟨a, ⟨ha, hmem⟩⟩
    rw [hx a ha hout, mul_zero]
  have hmeasure : volume (shiftPolynomialCarrierSet c M omega) ≤
      c.support.card * volume omega := by
    calc
      volume (shiftPolynomialCarrierSet c M omega) ≤
          ∑ a ∈ c.support, volume (integerEmbed (M + a) +ᵥ omega) := by
        simpa only [shiftPolynomialCarrierSet] using
          (measure_biUnion_finset_le c.support
            (fun a => integerEmbed (M + a) +ᵥ omega))
      _ = ∑ _a ∈ c.support, volume omega := by
        apply Finset.sum_congr rfl
        intro a ha
        exact measure_vadd volume _ omega
      _ = c.support.card * volume omega := by simp
  have hpair : Set.Pairwise (↑c.support : Set (IntVec d)) (fun a b =>
      Disjoint (integerEmbed (M + a) +ᵥ omega)
        (integerEmbed (M + b) +ᵥ omega)) := by
    intro a ha b hb hab
    rw [Set.disjoint_left]
    intro x hxa hxb
    rcases Set.mem_vadd_set.mp hxa with ⟨u, hu, hau⟩
    rcases Set.mem_vadd_set.mp hxb with ⟨v, hv, hbv⟩
    have hcoord : ∃ i : Fin d, a i ≠ b i := by
      by_contra hnone
      apply hab
      funext i
      exact not_ne_iff.mp (not_exists.mp hnone i)
    rcases hcoord with ⟨i, hi⟩
    have huI := homegaCube hu i
    have hvI := homegaCube hv i
    have haui : ((M i + a i : Int) : Real) + u i = x i := by
      have := congrFun hau i
      simpa [integerEmbed] using this
    have hbvi : ((M i + b i : Int) : Real) + v i = x i := by
      have := congrFun hbv i
      simpa [integerEmbed] using this
    rcases lt_or_gt_of_ne hi with hlt | hgt
    · have hgap : ((a i : Int) : Real) + 1 ≤ (b i : Int) := by
        exact_mod_cast (Int.add_one_le_iff.mpr hlt)
      push_cast at haui hbvi
      linarith [huI.2, hvI.1]
    · have hgap : ((b i : Int) : Real) + 1 ≤ (a i : Int) := by
        exact_mod_cast (Int.add_one_le_iff.mpr hgt)
      push_cast at haui hbvi
      linarith [huI.1, hvI.2]
  exact ⟨hmeas, hsupport, hmeasure, hpair⟩

/-- Analytic closure and exact/safe squared-norm costs. -/
theorem shiftPolynomialCarrier_analytic_cost {d : Nat}
    (c : Finsupp (IntVec d) Complex) (M : IntVec d)
    {omega : Set (RealVec d)} {F : RealVec d → Complex}
    (hstrong : AEStronglyMeasurable F volume) (hInt : Integrable F volume)
    (hLp : MemLp F (2 : ENNReal) volume)
    (hSupp : AESupportedIn F (integerEmbed M +ᵥ omega)) :
    Integrable (shiftPolynomialCarrier c F) volume ∧
      MemLp (shiftPolynomialCarrier c F) (2 : ENNReal) volume ∧
      sqNormOn Set.univ (shiftPolynomialCarrier c F) ≤
        c.support.card * (c.support.sum fun a => ‖c a‖ ^ 2) *
          sqNormOn Set.univ F ∧
      ((Set.Pairwise (↑c.support : Set (IntVec d)) fun a b =>
        Disjoint (integerEmbed (M + a) +ᵥ omega)
          (integerEmbed (M + b) +ᵥ omega)) →
        sqNormOn Set.univ (shiftPolynomialCarrier c F) =
          (c.support.sum fun a => ‖c a‖ ^ 2) * sqNormOn Set.univ F) := by
  classical
  have _hstrong := hstrong
  have hIntEach (a : IntVec d) : Integrable
      (fun x => c a * vectorTranslate (integerEmbed a) F x) volume := by
    have ht : Integrable (vectorTranslate (integerEmbed a) F) volume := by
      change Integrable (fun x : RealVec d => F (x - integerEmbed a)) volume
      exact hInt.comp_sub_right (integerEmbed a)
    exact ht.const_mul (c a)
  have hMemEach (a : IntVec d) : MemLp
      (fun x => c a * vectorTranslate (integerEmbed a) F x)
      (2 : ENNReal) volume := by
    have ht : MemLp (vectorTranslate (integerEmbed a) F)
        (2 : ENNReal) volume := by
      change MemLp (fun x : RealVec d => F (x + (-(integerEmbed a))))
        (2 : ENNReal) volume
      exact hLp.comp_measurePreserving
        (measurePreserving_add_right volume (-(integerEmbed a)))
    exact ht.const_mul (c a)
  have hCarrierInt : Integrable (shiftPolynomialCarrier c F) volume := by
    have hsum := integrable_finsetSum' c.support (fun a _ => hIntEach a)
    apply hsum.congr
    filter_upwards [] with x
    simp only [shiftPolynomialCarrier, Finset.sum_apply]
  have hCarrierLp : MemLp (shiftPolynomialCarrier c F)
      (2 : ENNReal) volume := by
    have hsum : MemLp
        (∑ a ∈ c.support, fun x => c a * vectorTranslate (integerEmbed a) F x)
        (2 : ENNReal) volume := by
      induction c.support using Finset.induction_on with
      | empty => simp
      | @insert a s has ih =>
          rw [Finset.sum_insert has]
          exact (hMemEach a).add ih
    have hfun : shiftPolynomialCarrier c F =
        ∑ a ∈ c.support, fun x => c a * vectorTranslate (integerEmbed a) F x := by
      funext x
      simp only [shiftPolynomialCarrier, Finset.sum_apply]
    rw [hfun]
    exact hsum
  have hNormInt (a : IntVec d) : Integrable
      (fun x : RealVec d => ‖c a * vectorTranslate (integerEmbed a) F x‖ ^ 2)
      volume := (hMemEach a).integrable_norm_pow (by norm_num)
  have hterm (a : IntVec d) :
      (∫ x : RealVec d,
          ‖c a * vectorTranslate (integerEmbed a) F x‖ ^ 2) =
        ‖c a‖ ^ 2 * ∫ x : RealVec d, ‖F x‖ ^ 2 := by
    simp_rw [norm_mul, mul_pow]
    rw [integral_const_mul]
    congr 1
    change (∫ x : RealVec d, ‖F (x - integerEmbed a)‖ ^ 2) =
      ∫ x : RealVec d, ‖F x‖ ^ 2
    exact integral_add_right_eq_self
      (fun x : RealVec d => ‖F x‖ ^ 2) (-(integerEmbed a))
  have hpointBound (x : RealVec d) :
      ‖shiftPolynomialCarrier c F x‖ ^ 2 ≤
        c.support.card * ∑ a ∈ c.support,
          ‖c a * vectorTranslate (integerEmbed a) F x‖ ^ 2 := by
    have htri : ‖∑ a ∈ c.support,
        c a * vectorTranslate (integerEmbed a) F x‖ ≤
        ∑ a ∈ c.support, ‖c a * vectorTranslate (integerEmbed a) F x‖ :=
      norm_sum_le _ _
    have hsq : ‖∑ a ∈ c.support,
        c a * vectorTranslate (integerEmbed a) F x‖ ^ 2 ≤
        (∑ a ∈ c.support,
          ‖c a * vectorTranslate (integerEmbed a) F x‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 htri
    rw [shiftPolynomialCarrier]
    exact hsq.trans (sq_sum_le_card_mul_sum_sq (s := c.support)
      (f := fun a => ‖c a * vectorTranslate (integerEmbed a) F x‖))
  have hupperInt : Integrable (fun x : RealVec d =>
      c.support.card * ∑ a ∈ c.support,
        ‖c a * vectorTranslate (integerEmbed a) F x‖ ^ 2) volume := by
    apply Integrable.const_mul
    exact integrable_finsetSum c.support fun a _ => hNormInt a
  have hsafe : sqNormOn Set.univ (shiftPolynomialCarrier c F) ≤
      c.support.card * (c.support.sum fun a => ‖c a‖ ^ 2) *
        sqNormOn Set.univ F := by
    rw [sqNormOn, sqNormOn, setIntegral_univ, setIntegral_univ]
    calc
      (∫ x : RealVec d, ‖shiftPolynomialCarrier c F x‖ ^ 2) ≤
          ∫ x : RealVec d, c.support.card * ∑ a ∈ c.support,
            ‖c a * vectorTranslate (integerEmbed a) F x‖ ^ 2 := by
        apply integral_mono_ae
        · exact hCarrierLp.integrable_norm_pow (by norm_num)
        · exact hupperInt
        · exact Filter.Eventually.of_forall hpointBound
      _ = c.support.card * ∑ a ∈ c.support,
          (∫ x : RealVec d,
            ‖c a * vectorTranslate (integerEmbed a) F x‖ ^ 2) := by
        rw [integral_const_mul]
        congr 1
        rw [integral_finsetSum c.support (fun a _ => hNormInt a)]
      _ = c.support.card * ∑ a ∈ c.support,
          (‖c a‖ ^ 2 * ∫ x : RealVec d, ‖F x‖ ^ 2) := by
        simp_rw [hterm]
      _ = c.support.card * ((∑ a ∈ c.support, ‖c a‖ ^ 2) *
          ∫ x : RealVec d, ‖F x‖ ^ 2) := by
        congr 1
        rw [Finset.sum_mul]
      _ = c.support.card * (∑ a ∈ c.support, ‖c a‖ ^ 2) *
          ∫ x : RealVec d, ‖F x‖ ^ 2 := by
        ring
  have hexact (hpair : Set.Pairwise (↑c.support : Set (IntVec d)) fun a b =>
      Disjoint (integerEmbed (M + a) +ᵥ omega)
        (integerEmbed (M + b) +ᵥ omega)) :
      sqNormOn Set.univ (shiftPolynomialCarrier c F) =
        (c.support.sum fun a => ‖c a‖ ^ 2) * sqNormOn Set.univ F := by
    have hEmbedAdd (a : IntVec d) :
        integerEmbed (M + a) = integerEmbed M + integerEmbed a := by
      ext i
      simp [integerEmbed]
    have hsupportEach (a : IntVec d) :
        AESupportedIn (vectorTranslate (integerEmbed a) F)
          (integerEmbed (M + a) +ᵥ omega) := by
      have h := vectorTranslate_supported (integerEmbed a)
        (integerEmbed M +ᵥ omega) F hSupp
      filter_upwards [h] with x hx
      intro hxout
      apply hx
      intro hmem
      apply hxout
      rcases Set.mem_vadd_set.mp hmem with ⟨y, hy, hxy⟩
      rcases Set.mem_vadd_set.mp hy with ⟨z, hz, hyz⟩
      apply Set.mem_vadd_set.mpr
      refine ⟨z, hz, ?_⟩
      change integerEmbed a + y = x at hxy
      change integerEmbed M + z = y at hyz
      rw [hEmbedAdd]
      calc
        (integerEmbed M + integerEmbed a) + z =
            integerEmbed a + (integerEmbed M + z) := by abel
        _ = integerEmbed a + y := by rw [hyz]
        _ = x := hxy
    have hall : ∀ᵐ x : RealVec d ∂volume, ∀ a ∈ c.support,
        x ∉ integerEmbed (M + a) +ᵥ omega →
          vectorTranslate (integerEmbed a) F x = 0 := by
      induction c.support using Finset.induction_on with
      | empty => simp
      | @insert a s has ih =>
          filter_upwards [hsupportEach a, ih] with x hxa hxs
          simp only [Finset.mem_insert]
          intro b hb
          rcases hb with rfl | hb
          · exact hxa
          · exact hxs b hb
    have hpoint : ∀ᵐ x : RealVec d ∂volume,
        ‖shiftPolynomialCarrier c F x‖ ^ 2 =
          ∑ a ∈ c.support,
            ‖c a * vectorTranslate (integerEmbed a) F x‖ ^ 2 := by
      filter_upwards [hall] with x hx
      apply norm_sq_finsetSum_of_pairwise_zero
      intro a ha b hb hab
      by_cases hza : vectorTranslate (integerEmbed a) F x = 0
      · exact Or.inl (by rw [hza, mul_zero])
      by_cases hzb : vectorTranslate (integerEmbed b) F x = 0
      · exact Or.inr (by rw [hzb, mul_zero])
      exfalso
      have hxa : x ∈ integerEmbed (M + a) +ᵥ omega := by
        by_contra hout
        exact hza (hx a ha hout)
      have hxb : x ∈ integerEmbed (M + b) +ᵥ omega := by
        by_contra hout
        exact hzb (hx b hb hout)
      exact (Set.disjoint_left.mp (hpair ha hb hab)) hxa hxb
    rw [sqNormOn, sqNormOn, setIntegral_univ, setIntegral_univ]
    rw [integral_congr_ae hpoint]
    rw [integral_finsetSum c.support (fun a _ => hNormInt a)]
    simp_rw [hterm]
    rw [Finset.sum_mul]
  exact ⟨hCarrierInt, hCarrierLp, hsafe, hexact⟩

end Internal

/-- Final first-coordinate difference. -/
def firstCoordinateDifference {d : Nat} (hd : 0 < d)
    (G : RealVec d → Complex) (x : RealVec d) : Complex :=
  Internal.vectorTranslate (basisVector (Internal.firstCoordinate hd)) G x - G x

/-- Sample multiplier and exact zeros at integral vectors. -/
theorem inverseSample_firstCoordinateDifference {d : Nat} (hd : 0 < d)
    {G : RealVec d → Complex} (hG : Integrable G volume) (xi : RealVec d) :
    inverseSample (firstCoordinateDifference hd G) xi =
      (Complex.exp ((((2 * Real.pi * xi (Internal.firstCoordinate hd) : Real)) :
        Complex) * Complex.I) - 1) * inverseSample G xi ∧
    ∀ m : IntVec d,
      inverseSample (firstCoordinateDifference hd G) (integerEmbed m) = 0 := by
  let i0 : Fin d := Internal.firstCoordinate hd
  let e0 : RealVec d := basisVector i0
  have hshift : Integrable (Internal.vectorTranslate e0 G) volume := by
    change Integrable (fun x : RealVec d => G (x - e0)) volume
    exact hG.comp_sub_right e0
  have hbasis (eta : RealVec d) : fourierChar eta e0 =
      Complex.exp ((((2 * Real.pi * eta i0 : Real)) : Complex) * Complex.I) := by
    unfold fourierChar
    congr 1
    have hsum : (∑ i : Fin d, eta i * e0 i : Real) = eta i0 := by
      simp [e0]
    rw [hsum]
    push_cast
    ring
  have hformula (eta : RealVec d) :
      inverseSample (firstCoordinateDifference hd G) eta =
        (Complex.exp ((((2 * Real.pi * eta i0 : Real)) : Complex) * Complex.I) - 1) *
          inverseSample G eta := by
    unfold inverseSample
    unfold inverseSampleOn
    simp only [setIntegral_univ, firstCoordinateDifference, i0]
    simp_rw [sub_mul]
    rw [integral_sub (Internal.integrable_mul_fourierChar _ hshift eta)
      (Internal.integrable_mul_fourierChar _ hG eta)]
    have htrans :
        (∫ x : RealVec d,
          Internal.vectorTranslate e0 G x * fourierChar eta x) =
          fourierChar eta e0 * ∫ x : RealVec d, G x * fourierChar eta x := by
      simpa only [inverseSample, inverseSampleOn, setIntegral_univ] using
        (Internal.inverseSample_vectorTranslate e0 G eta)
    rw [htrans, hbasis]
    ring
  refine ⟨by simpa [i0] using hformula xi, ?_⟩
  intro m
  rw [hformula]
  have hexp :
      Complex.exp
        ((((2 * Real.pi * integerEmbed m i0 : Real)) : Complex) * Complex.I) = 1 := by
    rw [show ((((2 * Real.pi * integerEmbed m i0 : Real)) : Complex) * Complex.I) =
        (m i0 : Complex) * (2 * (Real.pi : Complex) * Complex.I) by
      simp [integerEmbed]
      ring]
    exact Complex.exp_int_mul_two_pi_mul_I (m i0)
  rw [hexp]
  simp

namespace Internal

/-- Support, measure, analytic, and norm cost of the difference. -/
theorem firstCoordinateDifference_support_cost {d : Nat} (hd : 0 < d)
    {G : RealVec d → Complex} {A : Set (RealVec d)}
    (hA : MeasurableSet A) (hstrong : AEStronglyMeasurable G volume)
    (hInt : Integrable G volume) (hLp : MemLp G (2 : ENNReal) volume)
    (hSupp : AESupportedIn G A) :
    MeasurableSet ((basisVector (firstCoordinate hd) +ᵥ A) ∪ A) ∧
      AEStronglyMeasurable (firstCoordinateDifference hd G) volume ∧
      Integrable (firstCoordinateDifference hd G) volume ∧
      MemLp (firstCoordinateDifference hd G) (2 : ENNReal) volume ∧
      AESupportedIn (firstCoordinateDifference hd G)
        ((basisVector (firstCoordinate hd) +ᵥ A) ∪ A) ∧
      volume ((basisVector (firstCoordinate hd) +ᵥ A) ∪ A) ≤ 2 * volume A ∧
      sqNormOn Set.univ (firstCoordinateDifference hd G) ≤
        4 * sqNormOn Set.univ G := by
  let e0 : RealVec d := basisVector (firstCoordinate hd)
  have hshiftStrong : AEStronglyMeasurable (vectorTranslate e0 G) volume := by
    change AEStronglyMeasurable (fun x : RealVec d => G (x + (-e0))) volume
    exact hstrong.comp_measurePreserving
      (measurePreserving_add_right volume (-e0))
  have hshiftInt : Integrable (vectorTranslate e0 G) volume := by
    change Integrable (fun x : RealVec d => G (x - e0)) volume
    exact hInt.comp_sub_right e0
  have hshiftMem : MemLp (vectorTranslate e0 G) (2 : ENNReal) volume := by
    change MemLp (fun x : RealVec d => G (x + (-e0))) (2 : ENNReal) volume
    exact hLp.comp_measurePreserving
      (measurePreserving_add_right volume (-e0))
  have hdiffStrong : AEStronglyMeasurable
      (firstCoordinateDifference hd G) volume := by
    change AEStronglyMeasurable (fun x => vectorTranslate e0 G x - G x) volume
    exact hshiftStrong.sub hstrong
  have hdiffInt : Integrable (firstCoordinateDifference hd G) volume := by
    change Integrable (fun x => vectorTranslate e0 G x - G x) volume
    exact hshiftInt.sub hInt
  have hdiffMem : MemLp (firstCoordinateDifference hd G)
      (2 : ENNReal) volume := by
    change MemLp (fun x => vectorTranslate e0 G x - G x) (2 : ENNReal) volume
    exact hshiftMem.sub hLp
  have hshiftSupp : AESupportedIn (vectorTranslate e0 G) (e0 +ᵥ A) :=
    vectorTranslate_supported e0 A G hSupp
  have hzero : AESupportedIn (firstCoordinateDifference hd G)
      ((e0 +ᵥ A) ∪ A) := by
    filter_upwards [hshiftSupp, hSupp] with x hshift hbase
    intro hout
    have houtShift : x ∉ e0 +ᵥ A := fun hx =>
      hout (Set.mem_union_left A hx)
    have houtBase : x ∉ A := fun hx =>
      hout (Set.mem_union_right (e0 +ᵥ A) hx)
    change vectorTranslate e0 G x - G x = 0
    rw [hshift houtShift, hbase houtBase, sub_self]
  have hmeasure : volume ((e0 +ᵥ A) ∪ A) ≤ 2 * volume A := by
    calc
      volume ((e0 +ᵥ A) ∪ A) ≤ volume (e0 +ᵥ A) + volume A :=
        MeasureTheory.measure_union_le (e0 +ᵥ A) A
      _ = volume A + volume A := by rw [measure_vadd]
      _ = 2 * volume A := by ring
  have hshiftNormInt : Integrable
      (fun x : RealVec d => ‖vectorTranslate e0 G x‖ ^ 2) volume :=
    hshiftMem.integrable_norm_pow (by norm_num)
  have hbaseNormInt : Integrable (fun x : RealVec d => ‖G x‖ ^ 2) volume :=
    hLp.integrable_norm_pow (by norm_num)
  have hdiffNormInt : Integrable
      (fun x : RealVec d => ‖firstCoordinateDifference hd G x‖ ^ 2) volume :=
    hdiffMem.integrable_norm_pow (by norm_num)
  have hbound (x : RealVec d) :
      ‖firstCoordinateDifference hd G x‖ ^ 2 ≤
        2 * ‖vectorTranslate e0 G x‖ ^ 2 + 2 * ‖G x‖ ^ 2 := by
    have htri : ‖vectorTranslate e0 G x - G x‖ ≤
        ‖vectorTranslate e0 G x‖ + ‖G x‖ := norm_sub_le _ _
    have hsquare : ‖vectorTranslate e0 G x - G x‖ ^ 2 ≤
        (‖vectorTranslate e0 G x‖ + ‖G x‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 htri
    change ‖vectorTranslate e0 G x - G x‖ ^ 2 ≤ _
    nlinarith [sq_nonneg (‖vectorTranslate e0 G x‖ - ‖G x‖)]
  have hcost : sqNormOn Set.univ (firstCoordinateDifference hd G) ≤
      4 * sqNormOn Set.univ G := by
    rw [sqNormOn, sqNormOn, setIntegral_univ, setIntegral_univ]
    calc
      (∫ x : RealVec d, ‖firstCoordinateDifference hd G x‖ ^ 2) ≤
          ∫ x : RealVec d,
            (2 * ‖vectorTranslate e0 G x‖ ^ 2 + 2 * ‖G x‖ ^ 2) := by
        apply integral_mono_ae hdiffNormInt
        · exact (hshiftNormInt.const_mul 2).add (hbaseNormInt.const_mul 2)
        · exact Filter.Eventually.of_forall hbound
      _ = 2 * (∫ x : RealVec d, ‖vectorTranslate e0 G x‖ ^ 2) +
          2 * (∫ x : RealVec d, ‖G x‖ ^ 2) := by
        rw [integral_add (hshiftNormInt.const_mul 2) (hbaseNormInt.const_mul 2)]
        rw [integral_const_mul, integral_const_mul]
      _ = 4 * (∫ x : RealVec d, ‖G x‖ ^ 2) := by
        rw [show (∫ x : RealVec d, ‖vectorTranslate e0 G x‖ ^ 2) =
            ∫ x : RealVec d, ‖G x‖ ^ 2 by
          change (∫ x : RealVec d, ‖G (x - e0)‖ ^ 2) =
            ∫ x : RealVec d, ‖G x‖ ^ 2
          exact integral_add_right_eq_self (fun x : RealVec d => ‖G x‖ ^ 2) (-e0)]
        ring
  have hsetMeas : MeasurableSet ((e0 +ᵥ A) ∪ A) :=
    (hA.const_vadd e0).union hA
  simpa only [e0] using
    ⟨hsetMeas, hdiffStrong, hdiffInt, hdiffMem, hzero, hmeasure, hcost⟩

/-- Exact doubled norm for disjoint translated support. -/
theorem firstCoordinateDifference_sqNorm_of_disjoint {d : Nat} (hd : 0 < d)
    {G : RealVec d → Complex} {A : Set (RealVec d)}
    (hA : MeasurableSet A)
    (hGmeas : AEStronglyMeasurable G volume)
    (hGLp : MemLp G (2 : ENNReal) volume)
    (hSupp : AESupportedIn G A)
    (hdis : Disjoint A (basisVector (firstCoordinate hd) +ᵥ A)) :
    sqNormOn Set.univ (firstCoordinateDifference hd G) =
      2 * sqNormOn Set.univ G := by
  have _hA := hA
  have _hGmeas := hGmeas
  let e0 : RealVec d := basisVector (firstCoordinate hd)
  have hshiftMem : MemLp (vectorTranslate e0 G) (2 : ENNReal) volume := by
    change MemLp (fun x : RealVec d => G (x + (-e0))) (2 : ENNReal) volume
    exact hGLp.comp_measurePreserving
      (measurePreserving_add_right volume (-e0))
  have hdiffMem : MemLp (firstCoordinateDifference hd G)
      (2 : ENNReal) volume := by
    change MemLp (fun x => vectorTranslate e0 G x - G x) (2 : ENNReal) volume
    exact hshiftMem.sub hGLp
  have hshiftSupp : AESupportedIn (vectorTranslate e0 G) (e0 +ᵥ A) :=
    vectorTranslate_supported e0 A G hSupp
  have hpoint : ∀ᵐ x : RealVec d ∂volume,
      ‖firstCoordinateDifference hd G x‖ ^ 2 =
        ‖vectorTranslate e0 G x‖ ^ 2 + ‖G x‖ ^ 2 := by
    filter_upwards [hshiftSupp, hSupp] with x hshift hbase
    by_cases hzShift : vectorTranslate e0 G x = 0
    · change ‖vectorTranslate e0 G x - G x‖ ^ 2 = _
      simp only [hzShift, norm_zero, zero_pow (by norm_num : (2 : Nat) ≠ 0),
        zero_sub, norm_neg, zero_add]
    by_cases hzBase : G x = 0
    · change ‖vectorTranslate e0 G x - G x‖ ^ 2 = _
      simp only [hzBase, norm_zero, zero_pow (by norm_num : (2 : Nat) ≠ 0),
        sub_zero, add_zero]
    exfalso
    have hxShift : x ∈ e0 +ᵥ A := by
      by_contra hout
      exact hzShift (hshift hout)
    have hxBase : x ∈ A := by
      by_contra hout
      exact hzBase (hbase hout)
    exact (Set.disjoint_left.mp (by simpa only [e0] using hdis)) hxBase hxShift
  have hshiftNormInt : Integrable
      (fun x : RealVec d => ‖vectorTranslate e0 G x‖ ^ 2) volume :=
    hshiftMem.integrable_norm_pow (by norm_num)
  have hbaseNormInt : Integrable (fun x : RealVec d => ‖G x‖ ^ 2) volume :=
    hGLp.integrable_norm_pow (by norm_num)
  rw [sqNormOn, sqNormOn, setIntegral_univ, setIntegral_univ]
  rw [integral_congr_ae hpoint]
  rw [integral_add hshiftNormInt hbaseNormInt]
  rw [show (∫ x : RealVec d, ‖vectorTranslate e0 G x‖ ^ 2) =
      ∫ x : RealVec d, ‖G x‖ ^ 2 by
    change (∫ x : RealVec d, ‖G (x - e0)‖ ^ 2) =
      ∫ x : RealVec d, ‖G x‖ ^ 2
    exact integral_add_right_eq_self (fun x : RealVec d => ‖G x‖ ^ 2) (-e0)]
  ring

end Internal

end AsymptoticallyIntegerHD
