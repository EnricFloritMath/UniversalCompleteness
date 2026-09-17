import AsymptoticallyIntegerHD.Definitions
import AsymptoticallyIntegerHD.PerturbedExponentials
import AsymptoticallyIntegerHD.PeriodicCarrier

/-! # Modified frequencies and thin interpolation

The modified-frequency interpolation statements extend the completed
one-dimensional `Theorem13.ThinInterpolation` module.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Pointwise

namespace AsymptoticallyIntegerHD

namespace Internal

/-- One coherent finite central modification. -/
structure ModifiedFrequencyData {d : Nat} (delta : IntVec d → RealVec d) where
  N : Nat
  C0 : Finset (IntVec d)
  mem_C0_iff : ∀ n, n ∈ C0 ↔ indexSize n ≤ N
  nu : IntVec d → RealVec d
  nu_inside : ∀ n ∈ C0, nu n = integerEmbed n
  nu_outside : ∀ n ∉ C0, nu n = frequency delta n
  perturb_le : ∀ n, ‖nu n - integerEmbed n‖ ≤ perturbRadius d

/-- Existence certificate for the cached central modification. -/
theorem modifiedFrequencyData_nonempty {d : Nat} (hd : 0 < d)
    (delta : IntVec d → RealVec d) (hdelta : TendsToZeroAtIntVecInfinity delta) :
    Nonempty (ModifiedFrequencyData delta) := by
  have hradius : 0 < perturbRadius d := by
    unfold perturbRadius
    positivity
  obtain ⟨N, hN⟩ := hdelta (perturbRadius d) hradius
  let C0 : Finset (IntVec d) := indexBall d N
  let nu : IntVec d → RealVec d := fun n =>
    if n ∈ C0 then integerEmbed n else frequency delta n
  refine ⟨{
    N := N
    C0 := C0
    mem_C0_iff := ?_
    nu := nu
    nu_inside := ?_
    nu_outside := ?_
    perturb_le := ?_ }⟩
  · intro n
    simp [C0]
  · intro n hn
    simp [nu, hn]
  · intro n hn
    simp [nu, hn]
  · intro n
    by_cases hn : n ∈ C0
    · simpa [nu, hn] using hradius.le
    · have hnsize : N ≤ indexSize n := by
        have hnnot : ¬indexSize n ≤ N := by
          intro hle
          apply hn
          simpa [C0] using hle
        omega
      have htail := (hN n hnsize).le
      have hdiff : frequency delta n - integerEmbed n = delta n := by
        ext i
        simp [frequency, integerEmbed]
      simpa [nu, hn, hdiff] using htail

/-- Construct the cached central modification from the null tail. -/
noncomputable def modifiedFrequencyData {d : Nat} (hd : 0 < d)
    (delta : IntVec d → RealVec d) (hdelta : TendsToZeroAtIntVecInfinity delta) :
    ModifiedFrequencyData delta :=
  Classical.choice (modifiedFrequencyData_nonempty hd delta hdelta)

/-- Exponential bounds for the exact stored modified family. -/
noncomputable def modifiedExponentialBounds {d : Nat} (hd : 0 < d)
    {delta : IntVec d → RealVec d} (data : ModifiedFrequencyData delta) :
    ExponentialBoundsHD data.nu :=
  smallPerturbation_exponentialBounds_hd hd data.nu data.perturb_le

/-- The sanitized family is injective. -/
theorem ModifiedFrequencyData.nu_injective {d : Nat} (hd : 0 < d)
    {delta : IntVec d → RealVec d} (data : ModifiedFrequencyData delta) :
    Function.Injective data.nu := by
  intro n m hnm
  apply integerEmbed_injective
  by_contra hne
  have hdist : ‖integerEmbed n - integerEmbed m‖ < 1 := by
    calc
      ‖integerEmbed n - integerEmbed m‖ =
          ‖(integerEmbed n - data.nu n) + (data.nu m - integerEmbed m)‖ := by
            rw [hnm]
            congr 1
            abel
      _ ≤ ‖integerEmbed n - data.nu n‖ + ‖data.nu m - integerEmbed m‖ :=
        norm_add_le _ _
      _ = ‖data.nu n - integerEmbed n‖ + ‖data.nu m - integerEmbed m‖ := by
        rw [norm_sub_rev]
      _ ≤ perturbRadius d + perturbRadius d :=
        add_le_add (data.perturb_le n) (data.perturb_le m)
      _ < 1 := by
        unfold perturbRadius
        have hdR : (1 : Real) ≤ d := by exact_mod_cast hd
        have hpid : (2 : Real) ≤ Real.pi * d := by
          calc
            (2 : Real) = 2 * 1 := by ring
            _ ≤ Real.pi * d :=
              mul_le_mul Real.two_le_pi hdR (by norm_num) Real.pi_pos.le
        rw [← add_div]
        rw [div_lt_one (by positivity)]
        nlinarith
  have hcoord (i : Fin d) :
      |((n i : Int) : Real) - ((m i : Int) : Real)| < 1 := by
    calc
      |((n i : Int) : Real) - ((m i : Int) : Real)| =
          ‖(integerEmbed n - integerEmbed m) i‖ := by
            simp [integerEmbed]
      _ ≤ ‖integerEmbed n - integerEmbed m‖ := norm_le_pi_norm _ i
      _ < 1 := hdist
  apply hne
  funext i
  have hiCast : ((|n i - m i| : Int) : Real) < 1 := by
    rw [Int.cast_abs, Int.cast_sub]
    exact hcoord i
  have hiInt : |n i - m i| < (1 : Int) := by
    exact_mod_cast hiCast
  change (n i : Real) = (m i : Real)
  exact_mod_cast sub_eq_zero.mp (Int.abs_lt_one_iff.mp hiInt)

/-- Original frequencies are injective on the sanitized tail. -/
theorem ModifiedFrequencyData.frequency_injective_outside_C0 {d : Nat}
    (hd : 0 < d) {delta : IntVec d → RealVec d}
    (data : ModifiedFrequencyData delta) :
    Set.InjOn (frequency delta) {n | n ∉ data.C0} := by
  intro n hn m hm hfreq
  apply data.nu_injective hd
  rw [data.nu_outside n hn, data.nu_outside m hm, hfreq]

end Internal

/-- One carrier reusable for every origin and data vector. -/
structure ThinCarrierHD {d : Nat} {delta : IntVec d → RealVec d}
    (data : Internal.ModifiedFrequencyData delta)
    (K : ExponentialBoundsHD data.nu) (D : Finset (IntVec d))
    (theta : Real) where
  omega : Set (RealVec d)
  omega_measurable : MeasurableSet omega
  omega_subset : omega ⊆ unitCube d
  volume_omega : volume omega = ENNReal.ofReal theta
  interpolate : (M : IntVec d) →
    ({n : IntVec d // n ∈ D} → Complex) → RealVec d → Complex
  interpolate_stronglyMeasurable : ∀ M v,
    StronglyMeasurable (interpolate M v)
  interpolate_integrable : ∀ M v, Integrable (interpolate M v) volume
  interpolate_memLp : ∀ M v, MemLp (interpolate M v) (2 : ENNReal) volume
  interpolate_supported : ∀ M v,
    AESupportedIn (interpolate M v) (integerEmbed M +ᵥ omega)
  interpolate_samples : ∀ M v n,
    inverseSample (interpolate M v) (frequency delta n.1) = v n
  interpolate_cost : ∀ M v,
    sqNormOn Set.univ (interpolate M v) ≤
      (2 / (K.lower * theta)) * ∑ n, ‖v n‖ ^ 2

namespace Internal

/-- Exact solution of a coercive finite Gram system. -/
structure CoerciveGramSolution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι Complex) (c : Real) (w : ι → Complex) where
  a : ι → Complex
  equation : G.mulVec a = w
  unique : ∀ b : ι → Complex, G.mulVec b = w → b = a
  energy_le : (gramQuadratic G a).re ≤ (1 / c) * ∑ i, ‖w i‖ ^ 2

/-- Existence certificate for the coercive finite Gram solution. -/
theorem coerciveGramSolution_nonempty {ι : Type*}
    [Fintype ι] [DecidableEq ι] (G : Matrix ι ι Complex) (c : Real)
    (w : ι → Complex) (hc : 0 < c)
    (hcoer : ∀ b : ι → Complex,
      c * ∑ i, ‖b i‖ ^ 2 ≤ (gramQuadratic G b).re) :
    Nonempty (CoerciveGramSolution G c w) := by
  let L : (ι → Complex) →ₗ[Complex] (ι → Complex) := Matrix.toLin' G
  have hinj : Function.Injective L := by
    intro x y hxy
    have hGxy : G.mulVec x = G.mulVec y := by
      simpa [L, Matrix.toLin'_apply] using hxy
    have hGsub : G.mulVec (x - y) = 0 := by
      rw [Matrix.mulVec_sub, hGxy, sub_self]
    have hquad : (gramQuadratic G (x - y)).re = 0 := by
      simp [gramQuadratic, hGsub]
    have hsum_nonneg : 0 ≤ ∑ i, ‖(x - y) i‖ ^ 2 := by positivity
    have hsum_zero : (∑ i, ‖(x - y) i‖ ^ 2) = 0 := by
      have hbound := hcoer (x - y)
      rw [hquad] at hbound
      nlinarith
    have hsub : x - y = 0 := by
      funext i
      have hall : (fun j => ‖(x - y) j‖ ^ 2) = 0 :=
        (Fintype.sum_eq_zero_iff_of_nonneg fun j => sq_nonneg ‖(x - y) j‖).1
          hsum_zero
      have hi : ‖(x - y) i‖ ^ 2 = 0 := congrFun hall i
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hi)
    exact sub_eq_zero.mp hsub
  have hsurj : Function.Surjective L :=
    LinearMap.injective_iff_surjective.mp hinj
  let a : ι → Complex := Classical.choose (hsurj w)
  have ha : L a = w := Classical.choose_spec (hsurj w)
  have haeq : G.mulVec a = w := by
    simpa [L, Matrix.toLin'_apply] using ha
  refine ⟨{
    a := a
    equation := haeq
    unique := ?_
    energy_le := ?_ }⟩
  · intro b hb
    apply hinj
    simp [L, Matrix.toLin'_apply, hb, haeq]
  · let E : Real := (gramQuadratic G a).re
    let A : Real := ∑ i, ‖a i‖ ^ 2
    let W : Real := ∑ i, ‖w i‖ ^ 2
    let S : Real := ∑ i, ‖a i‖ * ‖w i‖
    have hA : 0 ≤ A := by dsimp [A]; positivity
    have hW : 0 ≤ W := by dsimp [W]; positivity
    have hS : 0 ≤ S := by dsimp [S]; positivity
    have hcoerA : c * A ≤ E := by
      simpa [A, E] using hcoer a
    have hE : 0 ≤ E := (mul_nonneg hc.le hA).trans hcoerA
    have hEupper : E ≤ S := by
      calc
        E = (∑ i, starRingEnd Complex (a i) * w i).re := by
          simp [E, gramQuadratic, haeq]
        _ ≤ ‖∑ i, starRingEnd Complex (a i) * w i‖ := Complex.re_le_norm _
        _ ≤ ∑ i, ‖starRingEnd Complex (a i) * w i‖ := norm_sum_le _ _
        _ = S := by simp [S]
    have hcs : S ^ 2 ≤ A * W := by
      simpa [S, A, W] using
        (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
          (fun i => ‖a i‖) (fun i => ‖w i‖))
    have hEsq : E ^ 2 ≤ A * W :=
      (sq_le_sq₀ hE hS).2 hEupper |>.trans hcs
    by_cases hEzero : E = 0
    · change E ≤ (1 / c) * W
      rw [hEzero]
      exact mul_nonneg (by positivity) hW
    · have hEpos : 0 < E := lt_of_le_of_ne hE (Ne.symm hEzero)
      have hleft : c * E ^ 2 ≤ c * (A * W) :=
        mul_le_mul_of_nonneg_left hEsq hc.le
      have hright : c * A * W ≤ E * W :=
        mul_le_mul_of_nonneg_right hcoerA hW
      have hcw : c * E ≤ W := by nlinarith
      have hdiv : E ≤ W / c := (le_div_iff₀ hc).2 (by simpa [mul_comm] using hcw)
      simpa [E, W, one_div, div_eq_mul_inv, mul_comm] using hdiv

/-- Coercivity gives an exact inverse and quantitative cost. -/
noncomputable def coerciveGram_solve_with_cost {ι : Type*}
    [Fintype ι] [DecidableEq ι] (G : Matrix ι ι Complex) (c : Real)
    (w : ι → Complex) (hc : 0 < c)
    (hcoer : ∀ b : ι → Complex,
      c * ∑ i, ‖b i‖ ^ 2 ≤ (gramQuadratic G b).re) :
    CoerciveGramSolution G c w :=
  Classical.choice (coerciveGramSolution_nonempty G c w hc hcoer)

end Internal

/-- Existence certificate for the reusable thin interpolation carrier. -/
theorem thinCarrierHD_nonempty {d : Nat} (hd : 0 < d)
    {delta : IntVec d → RealVec d}
    (data : Internal.ModifiedFrequencyData delta)
    (K : ExponentialBoundsHD data.nu) (D : Finset (IntVec d))
    (hD : D.Nonempty) (hDoutside : ∀ n ∈ D, n ∉ data.C0)
    (theta : Real) (htheta0 : 0 < theta) (htheta1 : theta ≤ 1) :
    Nonempty (ThinCarrierHD data K D theta) := by
  have hexists := exists_coercive_stripedCarrier hd K D hD theta htheta0 htheta1
  let N : Nat := Classical.choose hexists
  have hexistsN := Classical.choose_spec hexists
  let hN : 0 < N := Classical.choose hexistsN
  have hcarrier := Classical.choose_spec hexistsN
  let Omega : Set (RealVec d) := stripedCarrier hd theta N
  have hOmega_measurable : MeasurableSet Omega := by
    simpa only [Omega, N] using hcarrier.1
  have hOmega_subset : Omega ⊆ unitCube d := by
    simpa only [Omega, N] using hcarrier.2.1
  have hOmega_volume : volume Omega = ENNReal.ofReal theta := by
    simpa only [Omega, N] using hcarrier.2.2.1
  let G : Matrix {n : IntVec d // n ∈ D} {n : IntVec d // n ∈ D} Complex :=
    Internal.gramMatrix data.nu D Omega
  let c : Real := K.lower * theta / 2
  have hc : 0 < c := by
    dsimp [c]
    exact div_pos (mul_pos K.lower_pos htheta0) (by norm_num)
  have hcoer : ∀ a : {n : IntVec d // n ∈ D} → Complex,
      c * ∑ n, ‖a n‖ ^ 2 ≤ (Internal.gramQuadratic G a).re := by
    intro a
    simpa only [c, G, Omega, N] using hcarrier.2.2.2 a
  have hchar_add (xi x y : RealVec d) :
      fourierChar xi (x + y) = fourierChar xi x * fourierChar xi y := by
    unfold fourierChar
    rw [← Complex.exp_add]
    congr 1
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    push_cast
    ring
  have hstar_fourier (eta x : RealVec d) :
      starRingEnd Complex (fourierChar eta x) =
        Complex.exp
          ((((-2 * Real.pi : Real) : Complex) * Complex.I) *
            ((∑ k : Fin d, eta k * x k : Real) : Complex)) := by
    unfold fourierChar
    rw [← Complex.exp_conj]
    congr 1
    apply Complex.ext <;> simp
  have hchar_sub (xi eta x : RealVec d) :
      fourierChar xi x * starRingEnd Complex (fourierChar eta x) =
        fourierChar (xi - eta) x := by
    rw [hstar_fourier]
    unfold fourierChar
    rw [← Complex.exp_add]
    congr 1
    push_cast
    simp only [Pi.sub_apply]
    have hsumC :
        (∑ k : Fin d, (((xi k - eta k : Real) : Complex) * (x k : Complex))) =
          (∑ k : Fin d, (xi k : Complex) * (x k : Complex)) -
            ∑ k : Fin d, (eta k : Complex) * (x k : Complex) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      push_cast
      ring
    rw [hsumC]
    ring
  have hchar_unit (xi x : RealVec d) :
      fourierChar xi x * starRingEnd Complex (fourierChar xi x) = 1 := by
    rw [hchar_sub]
    simp [fourierChar]
  let w : IntVec d → ({n : IntVec d // n ∈ D} → Complex) →
      {n : IntVec d // n ∈ D} → Complex := fun M v n =>
    starRingEnd Complex (fourierChar (data.nu n.1) (integerEmbed M)) * v n
  let sol : (M : IntVec d) → (v : {n : IntVec d // n ∈ D} → Complex) →
      Internal.CoerciveGramSolution G c (w M v) := fun M v =>
    Internal.coerciveGram_solve_with_cost G c (w M v) hc hcoer
  let synth : (M : IntVec d) → ({n : IntVec d // n ∈ D} → Complex) →
      RealVec d → Complex := fun M v x =>
    ∑ n, (sol M v).a n * starRingEnd Complex (fourierChar (data.nu n.1) x)
  let H : (M : IntVec d) → ({n : IntVec d // n ∈ D} → Complex) →
      RealVec d → Complex := fun M v => Omega.indicator (synth M v)
  let F : (M : IntVec d) → ({n : IntVec d // n ∈ D} → Complex) →
      RealVec d → Complex := fun M v x => H M v (x - integerEmbed M)
  have hchar_cont (xi : RealVec d) : Continuous (fourierChar xi) := by
    unfold fourierChar
    fun_prop
  have hsynth_cont (M : IntVec d) (v : {n : IntVec d // n ∈ D} → Complex) :
      Continuous (synth M v) := by
    dsimp [synth]
    exact continuous_finsetSum Finset.univ fun n hn =>
      continuous_const.mul (continuous_star.comp (hchar_cont (data.nu n.1)))
  refine ⟨{
    omega := Omega
    omega_measurable := hOmega_measurable
    omega_subset := hOmega_subset
    volume_omega := hOmega_volume
    interpolate := F
    interpolate_stronglyMeasurable := ?_
    interpolate_integrable := ?_
    interpolate_memLp := ?_
    interpolate_supported := ?_
    interpolate_samples := ?_
    interpolate_cost := ?_ }⟩
  · intro M v
    have hsynth : StronglyMeasurable (synth M v) :=
      (hsynth_cont M v).stronglyMeasurable
    have hH : StronglyMeasurable (H M v) :=
      hsynth.indicator hOmega_measurable
    dsimp [F]
    exact hH.comp_measurable (by fun_prop)
  · intro M v
    let C : Real := ∑ n, ‖(sol M v).a n‖
    have hcubeFinite : volume (unitCube d) < ∞ := by
      have hcube : unitCube d = Set.univ.pi
          (fun _ : Fin d => Set.Ioo (0 : Real) 1) := by
        ext x
        simp [unitCube]
      rw [hcube, Real.volume_pi_Ioo]
      simp
    have hfinite : volume Omega < ∞ :=
      (measure_mono hOmega_subset).trans_lt hcubeFinite
    have hbound (x : RealVec d) : ‖synth M v x‖ ≤ C := by
      dsimp [synth, C]
      calc
        ‖∑ n, (sol M v).a n *
            starRingEnd Complex (fourierChar (data.nu n.1) x)‖ ≤
            ∑ n, ‖(sol M v).a n *
              starRingEnd Complex (fourierChar (data.nu n.1) x)‖ :=
          norm_sum_le _ _
        _ = ∑ n, ‖(sol M v).a n‖ := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [norm_mul, hstar_fourier]
          rw [Complex.norm_exp]
          norm_num
    have hsynth_on : IntegrableOn (synth M v) Omega := by
      refine MeasureTheory.IntegrableOn.of_bound hfinite
        (hsynth_cont M v).aestronglyMeasurable C ?_
      filter_upwards [] with x
      exact hbound x
    have hHint : Integrable (H M v) volume := by
      simpa [H] using hsynth_on.integrable_indicator hOmega_measurable
    simpa [F, Function.comp_def] using hHint.comp_sub_right (integerEmbed M)
  · intro M v
    let C : Real := ∑ n, ‖(sol M v).a n‖
    have hcubeFinite : volume (unitCube d) < ∞ := by
      have hcube : unitCube d = Set.univ.pi
          (fun _ : Fin d => Set.Ioo (0 : Real) 1) := by
        ext x
        simp [unitCube]
      rw [hcube, Real.volume_pi_Ioo]
      simp
    have hfinite : volume Omega < ∞ :=
      (measure_mono hOmega_subset).trans_lt hcubeFinite
    letI : IsFiniteMeasure (volume.restrict Omega) :=
      isFiniteMeasure_restrict.mpr hfinite.ne
    have hbound : ∀ᵐ x ∂volume.restrict Omega, ‖synth M v x‖ ≤ C := by
      filter_upwards [] with x
      dsimp [synth, C]
      calc
        ‖∑ n, (sol M v).a n *
            starRingEnd Complex (fourierChar (data.nu n.1) x)‖ ≤
            ∑ n, ‖(sol M v).a n *
              starRingEnd Complex (fourierChar (data.nu n.1) x)‖ :=
          norm_sum_le _ _
        _ = ∑ n, ‖(sol M v).a n‖ := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [norm_mul, hstar_fourier]
          rw [Complex.norm_exp]
          norm_num
    have hsynthLp : MemLp (synth M v) (2 : ENNReal) (volume.restrict Omega) :=
      MemLp.of_bound (hsynth_cont M v).aestronglyMeasurable C hbound
    have hHLp : MemLp (H M v) (2 : ENNReal) volume := by
      rw [memLp_indicator_iff_restrict hOmega_measurable]
      simpa [H] using hsynthLp
    have hFLp := hHLp.comp_measurePreserving
      (measurePreserving_add_right volume (-(integerEmbed M)))
    simpa [F, Function.comp_def, sub_eq_add_neg] using hFLp
  · intro M v
    filter_upwards [] with x
    intro hx
    dsimp [F, H]
    exact Set.indicator_of_notMem (by
      intro hs
      apply hx
      simpa [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, sub_eq_add_neg,
        add_comm] using hs) _
  · intro M v i
    have hfreq : data.nu i.1 = frequency delta i.1 :=
      data.nu_outside i.1 (hDoutside i.1 i.2)
    rw [← hfreq]
    let qfun : RealVec d → Complex := fun s =>
      H M v s * fourierChar (data.nu i.1) (s + integerEmbed M)
    have htranslate :
        (∫ x : RealVec d, F M v x * fourierChar (data.nu i.1) x) =
          ∫ x : RealVec d, qfun (x - integerEmbed M) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with x
      simp [F, qfun]
    have hindicator :
        (∫ s : RealVec d, qfun s) =
          ∫ s in Omega, synth M v s *
            fourierChar (data.nu i.1) (s + integerEmbed M) := by
      rw [← MeasureTheory.integral_indicator hOmega_measurable]
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with s
      by_cases hs : s ∈ Omega
      · simp [qfun, H, hs]
      · simp [qfun, H, hs]
    let eM : Complex := fourierChar (data.nu i.1) (integerEmbed M)
    have hpoint (s : RealVec d) :
        synth M v s * fourierChar (data.nu i.1) (s + integerEmbed M) =
          eM * ∑ j, fourierChar (data.nu i.1 - data.nu j.1) s *
            (sol M v).a j := by
      dsimp [synth]
      rw [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      dsimp [eM]
      rw [hchar_add]
      calc
        (sol M v).a j * starRingEnd Complex (fourierChar (data.nu j.1) s) *
            (fourierChar (data.nu i.1) s *
              fourierChar (data.nu i.1) (integerEmbed M)) =
            fourierChar (data.nu i.1) (integerEmbed M) *
              ((fourierChar (data.nu i.1) s *
                starRingEnd Complex (fourierChar (data.nu j.1) s)) *
                  (sol M v).a j) := by ring
        _ = fourierChar (data.nu i.1) (integerEmbed M) *
            (fourierChar (data.nu i.1 - data.nu j.1) s *
              (sol M v).a j) := by rw [hchar_sub]
    have hcubeFinite : volume (unitCube d) < ∞ := by
      have hcube : unitCube d = Set.univ.pi
          (fun _ : Fin d => Set.Ioo (0 : Real) 1) := by
        ext x
        simp [unitCube]
      rw [hcube, Real.volume_pi_Ioo]
      simp
    have hfinite : volume Omega < ∞ :=
      (measure_mono hOmega_subset).trans_lt hcubeFinite
    have hterm (j : {n : IntVec d // n ∈ D}) : IntegrableOn
        (fun s : RealVec d => fourierChar (data.nu i.1 - data.nu j.1) s *
          (sol M v).a j) Omega := by
      refine MeasureTheory.IntegrableOn.of_bound hfinite
        ((hchar_cont _).mul continuous_const).aestronglyMeasurable
        ‖(sol M v).a j‖ ?_
      filter_upwards [] with s
      rw [norm_mul]
      unfold fourierChar
      rw [Complex.norm_exp]
      norm_num
    have hcore :
        (∫ s in Omega, synth M v s *
          fourierChar (data.nu i.1) (s + integerEmbed M)) =
          eM * (G.mulVec (sol M v).a) i := by
      calc
        _ = ∫ s in Omega, eM * ∑ j,
              fourierChar (data.nu i.1 - data.nu j.1) s * (sol M v).a j := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards [] with s
            exact hpoint s
        _ = eM * ∫ s in Omega, ∑ j,
              fourierChar (data.nu i.1 - data.nu j.1) s * (sol M v).a j := by
            rw [MeasureTheory.integral_const_mul]
        _ = eM * ∑ j, ∫ s in Omega,
              fourierChar (data.nu i.1 - data.nu j.1) s * (sol M v).a j := by
            rw [MeasureTheory.integral_finsetSum Finset.univ (fun j _ => hterm j)]
        _ = eM * (G.mulVec (sol M v).a) i := by
            congr 1
            simp only [G, Internal.gramMatrix, Matrix.mulVec, dotProduct]
            apply Finset.sum_congr rfl
            intro j hj
            rw [MeasureTheory.integral_mul_const]
    unfold inverseSample inverseSampleOn
    simp only [Measure.restrict_univ]
    calc
      (∫ x : RealVec d, F M v x * fourierChar (data.nu i.1) x) =
          ∫ x : RealVec d, qfun (x - integerEmbed M) := htranslate
      _ = ∫ s : RealVec d, qfun s :=
        integral_sub_right_eq_self qfun (integerEmbed M)
      _ = ∫ s in Omega, synth M v s *
          fourierChar (data.nu i.1) (s + integerEmbed M) := hindicator
      _ = eM * (G.mulVec (sol M v).a) i := hcore
      _ = eM * w M v i := by rw [congrFun (sol M v).equation i]
      _ = v i := by
        dsimp [eM, w]
        rw [← mul_assoc, hchar_unit, one_mul]
  · intro M v
    have htranslateNorm : sqNormOn Set.univ (F M v) =
        sqNormOn Omega (synth M v) := by
      unfold sqNormOn
      calc
        (∫ x in Set.univ, ‖F M v x‖ ^ 2) =
            ∫ x : RealVec d, ‖F M v x‖ ^ 2 := by simp
        _ = ∫ s : RealVec d, ‖H M v s‖ ^ 2 := by
          simpa [F] using
            (integral_sub_right_eq_self
              (fun s : RealVec d => ‖H M v s‖ ^ 2) (integerEmbed M))
        _ = ∫ s in Omega, ‖synth M v s‖ ^ 2 := by
          rw [← MeasureTheory.integral_indicator hOmega_measurable]
          apply MeasureTheory.integral_congr_ae
          filter_upwards [] with s
          by_cases hs : s ∈ Omega
          · simp [H, hs]
          · simp [H, hs]
    have hgram : (Internal.gramQuadratic G (sol M v).a).re =
        sqNormOn Omega (synth M v) := by
      have h := (Internal.gramQuadratic_eq_sqNormOn data.nu D Omega
        (Or.inr ⟨hd, theta, N, hN, htheta0.le, htheta1, rfl⟩)
        (sol M v).a).2.2
      simpa [G, synth] using h
    have hw : (∑ n, ‖w M v n‖ ^ 2) = ∑ n, ‖v n‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro n hn
      dsimp [w]
      rw [norm_mul, hstar_fourier]
      rw [Complex.norm_exp]
      norm_num
    calc
      sqNormOn Set.univ (F M v) = sqNormOn Omega (synth M v) := htranslateNorm
      _ = (Internal.gramQuadratic G (sol M v).a).re := hgram.symm
      _ ≤ (1 / c) * ∑ n, ‖w M v n‖ ^ 2 := (sol M v).energy_le
      _ = (2 / (K.lower * theta)) * ∑ n, ‖v n‖ ^ 2 := by
        rw [hw]
        congr 1
        dsimp [c]
        field_simp [K.lower_pos.ne', htheta0.ne']

/-- Construct the thin carrier from the striped coercive Gram. -/
noncomputable def exists_thinCarrier_hd {d : Nat} (hd : 0 < d)
    {delta : IntVec d → RealVec d}
    (data : Internal.ModifiedFrequencyData delta)
    (K : ExponentialBoundsHD data.nu) (D : Finset (IntVec d))
    (hD : D.Nonempty) (hDoutside : ∀ n ∈ D, n ∉ data.C0)
    (theta : Real) (htheta0 : 0 < theta) (htheta1 : theta ≤ 1) :
    ThinCarrierHD data K D theta :=
  Classical.choice
    (thinCarrierHD_nonempty hd data K D hD hDoutside theta htheta0 htheta1)

/-- Projection from a supplied carrier. -/
theorem thin_interpolation_hd {d : Nat} {delta : IntVec d → RealVec d}
    {data : Internal.ModifiedFrequencyData delta}
    {K : ExponentialBoundsHD data.nu} {D : Finset (IntVec d)} {theta : Real}
    (T : ThinCarrierHD data K D theta) (M : IntVec d)
    (v : {n : IntVec d // n ∈ D} → Complex) :
    ∃ F : RealVec d → Complex,
      StronglyMeasurable F ∧ Integrable F volume ∧
      MemLp F (2 : ENNReal) volume ∧
      AESupportedIn F (integerEmbed M +ᵥ T.omega) ∧
      (∀ n, inverseSample F (frequency delta n.1) = v n) ∧
      sqNormOn Set.univ F ≤
        (2 / (K.lower * theta)) * ∑ n, ‖v n‖ ^ 2 := by
  exact ⟨T.interpolate M v, T.interpolate_stronglyMeasurable M v,
    T.interpolate_integrable M v, T.interpolate_memLp M v,
    T.interpolate_supported M v, T.interpolate_samples M v,
    T.interpolate_cost M v⟩

end AsymptoticallyIntegerHD
