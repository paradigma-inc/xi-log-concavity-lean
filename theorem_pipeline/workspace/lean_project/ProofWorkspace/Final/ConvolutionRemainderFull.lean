import ProofWorkspace.Final.TailBoundsFull
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Tactic.IntervalCases

/-!
# Two-Laplace integral jets and their exponentially decaying remainders

The analytic pointwise and integral bounds below are proved from the kernel
formula and an integrable exponential moment, not assumed as jet estimates.
The first two integral jets are identified as actual derivatives by a proved
dominated differentiation-under-the-integral argument, including the join at zero.
-/

noncomputable section
open MeasureTheory
namespace ReciprocalXi

/-- Absolute coefficient sum of a kernel jet. -/
def laplaceJetAmplitude (C a b : ℝ) (j : ℕ) : ℝ := C * (b * a ^ j + a * b ^ j)

/-- Unsigned-parity exponential formula for the positive half-line. -/
def rawLaplaceJet (C a b : ℝ) (j : ℕ) (t : ℝ) : ℝ :=
  C * (b * a ^ j * Real.exp (-a * t) - a * b ^ j * Real.exp (-b * t))

/-- Positive-half-line derivative formula extended to all real arguments. -/
def rightExponentialJet (C a b : ℝ) (j : ℕ) (t : ℝ) : ℝ :=
  (-1 : ℝ) ^ j * rawLaplaceJet C a b j t

/-- Piecewise kernel jets. For j=0,1,2 their derivative interpretation is proved
below, rather than incorporated as an assumption in the definition. -/
def twoLaplaceJet (C a b : ℝ) (j : ℕ) (t : ℝ) : ℝ :=
  if 0 ≤ t then rightExponentialJet C a b j t else rawLaplaceJet C a b j (-t)

theorem laplaceJetAmplitude_nonneg (C a b : ℝ) (j : ℕ)
    (hC : 0 ≤ C) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ laplaceJetAmplitude C a b j := by
  unfold laplaceJetAmplitude
  positivity

/-- Absolute-value domination of either exponential formula. -/
theorem rawLaplaceJet_abs_le (C a b t W : ℝ) (j : ℕ)
    (hC : 0 ≤ C) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (haW : Real.exp (-a * t) ≤ W) (hbW : Real.exp (-b * t) ≤ W) :
    |rawLaplaceJet C a b j t| ≤ laplaceJetAmplitude C a b j * W := by
  have haa : 0 ≤ b * a ^ j * Real.exp (-a * t) := by positivity
  have hbb : 0 ≤ a * b ^ j * Real.exp (-b * t) := by positivity
  unfold rawLaplaceJet laplaceJetAmplitude
  rw [abs_mul, abs_of_nonneg hC]
  calc
    C * |b * a ^ j * Real.exp (-a * t) - a * b ^ j * Real.exp (-b * t)| ≤
        C * (|b * a ^ j * Real.exp (-a * t)| + |a * b ^ j * Real.exp (-b * t)|) :=
      mul_le_mul_of_nonneg_left (abs_sub _ _) hC
    _ = C * (b * a ^ j * Real.exp (-a * t) + a * b ^ j * Real.exp (-b * t)) := by
      rw [abs_of_nonneg haa, abs_of_nonneg hbb]
    _ ≤ C * (b * a ^ j * W + a * b ^ j * W) := by gcongr
    _ = C * (b * a ^ j + a * b ^ j) * W := by ring

theorem abs_rightExponentialJet (C a b t : ℝ) (j : ℕ) :
    |rightExponentialJet C a b j t| = |rawLaplaceJet C a b j t| := by
  simp [rightExponentialJet, abs_mul, abs_pow]

/-- On y≤x the two formulas agree exactly: the remainder is supported on y>x. -/
theorem twoLaplaceJet_sub_right_eq_zero (C a b x y : ℝ) (j : ℕ) (hy : y ≤ x) :
    twoLaplaceJet C a b j (x - y) - rightExponentialJet C a b j (x - y) = 0 := by
  simp [twoLaplaceJet, sub_nonneg.mpr hy]

/-- The actual kernel jet is globally bounded by its coefficient sum. -/
theorem twoLaplaceJet_abs_le_amplitude (C a b t : ℝ) (j : ℕ)
    (hC : 0 ≤ C) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |twoLaplaceJet C a b j t| ≤ laplaceJetAmplitude C a b j := by
  unfold twoLaplaceJet
  split_ifs with ht
  · rw [abs_rightExponentialJet]
    have hh := rawLaplaceJet_abs_le C a b t 1 j hC ha hb
      (Real.exp_le_one_iff.mpr (by nlinarith))
      (Real.exp_le_one_iff.mpr (by nlinarith))
    simpa only [mul_one] using hh
  · have htn : 0 ≤ -t := by linarith
    have hh := rawLaplaceJet_abs_le C a b (-t) 1 j hC ha hb
      (Real.exp_le_one_iff.mpr (by nlinarith))
      (Real.exp_le_one_iff.mpr (by nlinarith))
    simpa only [mul_one] using hh

/-- Pointwise exponentially decaying difference, proved directly by splitting
at y=x. It is valid for every natural jet index, hence in particular 0,1,2. -/
theorem twoLaplaceJet_remainder_pointwise (C a b R x y : ℝ) (j : ℕ)
    (hC : 0 ≤ C) (ha : 0 ≤ a) (hb : 0 ≤ b) (haR : a ≤ R) (hbR : b ≤ R)
    (hx : 0 ≤ x) :
    |twoLaplaceJet C a b j (x - y) - rightExponentialJet C a b j (x - y)| ≤
      2 * laplaceJetAmplitude C a b j * Real.exp (-R * x) * Real.exp (R * |y|) := by
  have hamp := laplaceJetAmplitude_nonneg C a b j hC ha hb
  by_cases hy : y ≤ x
  · rw [twoLaplaceJet_sub_right_eq_zero C a b x y j hy, abs_zero]
    positivity
  · have hxy : x < y := lt_of_not_ge hy
    have hypos : 0 < y := lt_of_le_of_lt hx hxy
    have hR : 0 ≤ R := ha.trans haR
    have hW : 1 ≤ Real.exp (R * (y - x)) :=
      Real.one_le_exp_iff.mpr (mul_nonneg hR (sub_nonneg.mpr hxy.le))
    have hactual : |twoLaplaceJet C a b j (x - y)| ≤
        laplaceJetAmplitude C a b j * Real.exp (R * (y - x)) := by
      have hh := twoLaplaceJet_abs_le_amplitude C a b (x - y) j hC ha hb
      exact hh.trans (by nlinarith)
    have hext : |rightExponentialJet C a b j (x - y)| ≤
        laplaceJetAmplitude C a b j * Real.exp (R * (y - x)) := by
      rw [abs_rightExponentialJet]
      apply rawLaplaceJet_abs_le C a b (x - y) _ j hC ha hb
      · apply Real.exp_le_exp.mpr
        nlinarith [mul_nonneg (sub_nonneg.mpr haR) (sub_nonneg.mpr hxy.le)]
      · apply Real.exp_le_exp.mpr
        nlinarith [mul_nonneg (sub_nonneg.mpr hbR) (sub_nonneg.mpr hxy.le)]
    calc
      |twoLaplaceJet C a b j (x - y) - rightExponentialJet C a b j (x - y)| ≤
          |twoLaplaceJet C a b j (x - y)| + |rightExponentialJet C a b j (x - y)| :=
        abs_sub _ _
      _ ≤ laplaceJetAmplitude C a b j * Real.exp (R * (y - x)) +
          laplaceJetAmplitude C a b j * Real.exp (R * (y - x)) := add_le_add hactual hext
      _ = 2 * laplaceJetAmplitude C a b j * Real.exp (-R * x) * Real.exp (R * |y|) := by
        rw [abs_of_pos hypos]
        have he : Real.exp (R * (y - x)) = Real.exp (-R * x) * Real.exp (R * y) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [he]
        ring

/-- The zeroth piecewise jet is the actual two-Laplace kernel formula. -/
theorem twoLaplaceJet_zero (C a b t : ℝ) :
    twoLaplaceJet C a b 0 t =
      C * (b * Real.exp (-a * |t|) - a * Real.exp (-b * |t|)) := by
  by_cases ht : 0 ≤ t
  · simp [twoLaplaceJet, rightExponentialJet, rawLaplaceJet, ht, abs_of_nonneg ht]
  · simp [twoLaplaceJet, rawLaplaceJet, ht,
      abs_of_neg (lt_of_not_ge ht)]

theorem measurable_rawLaplaceJet (C a b : ℝ) (j : ℕ) :
    Measurable (rawLaplaceJet C a b j) := by unfold rawLaplaceJet; fun_prop

theorem measurable_rightExponentialJet (C a b : ℝ) (j : ℕ) :
    Measurable (rightExponentialJet C a b j) :=
  measurable_const.mul (measurable_rawLaplaceJet C a b j)

theorem measurable_twoLaplaceJet (C a b : ℝ) (j : ℕ) :
    Measurable (twoLaplaceJet C a b j) := by
  unfold twoLaplaceJet
  exact Measurable.ite measurableSet_Ici (measurable_rightExponentialJet C a b j)
    ((measurable_rawLaplaceJet C a b j).comp measurable_neg)

theorem rightExponentialJet_abs_le_moment (C a b R x y : ℝ) (j : ℕ)
    (hC : 0 ≤ C) (ha : 0 ≤ a) (hb : 0 ≤ b) (haR : a ≤ R) (hbR : b ≤ R)
    (hx : 0 ≤ x) :
    |rightExponentialJet C a b j (x - y)| ≤
      laplaceJetAmplitude C a b j * Real.exp (R * |y|) := by
  rw [abs_rightExponentialJet]
  apply rawLaplaceJet_abs_le C a b (x - y) _ j hC ha hb
  · apply Real.exp_le_exp.mpr
    have h1 := mul_le_mul_of_nonneg_left (le_abs_self y) ha
    have h2 := mul_le_mul_of_nonneg_right haR (abs_nonneg y)
    nlinarith [mul_nonneg ha hx]
  · apply Real.exp_le_exp.mpr
    have h1 := mul_le_mul_of_nonneg_left (le_abs_self y) hb
    have h2 := mul_le_mul_of_nonneg_right hbR (abs_nonneg y)
    nlinarith [mul_nonneg hb hx]

theorem twoLaplaceJet_abs_le_moment (C a b R x y : ℝ) (j : ℕ)
    (hC : 0 ≤ C) (ha : 0 ≤ a) (hb : 0 ≤ b) (hR : 0 ≤ R) :
    |twoLaplaceJet C a b j (x - y)| ≤
      laplaceJetAmplitude C a b j * Real.exp (R * |y|) := by
  have hh := twoLaplaceJet_abs_le_amplitude C a b (x - y) j hC ha hb
  have hamp := laplaceJetAmplitude_nonneg C a b j hC ha hb
  have hexp : 1 ≤ Real.exp (R * |y|) :=
    Real.one_le_exp_iff.mpr (mul_nonneg hR (abs_nonneg y))
  exact hh.trans (by nlinarith)

/-- Integrability of every actual kernel jet follows from the integrable
exponential moment; no integrability premise is added for the kernel itself. -/
theorem integrable_twoLaplaceJet (μ : Measure ℝ) (C a b R x : ℝ) (j : ℕ)
    (hC : 0 ≤ C) (ha : 0 ≤ a) (hb : 0 ≤ b) (hR : 0 ≤ R)
    (hMoment : Integrable (fun y : ℝ => Real.exp (R * |y|)) μ) :
    Integrable (fun y => twoLaplaceJet C a b j (x - y)) μ := by
  apply (hMoment.const_mul (laplaceJetAmplitude C a b j)).mono'
    (((measurable_twoLaplaceJet C a b j).comp
      (measurable_const.sub measurable_id)).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun y => by
    simpa only [Real.norm_eq_abs] using twoLaplaceJet_abs_le_moment C a b R x y j hC ha hb hR

/-- Integrability of the extended exponential jet follows from the same moment. -/
theorem integrable_rightExponentialJet (μ : Measure ℝ) (C a b R x : ℝ) (j : ℕ)
    (hC : 0 ≤ C) (ha : 0 ≤ a) (hb : 0 ≤ b) (haR : a ≤ R) (hbR : b ≤ R)
    (hx : 0 ≤ x)
    (hMoment : Integrable (fun y : ℝ => Real.exp (R * |y|)) μ) :
    Integrable (fun y => rightExponentialJet C a b j (x - y)) μ := by
  apply (hMoment.const_mul (laplaceJetAmplitude C a b j)).mono'
    (((measurable_rightExponentialJet C a b j).comp
      (measurable_const.sub measurable_id)).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun y => by
    simpa only [Real.norm_eq_abs] using
      rightExponentialJet_abs_le_moment C a b R x y j hC ha hb haR hbR hx

/-- The actual kernel-jet integral. Its derivative interpretation is proved
later by dominated differentiation, not incorporated into this definition. -/
def laplaceConvolutionJet (μ : Measure ℝ) (C a b : ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  ∫ y, twoLaplaceJet C a b j (x - y) ∂μ

/-- The two leading exponential terms, expressed as their full integral. -/
def laplaceLeadingJet (μ : Measure ℝ) (C a b : ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  ∫ y, rightExponentialJet C a b j (x - y) ∂μ

/-- Equation (7) at the integral-jet level. The pointwise comparison and both
integrability conditions are derived, not assumed. This holds for any positive
measure with an integrable exponential moment, without evenness or probability
normalization assumptions. -/
theorem laplaceConvolutionJet_remainder_bound
    (μ : Measure ℝ) (C a b R M x : ℝ) (j : ℕ)
    (hC : 0 ≤ C) (ha : 0 ≤ a) (hb : 0 ≤ b) (haR : a ≤ R) (hbR : b ≤ R)
    (hx : 0 ≤ x)
    (hMoment : Integrable (fun y : ℝ => Real.exp (R * |y|)) μ)
    (hM : (∫ y : ℝ, Real.exp (R * |y|) ∂μ) ≤ M) :
    |laplaceConvolutionJet μ C a b j x - laplaceLeadingJet μ C a b j x| ≤
      (2 * C * M * (b * a ^ j + a * b ^ j)) * Real.exp (-R * x) := by
  have hK := integrable_twoLaplaceJet μ C a b R x j hC ha hb (ha.trans haR) hMoment
  have hE := integrable_rightExponentialJet μ C a b R x j hC ha hb haR hbR hx hMoment
  unfold laplaceConvolutionJet laplaceLeadingJet
  rw [← integral_sub hK hE]
  have hbnd := norm_integral_le_of_norm_le
    (f := fun y : ℝ => twoLaplaceJet C a b j (x - y) - rightExponentialJet C a b j (x - y))
    (hMoment.const_mul (2 * laplaceJetAmplitude C a b j * Real.exp (-R * x)))
    (Filter.Eventually.of_forall fun y => by
      simpa only [Real.norm_eq_abs] using
        twoLaplaceJet_remainder_pointwise C a b R x y j hC ha hb haR hbR hx)
  rw [integral_const_mul] at hbnd
  rw [Real.norm_eq_abs] at hbnd
  have hconst : 0 ≤ 2 * laplaceJetAmplitude C a b j * Real.exp (-R * x) := by
    have hamp := laplaceJetAmplitude_nonneg C a b j hC ha hb
    positivity
  calc
    _ ≤ (2 * laplaceJetAmplitude C a b j * Real.exp (-R * x)) *
        (∫ y : ℝ, Real.exp (R * |y|) ∂μ) := hbnd
    _ ≤ (2 * laplaceJetAmplitude C a b j * Real.exp (-R * x)) * M :=
      mul_le_mul_of_nonneg_left hM hconst
    _ = (2 * C * M * (b * a ^ j + a * b ^ j)) * Real.exp (-R * x) := by
      unfold laplaceJetAmplitude
      ring

/-- One-sided exponential moments used in the leading coefficients. -/
def exponentialMoment (μ : Measure ℝ) (r : ℝ) : ℝ := ∫ y : ℝ, Real.exp (r * y) ∂μ

/-- Every smaller nonnegative one-sided exponential is integrable under the
given absolute exponential-moment hypothesis. -/
theorem integrable_smaller_exponential (μ : Measure ℝ) (a R : ℝ)
    (ha : 0 ≤ a) (haR : a ≤ R)
    (hMoment : Integrable (fun y : ℝ => Real.exp (R * |y|)) μ) :
    Integrable (fun y : ℝ => Real.exp (a * y)) μ := by
  apply hMoment.mono' (by fun_prop)
  apply Filter.Eventually.of_forall
  intro y
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  exact (mul_le_mul_of_nonneg_left (le_abs_self y) ha).trans
    (mul_le_mul_of_nonneg_right haR (abs_nonneg y))

theorem exp_neg_mul_sub (a x y : ℝ) :
    Real.exp (-a * (x - y)) = Real.exp (-a * x) * Real.exp (a * y) := by
  rw [← Real.exp_add]
  congr 1
  ring

/-- The leading integral is exactly the two exponential terms with the measure's
one-sided exponential moments as coefficients. -/
theorem laplaceLeadingJet_eq_moments
    (μ : Measure ℝ) (C a b R x : ℝ) (j : ℕ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (haR : a ≤ R) (hbR : b ≤ R)
    (hMoment : Integrable (fun y : ℝ => Real.exp (R * |y|)) μ) :
    laplaceLeadingJet μ C a b j x = (-1 : ℝ) ^ j * C *
      (b * a ^ j * Real.exp (-a * x) * exponentialMoment μ a -
        a * b ^ j * Real.exp (-b * x) * exponentialMoment μ b) := by
  have haInt := integrable_smaller_exponential μ a R ha haR hMoment
  have hbInt := integrable_smaller_exponential μ b R hb hbR hMoment
  have hfun : (fun y : ℝ => rightExponentialJet C a b j (x - y)) =
      fun y => ((-1 : ℝ) ^ j * C * b * a ^ j * Real.exp (-a * x)) * Real.exp (a * y) -
        ((-1 : ℝ) ^ j * C * a * b ^ j * Real.exp (-b * x)) * Real.exp (b * y) := by
    funext y
    unfold rightExponentialJet rawLaplaceJet
    rw [exp_neg_mul_sub, exp_neg_mul_sub]
    ring
  unfold laplaceLeadingJet
  rw [hfun]
  rw [integral_sub (haInt.const_mul _) (hbInt.const_mul _),
    integral_const_mul, integral_const_mul]
  unfold exponentialMoment
  ring

/-- Remainder estimate against the explicit moment-weighted leading formula.
This is the source's equation (7), for the actual integral jets and all j. -/
theorem laplaceConvolutionJet_remainder_to_moments
    (μ : Measure ℝ) (C a b R M x : ℝ) (j : ℕ)
    (hC : 0 ≤ C) (ha : 0 ≤ a) (hb : 0 ≤ b) (haR : a ≤ R) (hbR : b ≤ R)
    (hx : 0 ≤ x)
    (hMoment : Integrable (fun y : ℝ => Real.exp (R * |y|)) μ)
    (hM : (∫ y : ℝ, Real.exp (R * |y|) ∂μ) ≤ M) :
    |laplaceConvolutionJet μ C a b j x - (-1 : ℝ) ^ j * C *
      (b * a ^ j * Real.exp (-a * x) * exponentialMoment μ a -
        a * b ^ j * Real.exp (-b * x) * exponentialMoment μ b)| ≤
      (2 * C * M * (b * a ^ j + a * b ^ j)) * Real.exp (-R * x) := by
  rw [← laplaceLeadingJet_eq_moments μ C a b R x j ha hb haR hbR hMoment]
  exact laplaceConvolutionJet_remainder_bound μ C a b R M x j hC ha hb haR hbR hx hMoment hM

/-- Ordinary derivatives of the smooth exponential expressions. -/
theorem hasDerivAt_rawLaplaceJet (C a b t : ℝ) (j : ℕ) :
    HasDerivAt (rawLaplaceJet C a b j) (-rawLaplaceJet C a b (j + 1) t) t := by
  convert ((((hasDerivAt_id t).const_mul (-a)).exp.const_mul (b * a ^ j)).sub
    (((hasDerivAt_id t).const_mul (-b)).exp.const_mul (a * b ^ j))).const_mul C using 1
  simp only [rawLaplaceJet, pow_succ, id_eq]
  ring

theorem hasDerivAt_rightExponentialJet (C a b t : ℝ) (j : ℕ) :
    HasDerivAt (rightExponentialJet C a b j) (rightExponentialJet C a b (j + 1) t) t := by
  convert (hasDerivAt_rawLaplaceJet C a b t j).const_mul ((-1 : ℝ) ^ j) using 1
  simp only [rightExponentialJet, pow_succ]
  ring

theorem hasDerivAt_leftExponentialJet (C a b t : ℝ) (j : ℕ) :
    HasDerivAt (fun z => rawLaplaceJet C a b j (-z)) (rawLaplaceJet C a b (j + 1) (-t)) t := by
  convert (hasDerivAt_rawLaplaceJet C a b (-t) j).comp t (hasDerivAt_id t).neg using 1
  simp

/-- The two branches agree in value through order two at the joining point. -/
theorem rawLaplaceJet_zero_eq_right (C a b : ℝ) (j : ℕ) (hj : j ≤ 2) :
    rawLaplaceJet C a b j 0 = rightExponentialJet C a b j 0 := by
  interval_cases j
  · simp [rawLaplaceJet, rightExponentialJet]
  · simp [rawLaplaceJet, rightExponentialJet]
    ring
  · simp [rawLaplaceJet, rightExponentialJet]

/-- Differentiable gluing of two real functions at zero when their values and
derivatives match. The proof handles the boundary point explicitly. -/
theorem hasDerivAt_piecewise_zero
    (f g f1 g1 : ℝ → ℝ)
    (hf : ∀ t, HasDerivAt f (f1 t) t) (hg : ∀ t, HasDerivAt g (g1 t) t)
    (hzero : f 0 = g 0) (hderivzero : f1 0 = g1 0) (t : ℝ) :
    HasDerivAt (fun z => if 0 ≤ z then f z else g z)
      (if 0 ≤ t then f1 t else g1 t) t := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · rw [if_neg (not_le_of_gt ht)]
    apply (hg t).congr_of_eventuallyEq
    exact Filter.mem_of_superset (Iio_mem_nhds ht) fun z hz => if_neg (not_le_of_gt hz)
  · rw [if_pos le_rfl]
    have hr : HasDerivWithinAt (fun z => if 0 ≤ z then f z else g z) (f1 0) (Set.Ici 0) 0 := by
      apply (hf 0).hasDerivWithinAt.congr
      · intro z hz
        exact if_pos hz
      · simp
    have hl : HasDerivWithinAt (fun z => if 0 ≤ z then f z else g z) (g1 0) (Set.Iic 0) 0 := by
      apply (hg 0).hasDerivWithinAt.congr
      · intro z hz
        by_cases h : 0 ≤ z
        · have hz0 : z = 0 := le_antisymm hz h
          simp [hz0, hzero]
        · exact if_neg h
      · simp [hzero]
    rw [← hderivzero] at hl
    have hh := hr.union hl
    have hset : Set.Ici (0 : ℝ) ∪ Set.Iic 0 = Set.univ := by
      ext z
      simp only [Set.mem_union, Set.mem_Ici, Set.mem_Iic, Set.mem_univ, iff_true]
      exact le_total 0 z
    simpa only [hset, hasDerivWithinAt_univ] using hh
  · rw [if_pos ht.le]
    apply (hf t).congr_of_eventuallyEq
    exact Filter.mem_of_superset (Ioi_mem_nhds ht) fun z hz => if_pos hz.le

/-- The piecewise kernel is twice differentiable, including its joining point.
For j=0 and j=1 its derivative is exactly the next integral-jet integrand. -/
theorem hasDerivAt_twoLaplaceJet (C a b t : ℝ) (j : ℕ) (hj : j ≤ 1) :
    HasDerivAt (twoLaplaceJet C a b j) (twoLaplaceJet C a b (j + 1) t) t := by
  unfold twoLaplaceJet
  apply hasDerivAt_piecewise_zero (rightExponentialJet C a b j)
    (fun z => rawLaplaceJet C a b j (-z)) (rightExponentialJet C a b (j + 1))
    (fun z => rawLaplaceJet C a b (j + 1) (-z))
    (fun z => hasDerivAt_rightExponentialJet C a b z j)
    (fun z => hasDerivAt_leftExponentialJet C a b z j)
  · simpa only [neg_zero] using (rawLaplaceJet_zero_eq_right C a b j (by omega)).symm
  · simpa only [neg_zero] using (rawLaplaceJet_zero_eq_right C a b (j + 1) (by omega)).symm

/-- Differentiation under the actual kernel integral. The kernel's derivative
is globally dominated by an integrable exponential-moment multiple, so this
includes atomic measures and points at the kernel's joining location. -/
theorem hasDerivAt_laplaceConvolutionJet
    (μ : Measure ℝ) (C a b R x : ℝ) (j : ℕ) (hj : j ≤ 1)
    (hC : 0 ≤ C) (ha : 0 ≤ a) (hb : 0 ≤ b) (hR : 0 ≤ R)
    (hMoment : Integrable (fun y : ℝ => Real.exp (R * |y|)) μ) :
    HasDerivAt (laplaceConvolutionJet μ C a b j)
      (laplaceConvolutionJet μ C a b (j + 1) x) x := by
  have hmeas : ∀ z : ℝ, AEStronglyMeasurable
      (fun y : ℝ => twoLaplaceJet C a b j (z - y)) μ := by
    intro z
    exact ((measurable_twoLaplaceJet C a b j).comp
      (measurable_const.sub measurable_id)).aestronglyMeasurable
  have hmeas' : AEStronglyMeasurable
      (fun y : ℝ => twoLaplaceJet C a b (j + 1) (x - y)) μ :=
    ((measurable_twoLaplaceJet C a b (j + 1)).comp
      (measurable_const.sub measurable_id)).aestronglyMeasurable
  have hh := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z y : ℝ => twoLaplaceJet C a b j (z - y))
    (F' := fun z y : ℝ => twoLaplaceJet C a b (j + 1) (z - y))
    (bound := fun y : ℝ => laplaceJetAmplitude C a b (j + 1) * Real.exp (R * |y|))
    (s := Set.univ) (x₀ := x) (μ := μ) (Filter.univ_mem)
    (Filter.Eventually.of_forall hmeas)
    (integrable_twoLaplaceJet μ C a b R x j hC ha hb hR hMoment) hmeas'
    (Filter.Eventually.of_forall fun y => by
      intro z _
      simpa only [Real.norm_eq_abs] using
        twoLaplaceJet_abs_le_moment C a b R z y (j + 1) hC ha hb hR)
    (hMoment.const_mul (laplaceJetAmplitude C a b (j + 1)))
    (Filter.Eventually.of_forall fun y => by
      intro z _
      simpa only [mul_one] using
        (hasDerivAt_twoLaplaceJet C a b (z - y) j hj).comp z
          ((hasDerivAt_id z).sub_const y))
  exact hh.2

theorem laplaceConvolution_deriv_eq (μ : Measure ℝ) (C a b R : ℝ)
    (hC : 0 ≤ C) (ha : 0 ≤ a) (hb : 0 ≤ b) (hR : 0 ≤ R)
    (hMoment : Integrable (fun y : ℝ => Real.exp (R * |y|)) μ) :
    deriv (laplaceConvolutionJet μ C a b 0) = laplaceConvolutionJet μ C a b 1 := by
  funext x
  exact (hasDerivAt_laplaceConvolutionJet μ C a b R x 0 (by omega) hC ha hb hR hMoment).deriv

theorem laplaceConvolution_second_deriv_eq (μ : Measure ℝ) (C a b R : ℝ)
    (hC : 0 ≤ C) (ha : 0 ≤ a) (hb : 0 ≤ b) (hR : 0 ≤ R)
    (hMoment : Integrable (fun y : ℝ => Real.exp (R * |y|)) μ) :
    deriv (deriv (laplaceConvolutionJet μ C a b 0)) = laplaceConvolutionJet μ C a b 2 := by
  rw [laplaceConvolution_deriv_eq μ C a b R hC ha hb hR hMoment]
  funext x
  exact (hasDerivAt_laplaceConvolutionJet μ C a b R x 1 (by omega) hC ha hb hR hMoment).deriv

theorem laplaceConvolution_iterated_deriv_eq (μ : Measure ℝ) (C a b R : ℝ)
    (j : ℕ) (hj : j ≤ 2)
    (hC : 0 ≤ C) (ha : 0 ≤ a) (hb : 0 ≤ b) (hR : 0 ≤ R)
    (hMoment : Integrable (fun y : ℝ => Real.exp (R * |y|)) μ) :
    (deriv^[j] (laplaceConvolutionJet μ C a b 0)) = laplaceConvolutionJet μ C a b j := by
  interval_cases j
  · rfl
  · exact laplaceConvolution_deriv_eq μ C a b R hC ha hb hR hMoment
  · exact laplaceConvolution_second_deriv_eq μ C a b R hC ha hb hR hMoment

/-- Actual derivative version of equation (7), including the proved
differentiation-under-integral step. No derivative remainder is a premise. -/
theorem laplaceConvolution_actual_derivative_remainder
    (μ : Measure ℝ) (C a b R M x : ℝ) (j : ℕ) (hj : j ≤ 2)
    (hC : 0 ≤ C) (ha : 0 ≤ a) (hb : 0 ≤ b) (haR : a ≤ R) (hbR : b ≤ R)
    (hx : 0 ≤ x)
    (hMoment : Integrable (fun y : ℝ => Real.exp (R * |y|)) μ)
    (hM : (∫ y : ℝ, Real.exp (R * |y|) ∂μ) ≤ M) :
    |(deriv^[j] (laplaceConvolutionJet μ C a b 0)) x - (-1 : ℝ) ^ j * C *
      (b * a ^ j * Real.exp (-a * x) * exponentialMoment μ a -
        a * b ^ j * Real.exp (-b * x) * exponentialMoment μ b)| ≤
      (2 * C * M * (b * a ^ j + a * b ^ j)) * Real.exp (-R * x) := by
  rw [laplaceConvolution_iterated_deriv_eq μ C a b R j hj hC ha hb (ha.trans haR) hMoment]
  exact laplaceConvolutionJet_remainder_to_moments μ C a b R M x j
    hC ha hb haR hbR hx hMoment hM

theorem differentiable_laplaceConvolution (μ : Measure ℝ) (C a b R : ℝ)
    (hC : 0 ≤ C) (ha : 0 ≤ a) (hb : 0 ≤ b) (hR : 0 ≤ R)
    (hMoment : Integrable (fun y : ℝ => Real.exp (R * |y|)) μ) :
    Differentiable ℝ (laplaceConvolutionJet μ C a b 0) := by
  intro x
  exact (hasDerivAt_laplaceConvolutionJet μ C a b R x 0 (by omega)
    hC ha hb hR hMoment).differentiableAt

theorem differentiable_deriv_laplaceConvolution (μ : Measure ℝ) (C a b R : ℝ)
    (hC : 0 ≤ C) (ha : 0 ≤ a) (hb : 0 ≤ b) (hR : 0 ≤ R)
    (hMoment : Integrable (fun y : ℝ => Real.exp (R * |y|)) μ) :
    Differentiable ℝ (deriv (laplaceConvolutionJet μ C a b 0)) := by
  rw [laplaceConvolution_deriv_eq μ C a b R hC ha hb hR hMoment]
  intro x
  exact (hasDerivAt_laplaceConvolutionJet μ C a b R x 1 (by omega)
    hC ha hb hR hMoment).differentiableAt

/-- Strict positivity of the actual zeroth kernel formula. -/
theorem twoLaplaceKernel_pos (C a b t : ℝ)
    (hC : 0 < C) (ha : 0 < a) (hab : a < b) :
    0 < twoLaplaceJet C a b 0 t := by
  rw [twoLaplaceJet_zero]
  apply mul_pos hC
  have he : Real.exp (-b * |t|) ≤ Real.exp (-a * |t|) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hab.le) (abs_nonneg t)]
  have h1 := mul_le_mul_of_nonneg_left he ha.le
  have h2 := mul_pos (sub_pos.mpr hab) (Real.exp_pos (-a * |t|))
  nlinarith

/-- A probability mixture of this positive kernel is strictly positive.
The integrability needed to justify the positive integral has already been
derived from the exponential moment. -/
theorem laplaceConvolution_pos (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (C a b R x : ℝ) (hC : 0 < C) (ha : 0 < a) (hab : a < b) (hR : 0 ≤ R)
    (hMoment : Integrable (fun y : ℝ => Real.exp (R * |y|)) μ) :
    0 < laplaceConvolutionJet μ C a b 0 x := by
  have hInt := integrable_twoLaplaceJet μ C a b R x 0 hC.le ha.le (ha.trans hab).le hR hMoment
  have hpos : ∀ y : ℝ, 0 < twoLaplaceJet C a b 0 (x - y) :=
    fun y => twoLaplaceKernel_pos C a b (x - y) hC ha hab
  have hsupp : Function.support (fun y : ℝ => twoLaplaceJet C a b 0 (x - y)) = Set.univ := by
    ext y
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact ne_of_gt (hpos y)
  unfold laplaceConvolutionJet
  apply (integral_pos_iff_support_of_nonneg (fun y => (hpos y).le) hInt).mpr
  rw [hsupp, measure_univ]
  norm_num

/-- The leading moments of an even probability measure are at least one.
This supplies the coefficient lower bounds used in the tail comparison. -/
theorem exponentialMoment_one_le_of_even (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a R : ℝ) (ha : 0 ≤ a) (haR : a ≤ R)
    (hEven : MeasurePreserving (fun y : ℝ => -y) μ μ)
    (hMoment : Integrable (fun y : ℝ => Real.exp (R * |y|)) μ) :
    1 ≤ exponentialMoment μ a := by
  have hp := integrable_smaller_exponential μ a R ha haR hMoment
  have hn : Integrable (fun y : ℝ => Real.exp (a * (-y))) μ :=
    hEven.integrable_comp_of_integrable hp
  have heq : (∫ y : ℝ, Real.exp (a * (-y)) ∂μ) = exponentialMoment μ a := by
    exact hEven.integral_comp (MeasurableEquiv.neg ℝ).measurableEmbedding
      (fun y : ℝ => Real.exp (a * y))
  have hsum := integral_mono (integrable_const (2 : ℝ)) (hp.add hn)
    (fun y : ℝ => show (2 : ℝ) ≤ Real.exp (a * y) + Real.exp (a * (-y)) from by
      have h₁ := Real.add_one_le_exp (a * y)
      have h₂ := Real.add_one_le_exp (a * (-y))
      nlinarith)
  change (∫ y : ℝ, (2 : ℝ) ∂μ) ≤
    ∫ y : ℝ, Real.exp (a * y) + Real.exp (a * (-y)) ∂μ at hsum
  rw [integral_add hp hn, heq] at hsum
  simp only [integral_const, probReal_univ, one_smul] at hsum
  change 2 ≤ exponentialMoment μ a + exponentialMoment μ a at hsum
  linarith

end ReciprocalXi

end
