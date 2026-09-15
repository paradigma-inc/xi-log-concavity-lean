import ProofWorkspace.Final.ReciprocalStripFull
import ProofWorkspace.Final.XiFourierRealFull
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Actual reciprocal-Xi contour shifting

Absolute convergence on horizontal lines and vanishing vertical sides justify
the rectangular contour limit. The sign-adapted height then gives actual
exponential decay of the inverse Fourier integral.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace ReciprocalXi

/-- The inverse Fourier integrand at a complex frequency and complex contour point. -/
def stripFourierKernel (z w : ℂ) : ℂ :=
  reciprocalExtension w * Complex.exp (-Complex.I * z * w)

theorem differentiableAt_reciprocalExtension_closed (w : ℂ) (hw : |w.im| ≤ 1) :
    DifferentiableAt ℂ reciprocalExtension w := by
  have hd : Differentiable ℂ (fun v : ℂ => F (Complex.I * v)) :=
    differentiable_F_complex.comp ((differentiable_const Complex.I).mul differentiable_id)
  exact ((differentiable_const (F 0)).differentiableAt).div
    (hd w) (F_imaginary_axis_complex_ne_zero w hw)

theorem differentiableAt_stripFourierKernel (z w : ℂ) (hw : |w.im| ≤ 1) :
    DifferentiableAt ℂ (stripFourierKernel z) w := by
  exact (differentiableAt_reciprocalExtension_closed w hw).mul (by fun_prop)

theorem norm_stripFourier_exponential (z : ℂ) (u v : ℝ) :
    ‖Complex.exp (-Complex.I * z * ((u : ℂ) + (v : ℂ) * Complex.I))‖ =
      Real.exp (z.im * u + z.re * v) := by
  rw [Complex.norm_exp]
  congr 1
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.I_re, Complex.I_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem stripFourierKernel_norm_le (z : ℂ) (u v : ℝ) (hv : |v| ≤ 1) :
    ‖stripFourierKernel z ((u : ℂ) + (v : ℂ) * Complex.I)‖ ≤
      (5 * Real.exp |z.re|) * (Real.exp (|z.im| * |u|) * ‖reciprocalTransform u‖) := by
  have hi : |(((u : ℂ) + (v : ℂ) * Complex.I)).im| ≤ 1 := by simpa using hv
  have hr : (((u : ℂ) + (v : ℂ) * Complex.I)).re = u := by simp
  have hp := reciprocalExtension_norm_le_five ((u : ℂ) + (v : ℂ) * Complex.I) hi
  rw [hr] at hp
  have he : z.im * u + z.re * v ≤ |z.im| * |u| + |z.re| := by
    have h1 := le_abs_self (z.im * u)
    have h2 := le_abs_self (z.re * v)
    have h3 := mul_le_mul_of_nonneg_left hv (abs_nonneg z.re)
    rw [abs_mul] at h1 h2
    linarith
  rw [stripFourierKernel, norm_mul, norm_stripFourier_exponential]
  calc
    _ ≤ (5 * ‖reciprocalTransform u‖) * Real.exp (|z.im| * |u| + |z.re|) :=
      mul_le_mul hp (Real.exp_le_exp.mpr he) (le_of_lt (Real.exp_pos _))
        (by positivity)
    _ = _ := by rw [Real.exp_add]; ring

theorem continuous_stripFourier_line (z : ℂ) (v : ℝ) (hv : |v| ≤ 1) :
    Continuous (fun u : ℝ => stripFourierKernel z ((u : ℂ) + (v : ℂ) * Complex.I)) := by
  apply continuous_iff_continuousAt.mpr
  intro u
  have hc : ContinuousAt (fun t : ℝ => (t : ℂ) + (v : ℂ) * Complex.I) u := by fun_prop
  exact ContinuousAt.comp (f := fun t : ℝ => (t : ℂ) + (v : ℂ) * Complex.I)
    (g := stripFourierKernel z)
    (differentiableAt_stripFourierKernel z ((u : ℂ) + (v : ℂ) * Complex.I)
      (by simpa using hv)).continuousAt hc

theorem integrable_exp_norm_reciprocalTransform (q : ℝ) :
    Integrable (fun u : ℝ => Real.exp (q * |u|) * ‖reciprocalTransform u‖) := by
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
    (integrable_weighted_reciprocalTransform q).norm

theorem integrable_stripFourier_line (z : ℂ) (v : ℝ) (hv : |v| ≤ 1) :
    Integrable (fun u : ℝ => stripFourierKernel z ((u : ℂ) + (v : ℂ) * Complex.I)) := by
  apply ((integrable_exp_norm_reciprocalTransform |z.im|).const_mul
    (5 * Real.exp |z.re|)).mono'
  · exact (continuous_stripFourier_line z v hv).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun u => stripFourierKernel_norm_le z u v hv)

theorem integral_stripFourier_line_norm_le (z : ℂ) (v : ℝ) (hv : |v| ≤ 1) :
    ‖∫ u : ℝ, stripFourierKernel z ((u : ℂ) + (v : ℂ) * Complex.I)‖ ≤
      (5 * Real.exp |z.re|) * ∫ u : ℝ, Real.exp (|z.im| * |u|) * ‖reciprocalTransform u‖ := by
  calc
    _ ≤ ∫ u : ℝ, ‖stripFourierKernel z ((u : ℂ) + (v : ℂ) * Complex.I)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ u : ℝ, (5 * Real.exp |z.re|) *
        (Real.exp (|z.im| * |u|) * ‖reciprocalTransform u‖) := by
      exact integral_mono (integrable_stripFourier_line z v hv).norm
        ((integrable_exp_norm_reciprocalTransform |z.im|).const_mul _)
        (fun u => stripFourierKernel_norm_le z u v hv)
    _ = _ := integral_const_mul _ _

theorem integral_stripFourier_rectangle (z : ℂ) (a b v w : ℝ)
    (hv : |v| ≤ 1) (hw : |w| ≤ 1) :
    (∫ u : ℝ in a..b, stripFourierKernel z ((u : ℂ) + (v : ℂ) * Complex.I)) -
      (∫ u : ℝ in a..b, stripFourierKernel z ((u : ℂ) + (w : ℂ) * Complex.I)) +
      Complex.I * (∫ t : ℝ in v..w,
        stripFourierKernel z ((b : ℂ) + (t : ℂ) * Complex.I)) -
      Complex.I * (∫ t : ℝ in v..w,
        stripFourierKernel z ((a : ℂ) + (t : ℂ) * Complex.I)) = 0 := by
  have hd : DifferentiableOn ℂ (stripFourierKernel z)
      (Set.uIcc a b ×ℂ Set.uIcc v w) := by
    intro q hq
    have hi : q.im ∈ Set.Icc (-1) 1 :=
      Set.uIcc_subset_Icc (abs_le.mp hv) (abs_le.mp hw) hq.2
    exact (differentiableAt_stripFourierKernel z q (abs_le.mpr hi)).differentiableWithinAt
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn (stripFourierKernel z)
    ((a : ℂ) + (v : ℂ) * Complex.I) ((b : ℂ) + (w : ℂ) * Complex.I)
    (by simpa using hd)
  simpa using h

theorem stripFourierKernel_norm_le_exp_tail (z : ℂ) (u v r : ℝ)
    (hu : 3 ≤ |u|) (hv : |v| ≤ 1) :
    ‖stripFourierKernel z ((u : ℂ) + (v : ℂ) * Complex.I)‖ ≤
      (5 * Real.exp |z.re| * reciprocalTailConstant (r + |z.im|)) *
        Real.exp (-(r * |u|)) := by
  have hp := reciprocalTransform_norm_le_exp_of_abs_three_le u (r + |z.im|) hu
  calc
    _ ≤ (5 * Real.exp |z.re|) *
        (Real.exp (|z.im| * |u|) * ‖reciprocalTransform u‖) :=
      stripFourierKernel_norm_le z u v hv
    _ ≤ (5 * Real.exp |z.re|) * (Real.exp (|z.im| * |u|) *
        (reciprocalTailConstant (r + |z.im|) * Real.exp (-((r + |z.im|) * |u|)))) := by
      gcongr
    _ = _ := by
      have he : |z.im| * |u| + -((r + |z.im|) * |u|) = -(r * |u|) := by ring
      calc
        _ = (5 * Real.exp |z.re| * reciprocalTailConstant (r + |z.im|)) *
            (Real.exp (|z.im| * |u|) * Real.exp (-((r + |z.im|) * |u|))) := by ring
        _ = _ := by rw [← Real.exp_add, he]

theorem integral_stripFourier_vertical_norm_le (z : ℂ) (u v w r : ℝ)
    (hu : 3 ≤ |u|) (hv : |v| ≤ 1) (hw : |w| ≤ 1) :
    ‖∫ t : ℝ in v..w, stripFourierKernel z ((u : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      ((5 * Real.exp |z.re| * reciprocalTailConstant (r + |z.im|)) *
        Real.exp (-(r * |u|))) * |w - v| := by
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro t ht
  have hi : t ∈ Set.Icc (-1) 1 :=
    Set.uIcc_subset_Icc (abs_le.mp hv) (abs_le.mp hw) (Set.uIoc_subset_uIcc ht)
  exact stripFourierKernel_norm_le_exp_tail z u t r hu (abs_le.mpr hi)

theorem tendsto_integral_stripFourier_vertical_right (z : ℂ) (v w : ℝ)
    (hv : |v| ≤ 1) (hw : |w| ≤ 1) :
    Tendsto (fun R : ℝ => ∫ t : ℝ in v..w,
      stripFourierKernel z ((R : ℂ) + (t : ℂ) * Complex.I)) atTop (𝓝 0) := by
  refine squeeze_zero_norm' (a := fun R : ℝ =>
    (5 * Real.exp |z.re| * reciprocalTailConstant (1 + |z.im|)) *
      Real.exp (-R) * |w - v|) ?_ ?_
  · filter_upwards [eventually_ge_atTop (3 : ℝ)] with R hR
    have h := integral_stripFourier_vertical_norm_le z R v w 1
      (by rwa [abs_of_nonneg (by linarith : 0 ≤ R)]) hv hw
    simpa only [one_mul, abs_of_nonneg (by linarith : 0 ≤ R)] using h
  · simpa only [mul_zero, zero_mul] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul
        (5 * Real.exp |z.re| * reciprocalTailConstant (1 + |z.im|))).mul_const |w - v|

theorem tendsto_integral_stripFourier_vertical_left (z : ℂ) (v w : ℝ)
    (hv : |v| ≤ 1) (hw : |w| ≤ 1) :
    Tendsto (fun R : ℝ => ∫ t : ℝ in v..w,
      stripFourierKernel z ((-R : ℝ) + (t : ℂ) * Complex.I)) atTop (𝓝 0) := by
  refine squeeze_zero_norm' (a := fun R : ℝ =>
    (5 * Real.exp |z.re| * reciprocalTailConstant (1 + |z.im|)) *
      Real.exp (-R) * |w - v|) ?_ ?_
  · filter_upwards [eventually_ge_atTop (3 : ℝ)] with R hR
    have h := integral_stripFourier_vertical_norm_le z (-R) v w 1
      (by rwa [abs_neg, abs_of_nonneg (by linarith : 0 ≤ R)]) hv hw
    simpa only [one_mul, abs_neg, abs_of_nonneg (by linarith : 0 ≤ R)] using h
  · simpa only [mul_zero, zero_mul] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul
        (5 * Real.exp |z.re| * reciprocalTailConstant (1 + |z.im|))).mul_const |w - v|

/-- Actual contour shifting, justified by integrability, the rectangle identity,
and the proved decay of both vertical sides. -/
theorem integral_stripFourier_line_eq (z : ℂ) (v w : ℝ)
    (hv : |v| ≤ 1) (hw : |w| ≤ 1) :
    (∫ u : ℝ, stripFourierKernel z ((u : ℂ) + (v : ℂ) * Complex.I)) =
      ∫ u : ℝ, stripFourierKernel z ((u : ℂ) + (w : ℂ) * Complex.I) := by
  have h1 := intervalIntegral_tendsto_integral (integrable_stripFourier_line z v hv)
    tendsto_neg_atTop_atBot tendsto_id
  have h2 := intervalIntegral_tendsto_integral (integrable_stripFourier_line z w hw)
    tendsto_neg_atTop_atBot tendsto_id
  have h3 := (tendsto_integral_stripFourier_vertical_right z v w hv hw).const_mul Complex.I
  have h4 := (tendsto_integral_stripFourier_vertical_left z v w hv hw).const_mul Complex.I
  have hlim := ((h1.sub h2).add h3).sub h4
  simp only [mul_zero, add_zero, sub_zero] at hlim
  have hz := hlim.congr' (Filter.Eventually.of_forall
    (fun R : ℝ => integral_stripFourier_rectangle z (-R) R v w hv hw))
  exact sub_eq_zero.mp (tendsto_nhds_unique hz tendsto_const_nhds)

/-- A height-sensitive estimate preserves the exponential gain from shifting
opposite to the sign of the real part of the frequency. -/
theorem stripFourierKernel_norm_le_height (z : ℂ) (u v : ℝ) (hv : |v| ≤ 1) :
    ‖stripFourierKernel z ((u : ℂ) + (v : ℂ) * Complex.I)‖ ≤
      (5 * Real.exp (z.re * v)) *
        (Real.exp (|z.im| * |u|) * ‖reciprocalTransform u‖) := by
  have hp := reciprocalExtension_norm_le_five ((u : ℂ) + (v : ℂ) * Complex.I)
    (by simpa using hv)
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_I_re,
    Complex.ofReal_im, neg_zero, add_zero] at hp
  have he : z.im * u + z.re * v ≤ |z.im| * |u| + z.re * v := by
    have h := le_abs_self (z.im * u)
    rw [abs_mul] at h
    linarith
  rw [stripFourierKernel, norm_mul, norm_stripFourier_exponential]
  calc
    _ ≤ (5 * ‖reciprocalTransform u‖) * Real.exp (|z.im| * |u| + z.re * v) :=
      mul_le_mul hp (Real.exp_le_exp.mpr he) (le_of_lt (Real.exp_pos _))
        (by positivity)
    _ = _ := by rw [Real.exp_add]; ring

theorem integral_stripFourier_line_norm_le_height (z : ℂ) (v : ℝ) (hv : |v| ≤ 1) :
    ‖∫ u : ℝ, stripFourierKernel z ((u : ℂ) + (v : ℂ) * Complex.I)‖ ≤
      (5 * Real.exp (z.re * v)) *
        ∫ u : ℝ, Real.exp (|z.im| * |u|) * ‖reciprocalTransform u‖ := by
  calc
    _ ≤ ∫ u : ℝ, ‖stripFourierKernel z ((u : ℂ) + (v : ℂ) * Complex.I)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ u : ℝ, (5 * Real.exp (z.re * v)) *
        (Real.exp (|z.im| * |u|) * ‖reciprocalTransform u‖) := by
      exact integral_mono (integrable_stripFourier_line z v hv).norm
        ((integrable_exp_norm_reciprocalTransform |z.im|).const_mul _)
        (fun u => stripFourierKernel_norm_le_height z u v hv)
    _ = _ := integral_const_mul _ _

/-- Exponential decay of the actual inverse Fourier integral in the real
direction, with a finite majorant depending only on the imaginary part. -/
theorem inverseFourierIntegral_norm_le_exp (z : ℂ) :
    ‖∫ u : ℝ, reciprocalTransform u * Complex.exp (-Complex.I * z * (u : ℂ))‖ ≤
      (5 * Real.exp (-|z.re|)) *
        ∫ u : ℝ, Real.exp (|z.im| * |u|) * ‖reciprocalTransform u‖ := by
  by_cases hz : 0 ≤ z.re
  · have hb := integral_stripFourier_line_norm_le_height z (-1) (by norm_num)
    rw [← integral_stripFourier_line_eq z 0 (-1) (by norm_num) (by norm_num)] at hb
    simpa [stripFourierKernel, reciprocalExtension_ofReal, abs_of_nonneg hz] using hb
  · have hb := integral_stripFourier_line_norm_le_height z 1 (by norm_num)
    rw [← integral_stripFourier_line_eq z 0 1 (by norm_num) (by norm_num)] at hb
    simpa [stripFourierKernel, reciprocalExtension_ofReal,
      abs_of_neg (lt_of_not_ge hz)] using hb

end ReciprocalXi
