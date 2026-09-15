import ProofWorkspace.Final.XiRealBoundsFull
import ProofWorkspace.Final.XiMellinIdentityFull
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Actual reciprocal-Xi Fourier normalization and regularity

The Fourier identity below matches the original inverse integral exactly,
including its sign and frequency scaling. Integrability and regularity will
use the proved Xi estimates, never an assumed numerical enclosure.
-/

noncomputable section
open MeasureTheory
open Set
open scoped FourierTransform Topology ContDiff
namespace ReciprocalXi

/-- Positivity of the real part of actual Xi on the entire real axis. -/
theorem xi_re_pos (s : ℝ) : 0 < (xi (s : ℂ)).re := by
  by_cases h0 : s < 0
  · exact xi_re_pos_of_lt_zero s h0
  · by_cases h1 : 1 < s
    · exact xi_re_pos_of_one_lt s h1
    · exact xi_re_pos_of_mem_Icc s ⟨le_of_not_gt h0, le_of_not_gt h1⟩

theorem xi_ofReal_ne_zero (s : ℝ) : xi (s : ℂ) ≠ 0 := by
  intro hz
  have hp := xi_re_pos s
  simp only [hz, Complex.zero_re, lt_self_iff_false] at hp

theorem F_imaginary_axis_ne_zero (u : ℝ) : F (Complex.I * (u : ℂ)) ≠ 0 := by
  rw [F_imaginary_axis]
  apply div_ne_zero
  · convert xi_ofReal_ne_zero ((1 + u) / 2) using 1
    push_cast
    rfl
  · norm_num

theorem continuous_reciprocalTransform : Continuous reciprocalTransform := by
  have hden : Continuous (fun u : ℝ => F (Complex.I * (u : ℂ))) := by
    exact continuous_F.comp (by fun_prop)
  exact continuous_const.div hden F_imaginary_axis_ne_zero

/-- The central theta bound closes the only remaining interval: every
exponentially weighted actual reciprocal transform is integrable globally. -/
theorem integrable_weighted_reciprocalTransform (q : ℝ) :
    Integrable (fun u : ℝ => Real.exp (q * |u|) • reciprocalTransform u) := by
  have hc : Continuous (fun u : ℝ => Real.exp (q * |u|) • reciprocalTransform u) := by
    have hr := continuous_reciprocalTransform
    fun_prop
  have hi : IntegrableOn (fun u : ℝ => Real.exp (q * |u|) • reciprocalTransform u)
      (Icc (-3) 3) := hc.continuousOn.integrableOn_compact isCompact_Icc
  have hu : (Iio (-3 : ℝ) ∪ Ioi 3) ∪ Icc (-3) 3 = univ := by
    ext u
    simp only [mem_union, mem_Iio, mem_Ioi, mem_Icc, mem_univ, iff_true]
    rcases lt_or_ge u (-3) with h | h
    · exact Or.inl (Or.inl h)
    · rcases lt_or_ge 3 u with h' | h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr ⟨h, h'⟩
  rw [← integrableOn_univ, ← hu]
  exact (integrableOn_weighted_reciprocalTransform_tails q).union hi

theorem integrable_reciprocalTransform : Integrable reciprocalTransform := by
  simpa only [zero_mul, Real.exp_zero, one_smul] using integrable_weighted_reciprocalTransform 0

theorem integrable_reciprocalTransform_moment (n : ℕ) :
    Integrable (fun u : ℝ => ‖u‖ ^ n * ‖reciprocalTransform u‖) := by
  have hi := (integrable_weighted_reciprocalTransform 1).norm.const_mul (n.factorial : ℝ)
  apply hi.mono'
  · have hm := measurable_reciprocalTransform
    exact (by fun_prop : Measurable (fun u : ℝ =>
      ‖u‖ ^ n * ‖reciprocalTransform u‖)).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro u
    have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
    have hp := (div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp ‖u‖ (norm_nonneg u) n)
    have h := mul_le_mul_of_nonneg_right hp (norm_nonneg (reciprocalTransform u))
    simpa only [norm_smul, Real.norm_eq_abs, abs_mul, abs_pow, abs_abs, abs_norm,
      one_mul, mul_one, abs_of_pos (Real.exp_pos _), mul_assoc, mul_left_comm, mul_comm] using h

theorem density_eq_re_fourier (x : ℝ) :
    density x = (𝓕 reciprocalTransform (x / (2 * Real.pi))).re / (2 * Real.pi) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  unfold density
  congr 2
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro u
  simp only [smul_eq_mul]
  rw [mul_comm (reciprocalTransform u)]
  congr 2
  push_cast
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

/-- Actual polynomial Fourier moments are integrable on both noncompact
tails, using the already-proved exponential bound and the exponential series. -/
theorem integrableOn_reciprocalTransform_moment_tails (n : ℕ) :
    IntegrableOn (fun u : ℝ => ‖u‖ ^ n * ‖reciprocalTransform u‖)
      (Iio (-3) ∪ Ioi 3) := by
  have hi := (integrableOn_weighted_reciprocalTransform_tails 1).norm.const_mul (n.factorial : ℝ)
  apply hi.mono'
  · have hm := measurable_reciprocalTransform
    exact (by fun_prop : Measurable (fun u : ℝ =>
      ‖u‖ ^ n * ‖reciprocalTransform u‖)).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro u
    have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
    have hp := (div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp ‖u‖ (norm_nonneg u) n)
    have h := mul_le_mul_of_nonneg_right hp (norm_nonneg (reciprocalTransform u))
    simpa only [norm_smul, Real.norm_eq_abs, abs_mul, abs_pow, abs_abs, abs_norm,
      one_mul, mul_one, abs_of_pos (Real.exp_pos _), mul_assoc, mul_left_comm, mul_comm] using h

theorem contDiff_fourier_reciprocalTransform : ContDiff ℝ ∞ (𝓕 reciprocalTransform) :=
  Real.contDiff_fourier (fun n _ => integrable_reciprocalTransform_moment n)

/-- The actual density is smooth on the entire real line. All Fourier moment
hypotheses have been discharged using the actual Xi/Gamma/theta bounds. -/
theorem contDiff_density : ContDiff ℝ ∞ density := by
  have h : ContDiff ℝ ∞ (fun x : ℝ =>
      (𝓕 reciprocalTransform (x / (2 * Real.pi))).re / (2 * Real.pi)) :=
    (Complex.reCLM.contDiff.comp
      (contDiff_fourier_reciprocalTransform.comp
        (contDiff_id.div_const (2 * Real.pi)))).div_const (2 * Real.pi)
  simpa only [← density_eq_re_fourier] using h

theorem differentiable_density : Differentiable ℝ density :=
  contDiff_density.differentiable (by simp)

theorem differentiable_deriv_density : Differentiable ℝ (deriv density) := by
  have h : ContDiff ℝ 2 density := contDiff_density.of_le (by
    exact WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  exact h.differentiable_deriv_two

end ReciprocalXi
