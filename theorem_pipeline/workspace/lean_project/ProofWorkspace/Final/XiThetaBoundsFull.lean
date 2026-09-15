import ProofWorkspace.Final.XiRealBoundsFull
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Actual theta-kernel bounds for the central real Xi interval

The inequalities here are derived from mathlib's Gaussian-series definition of
the actual Hurwitz theta kernel. They are not numerical enclosure assumptions.
-/

noncomputable section
open MeasureTheory Set
namespace ReciprocalXi

theorem cosKernel_zero_sub_eq (t : ℝ) (ht : 0 < t) :
    HurwitzZeta.cosKernel 0 t - 1 = 2 * HurwitzKernelBounds.F_nat 0 1 t := by
  have h : HasSum (fun n : ℕ => 2 * Real.exp (-Real.pi * (n + 1 : ℝ) ^ 2 * t))
      (HurwitzZeta.cosKernel 0 t - 1) := by
    simpa using HurwitzZeta.hasSum_nat_cosKernel₀ 0 ht
  rw [← h.tsum_eq, HurwitzKernelBounds.F_nat, ← tsum_mul_left]
  apply tsum_congr
  intro n
  simp [HurwitzKernelBounds.f_nat]

/-- Uniform Gaussian tail bound for the actual theta kernel, valid on the
whole interval t≥1. -/
theorem cosKernel_zero_sub_abs_le (t : ℝ) (ht : 1 ≤ t) :
    |HurwitzZeta.cosKernel 0 t - 1| ≤ 4 * Real.exp (-Real.pi * t) := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hseries := HurwitzKernelBounds.F_nat_zero_le (a := 1) zero_le_one ht0
  norm_num only [one_pow, mul_one, Real.norm_eq_abs] at hseries
  have hpt : 1 ≤ Real.pi * t := by nlinarith [Real.two_le_pi]
  have hExp : 2 ≤ Real.exp (Real.pi * t) := by
    linarith [Real.add_one_le_exp (Real.pi * t)]
  have he : Real.exp (-Real.pi * t) ≤ 1 / 2 := by
    rw [show -Real.pi * t = -(Real.pi * t) by ring, Real.exp_neg]
    rw [← one_div]
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    linarith
  have hden : 0 < 1 - Real.exp (-Real.pi * t) := by linarith
  have hfrac : Real.exp (-Real.pi * t) / (1 - Real.exp (-Real.pi * t)) ≤
      2 * Real.exp (-Real.pi * t) := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [Real.exp_pos (-Real.pi * t)]
  rw [cosKernel_zero_sub_eq t ht0, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith

def thetaMellinIntegrand (s : ℂ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ (s - 1) * ((HurwitzZeta.cosKernel 0 t - 1 : ℝ) : ℂ)

theorem thetaMellinIntegrand_norm_le (s : ℂ) (hs : s.re ≤ 1) (t : ℝ) (ht : 1 ≤ t) :
    ‖thetaMellinIntegrand s t‖ ≤ 4 * Real.exp (-Real.pi * t) := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hp : t ^ (s.re - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht (by linarith)
  have hk := cosKernel_zero_sub_abs_le t ht
  unfold thetaMellinIntegrand
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
  simp only [Complex.sub_re, Complex.one_re, Complex.norm_real, Real.norm_eq_abs]
  have h := mul_le_mul_of_nonneg_right hp (abs_nonneg (HurwitzZeta.cosKernel 0 t - 1))
  linarith

theorem continuousOn_thetaMellinIntegrand (s : ℂ) :
    ContinuousOn (thetaMellinIntegrand s) (Ioi 1) := by
  have hk := (HurwitzZeta.continuousOn_cosKernel 0).mono
    (show Ioi (1 : ℝ) ⊆ Ioi 0 by
      intro t ht
      change 1 < t at ht
      change 0 < t
      linarith)
  unfold thetaMellinIntegrand
  apply ContinuousOn.mul
  · apply Complex.continuous_ofReal.continuousOn.cpow_const
    intro t ht
    apply Complex.mem_slitPlane_iff.mpr
    exact Or.inl (by change 0 < t; have ht' : 1 < t := ht; linarith)
  · exact Complex.continuous_ofReal.comp_continuousOn (hk.sub continuousOn_const)

theorem integrableOn_thetaMellinIntegrand (s : ℂ) (hs : s.re ≤ 1) :
    IntegrableOn (thetaMellinIntegrand s) (Ioi 1) := by
  have hmajor := (exp_neg_integrableOn_Ioi 1 Real.pi_pos).const_mul 4
  apply hmajor.mono'
  · exact (continuousOn_thetaMellinIntegrand s).aestronglyMeasurable measurableSet_Ioi
  · apply (ae_restrict_iff' measurableSet_Ioi).mpr
    exact Filter.Eventually.of_forall fun t ht => thetaMellinIntegrand_norm_le s hs t ht.le

/-- An explicit norm bound for the upper-half theta integral; valid throughout
the complex half-plane Re(s)≤1, including the central real Xi parameters. -/
theorem thetaMellinIntegral_norm_le (s : ℂ) (hs : s.re ≤ 1) :
    ‖∫ t : ℝ in Ioi 1, thetaMellinIntegrand s t‖ ≤
      4 * Real.exp (-Real.pi) / Real.pi := by
  have hi := integrableOn_thetaMellinIntegrand s hs
  have hmajor := (exp_neg_integrableOn_Ioi 1 Real.pi_pos).const_mul 4
  calc
    ‖∫ t : ℝ in Ioi 1, thetaMellinIntegrand s t‖ ≤
        ∫ t : ℝ in Ioi 1, ‖thetaMellinIntegrand s t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ in Ioi 1, 4 * Real.exp (-Real.pi * t) := by
      apply integral_mono_ae hi.norm hmajor
      apply (ae_restrict_iff' measurableSet_Ioi).mpr
      exact Filter.Eventually.of_forall fun t ht => thetaMellinIntegrand_norm_le s hs t ht.le
    _ = 4 * Real.exp (-Real.pi) / Real.pi := by
      rw [integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos Real.pi_pos) 1]
      simp only [mul_one, neg_div_neg_eq]
      ring

theorem thetaMellinIntegral_norm_lt_two (s : ℂ) (hs : s.re ≤ 1) :
    ‖∫ t : ℝ in Ioi 1, thetaMellinIntegrand s t‖ < 2 := by
  apply lt_of_le_of_lt (thetaMellinIntegral_norm_le s hs)
  apply (div_lt_iff₀ Real.pi_pos).mpr
  have he : Real.exp (-Real.pi) < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos Real.pi_pos)
  linarith [Real.two_le_pi]

end ReciprocalXi
