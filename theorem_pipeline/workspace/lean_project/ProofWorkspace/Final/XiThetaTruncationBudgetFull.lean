import ProofWorkspace.Final.XiThetaFiniteIntegralFull
import Mathlib.Analysis.Complex.ExponentialBounds

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
namespace ReciprocalXi

theorem exp_48_lower_for_theta : (10:ℝ)^19≤Real.exp 48 := by
  have he : (5/2:ℝ)≤Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  calc
    _ ≤ (5/2:ℝ)^48 := by norm_num
    _ ≤ (Real.exp 1)^48 := pow_le_pow_left₀ (by norm_num) he 48
    _ = _ := by rw [← Real.exp_nat_mul]; norm_num

theorem F48_finite_theta_truncation_error :
    |(F (48:ℂ)).re-(1-(2305/4:ℝ)*
      (∫ t : ℝ in Ioc 1 16, realThetaFiniteIntegrand 48 4 t))/8|≤1/(10:ℝ)^16 := by
  have h := F_real_finite_theta_sum_integral_error 48 16 4 (by norm_num)
  norm_num only [Nat.cast_ofNat] at h
  have he : Real.exp (-48)≤1/(10:ℝ)^19 := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by positivity) exp_48_lower_for_theta
  have h1 : Real.exp (-Real.pi*16)≤1/(10:ℝ)^19 :=
    (Real.exp_le_exp.mpr (by nlinarith [Real.pi_gt_three])).trans he
  have h2 : Real.exp (-Real.pi*((4:ℝ)+1)^2)≤1/(10:ℝ)^19 :=
    (Real.exp_le_exp.mpr (by nlinarith [Real.pi_gt_three])).trans he
  norm_num at h1 h2
  convert h.trans ?_ using 1 <;> norm_num
  apply (div_le_iff₀ (by positivity : (0:ℝ)<8*Real.pi)).mpr
  nlinarith [Real.pi_gt_three]

end ReciprocalXi
