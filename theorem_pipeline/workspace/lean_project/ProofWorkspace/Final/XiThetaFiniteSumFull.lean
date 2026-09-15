import ProofWorkspace.Final.XiThetaTruncationFull

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
namespace ReciprocalXi

theorem cosKernel_zero_finite_sum_tail (N : ℕ) (t : ℝ) (ht : 0<t) :
    HurwitzZeta.cosKernel 0 t-1-
      2*(∑ n ∈ Finset.range N, Real.exp (-Real.pi*((n:ℝ)+1)^2*t)) =
        2*HurwitzKernelBounds.F_nat 0 ((N:ℝ)+1) t := by
  have hs := (HurwitzKernelBounds.summable_f_nat 0 1 ht).sum_add_tsum_nat_add N
  have he : (∑' n : ℕ, HurwitzKernelBounds.f_nat 0 1 t (n+N)) =
      HurwitzKernelBounds.F_nat 0 ((N:ℝ)+1) t := by
    apply tsum_congr
    intro n
    simp only [HurwitzKernelBounds.f_nat, Nat.cast_add, pow_zero, one_mul]
    congr 2 <;> ring
  rw [he] at hs
  simp only [HurwitzKernelBounds.f_nat, pow_zero, one_mul] at hs
  rw [cosKernel_zero_sub_eq t ht]
  have hf : (∑' n : ℕ, Real.exp (-Real.pi*((n:ℝ)+1)^2*t))=
      HurwitzKernelBounds.F_nat 0 1 t := by
    simp [HurwitzKernelBounds.F_nat, HurwitzKernelBounds.f_nat]
  rw [hf] at hs
  linarith

theorem cosKernel_zero_finite_sum_error (N : ℕ) (t : ℝ) (ht : 1≤t) :
    |HurwitzZeta.cosKernel 0 t-1-
      2*(∑ n ∈ Finset.range N, Real.exp (-Real.pi*((n:ℝ)+1)^2*t))| ≤
        4*Real.exp (-Real.pi*((N:ℝ)+1)^2*t) := by
  have ht0 : 0<t := zero_lt_one.trans_le ht
  have hb := HurwitzKernelBounds.F_nat_zero_le (a := (N:ℝ)+1) (by positivity) ht0
  have hpt : 1≤Real.pi*t := by nlinarith [Real.two_le_pi]
  have hExp : 2≤Real.exp (Real.pi*t) := by linarith [Real.add_one_le_exp (Real.pi*t)]
  have he : Real.exp (-Real.pi*t)≤1/2 := by
    rw [show -Real.pi*t = -(Real.pi*t) by ring, Real.exp_neg, ← one_div]
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    linarith
  have hd : 0<1-Real.exp (-Real.pi*t) := by linarith
  have hfrac : Real.exp (-Real.pi*((N:ℝ)+1)^2*t)/(1-Real.exp (-Real.pi*t))≤
      2*Real.exp (-Real.pi*((N:ℝ)+1)^2*t) := by
    apply (div_le_iff₀ hd).mpr
    nlinarith [Real.exp_pos (-Real.pi*((N:ℝ)+1)^2*t)]
  rw [cosKernel_zero_finite_sum_tail N t ht0, abs_mul,
    abs_of_pos (by norm_num : (0:ℝ)<2)]
  simp only [Real.norm_eq_abs] at hb
  linarith

def realThetaFiniteIntegrand (x : ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  t^(-3/4:ℝ)*Real.cos ((x/4)*Real.log t)*
    (2*(∑ n ∈ Finset.range N, Real.exp (-Real.pi*((n:ℝ)+1)^2*t)))

theorem realThetaCosineIntegrand_finite_error (x : ℝ) (N : ℕ) (t : ℝ) (ht : 1≤t) :
    |realThetaCosineIntegrand x t-realThetaFiniteIntegrand x N t|≤
      4*Real.exp (-Real.pi*((N:ℝ)+1)^2*t) := by
  have hp : t^(-3/4:ℝ)≤1 := Real.rpow_le_one_of_one_le_of_nonpos ht (by norm_num)
  have hc := Real.abs_cos_le_one ((x/4)*Real.log t)
  have hfac : |t^(-3/4:ℝ)*Real.cos ((x/4)*Real.log t)|≤1 := by
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (zero_le_one.trans ht) _)]
    calc
      _ ≤ t^(-3/4:ℝ)*1 := mul_le_mul_of_nonneg_left hc (Real.rpow_nonneg (zero_le_one.trans ht) _)
      _ ≤ 1 := by simpa using hp
  change |t^(-3/4:ℝ)*Real.cos ((x/4)*Real.log t)*(HurwitzZeta.cosKernel 0 t-1)-
    t^(-3/4:ℝ)*Real.cos ((x/4)*Real.log t)*
      (2*(∑ n ∈ Finset.range N, Real.exp (-Real.pi*((n:ℝ)+1)^2*t)))|≤_
  rw [← mul_sub, abs_mul]
  calc
    _ ≤ 1*|HurwitzZeta.cosKernel 0 t-1-
      2*(∑ n ∈ Finset.range N, Real.exp (-Real.pi*((n:ℝ)+1)^2*t))| :=
        mul_le_mul_of_nonneg_right hfac (abs_nonneg _)
    _ ≤ _ := by simpa using cosKernel_zero_finite_sum_error N t ht

end ReciprocalXi

