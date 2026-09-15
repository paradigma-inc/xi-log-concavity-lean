import ProofWorkspace.Final.XiThetaFiniteSumFull
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds

set_option autoImplicit false
noncomputable section
open Set Complex
namespace ReciprocalXi

def complexThetaExponent (x : ℝ) : ℂ := -3/4+I*(x:ℂ)/4

def complexThetaFiniteIntegrand (x : ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  z^(complexThetaExponent x)*
    (2*(∑ n ∈ Finset.range N, Complex.exp (((-Real.pi*((n:ℝ)+1)^2:ℝ):ℂ)*z)))

theorem complexThetaExponent_re (x : ℝ) : (complexThetaExponent x).re = -3/4 := by
  simp [complexThetaExponent, Complex.mul_re, Complex.mul_im]

theorem complexThetaExponent_im (x : ℝ) : (complexThetaExponent x).im = x/4 := by
  simp [complexThetaExponent, Complex.mul_re, Complex.mul_im]

theorem complexThetaFiniteIntegrand_differentiableAt (x : ℝ) (N : ℕ) (z : ℂ)
    (hz : 0<z.re) : DifferentiableAt ℂ (complexThetaFiniteIntegrand x N) z := by
  have hs : z∈Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl hz)
  have hp : DifferentiableAt ℂ (fun w : ℂ ↦ w^(complexThetaExponent x)) z :=
    differentiableAt_id.cpow_const hs
  have he : Differentiable ℂ (fun w : ℂ ↦
      2*(∑ n ∈ Finset.range N, Complex.exp (((-Real.pi*((n:ℝ)+1)^2:ℝ):ℂ)*w))) := by fun_prop
  exact hp.mul (he z)

theorem complexThetaFiniteIntegrand_re (x t : ℝ) (N : ℕ) (ht : 0<t) :
    (complexThetaFiniteIntegrand x N (t:ℂ)).re=realThetaFiniteIntegrand x N t := by
  have he : (2*(∑ n ∈ Finset.range N,
      Complex.exp (((-Real.pi*((n:ℝ)+1)^2:ℝ):ℂ)*(t:ℂ)))) =
      ((2*(∑ n ∈ Finset.range N, Real.exp (-Real.pi*((n:ℝ)+1)^2*t)):ℝ):ℂ) := by
    push_cast
    rfl
  have ht0 : (t:ℂ)≠0 := by exact_mod_cast ht.ne'
  rw [complexThetaFiniteIntegrand, he, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, Complex.cpow_def_of_ne_zero ht0,
    ← Complex.ofReal_log ht.le, Complex.exp_re]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, zero_add, sub_zero, complexThetaExponent_re, complexThetaExponent_im]
  unfold realThetaFiniteIntegrand
  rw [Real.rpow_def_of_pos ht]
  congr 2 <;> congr 1 <;> ring

theorem complexThetaFiniteIntegrand_norm_le (x : ℝ) (N : ℕ) (z : ℂ)
    (hz : 1/2≤z.re) :
    ‖complexThetaFiniteIntegrand x N z‖≤4*(N:ℝ)*Real.exp (|x| *Real.pi/8) := by
  have hz0 : 0<z.re := by linarith
  have hzn : z≠0 := by intro he; simp [he] at hz0
  have hn : (1/2:ℝ)≤‖z‖ := hz.trans (Complex.re_le_norm z)
  have hp : ‖z‖^(-3/4:ℝ)≤2 := by
    calc
      _ ≤ (1/2:ℝ)^(-3/4:ℝ) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hn (by norm_num)
      _ ≤ (1/2:ℝ)^(-1:ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by norm_num)
      _ = 2 := by norm_num
  have ha := Complex.abs_arg_le_pi_div_two_iff.mpr hz0.le
  have hx : -(Complex.arg z*(x/4))≤|x| *Real.pi/8 := by
    calc
      _ ≤ |Complex.arg z*(x/4)| := neg_le_abs _
      _ = |Complex.arg z| *(|x| /4) := by rw [abs_mul, abs_div]; norm_num
      _ ≤ (Real.pi/2)*(|x| /4) := mul_le_mul_of_nonneg_right ha (by positivity)
      _ = _ := by ring
  have hpow : ‖z^(complexThetaExponent x)‖≤2*Real.exp (|x| *Real.pi/8) := by
    rw [Complex.norm_cpow_of_ne_zero hzn, complexThetaExponent_re,
      complexThetaExponent_im, div_eq_mul_inv, ← Real.exp_neg]
    exact mul_le_mul hp (Real.exp_le_exp.mpr hx) (Real.exp_pos _).le (by norm_num)
  have hsum : ‖2*(∑ n ∈ Finset.range N,
      Complex.exp (((-Real.pi*((n:ℝ)+1)^2:ℝ):ℂ)*z))‖≤2*(N:ℝ) := by
    rw [norm_mul, Complex.norm_ofNat]
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤2)
    calc
      _ ≤ ∑ n ∈ Finset.range N, ‖Complex.exp (((-Real.pi*((n:ℝ)+1)^2:ℝ):ℂ)*z)‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ Finset.range N, (1:ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        rw [Complex.norm_exp]
        apply Real.exp_le_one_iff.mpr
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        exact mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr Real.pi_pos.le) (sq_nonneg _)) hz0.le
      _ = _ := by simp
  rw [complexThetaFiniteIntegrand, norm_mul]
  have h := mul_le_mul hpow hsum (norm_nonneg _) (by positivity)
  convert h using 1 <;> ring

theorem complexThetaFiniteIntegrand_48_norm_le (z : ℂ) (hz : 1/2≤z.re) :
    ‖complexThetaFiniteIntegrand 48 4 z‖≤(10:ℝ)^14 := by
  have h := complexThetaFiniteIntegrand_norm_le 48 4 z hz
  norm_num at h
  have he : Real.exp (|(48:ℝ)| *Real.pi/8)≤(3:ℝ)^24 := by
    calc
      _ ≤ Real.exp 24 := Real.exp_le_exp.mpr (by norm_num; nlinarith [Real.pi_lt_four])
      _ = (Real.exp 1)^24 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ (3:ℝ)^24 := pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_one_lt_three.le 24
  norm_num at he
  nlinarith

end ReciprocalXi
