import ProofWorkspace.Final.XiLowZeroTaylorFull
import ProofWorkspace.Final.XiThetaCoefficientFull
import ProofWorkspace.Final.RationalComplexFull

set_option autoImplicit false
noncomputable section
open Set Metric Complex
namespace ReciprocalXi

theorem lowZeroAtom_norm_gaussian (x : ℝ) (k : ℕ) (z : ℂ)
    (hz : 1/2≤z.re) :
    ‖complexPowerExpAtom (complexThetaExponent x) (Real.pi*(k:ℝ)^2) z‖≤
      2*Real.exp (|x| *Real.pi/8)*Real.exp (-Real.pi*(k:ℝ)^2*z.re) := by
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
      _ = |Complex.arg z| *(|x|/4) := by rw [abs_mul,abs_div]; norm_num
      _ ≤ (Real.pi/2)*(|x|/4) := mul_le_mul_of_nonneg_right ha (by positivity)
      _ = _ := by ring
  have hpow : ‖z^(complexThetaExponent x)‖≤2*Real.exp (|x| *Real.pi/8) := by
    rw [Complex.norm_cpow_of_ne_zero hzn,complexThetaExponent_re,
      complexThetaExponent_im,div_eq_mul_inv,← Real.exp_neg]
    exact mul_le_mul hp (Real.exp_le_exp.mpr hx) (Real.exp_pos _).le (by norm_num)
  unfold complexPowerExpAtom
  rw [norm_mul,Complex.norm_exp]
  simp only [Complex.mul_re,Complex.neg_re,Complex.ofReal_re,
    Complex.neg_im,Complex.ofReal_im,neg_zero,zero_mul,sub_zero]
  convert mul_le_mul_of_nonneg_right hpow
    (Real.exp_pos (-Real.pi*(k:ℝ)^2*z.re)).le using 1 <;> ring_nf

theorem exp_neg_192_lowZero_upper : Real.exp (-192)≤1/(10:ℝ)^82 := by
  have he : (10:ℝ)^82≤Real.exp 192 := by
    calc
      _ = ((10:ℝ)^41)^2 := by norm_num
      _ ≤ (Real.exp 96)^2 :=
        pow_le_pow_left₀ (by positivity) exp_96_lower_for_lowZero 2
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  rw [Real.exp_neg,← one_div]
  exact one_div_le_one_div_of_le (by positivity) he

theorem lowZero_smallDisk_re_lower (c : ℝ) (z : ℂ)
    (hz : z∈closedBall (c:ℂ) (c/16)) : 15*c/16≤z.re := by
  have hn : ‖z-(c:ℂ)‖≤c/16 := by
    simpa only [mem_closedBall,dist_eq_norm] using hz
  have ha := (Complex.abs_re_le_norm (z-(c:ℂ))).trans hn
  simp only [Complex.sub_re,Complex.ofReal_re] at ha
  linarith [(abs_le.mp ha).1]

theorem lowZeroFarAtom_disk_norm_le (x c : ℝ) (k : ℕ) (z : ℂ)
    (hx : |x|≤60) (hc : 1≤c) (hkc : 72≤(k:ℝ)^2*c)
    (hz : z∈closedBall (c:ℂ) (c/16)) :
    ‖complexPowerExpAtom (complexThetaExponent x) (Real.pi*(k:ℝ)^2) z‖≤1/(10:ℝ)^50 := by
  have hzR := lowZero_smallDisk_re_lower c z hz
  have h := lowZeroAtom_norm_gaussian x k z (by linarith)
  have hp : 192≤Real.pi*(k:ℝ)^2*(15*c/16) := by
    have hmul := mul_le_mul_of_nonneg_right Real.pi_gt_three.le
      (show 0≤(k:ℝ)^2*c by positivity)
    nlinarith
  have hzprod := mul_le_mul_of_nonneg_left hzR
    (show 0≤Real.pi*(k:ℝ)^2 by positivity)
  have hg : Real.exp (-Real.pi*(k:ℝ)^2*z.re)≤1/(10:ℝ)^82 :=
    (Real.exp_le_exp.mpr (by nlinarith)).trans exp_neg_192_lowZero_upper
  have he : Real.exp (|x| *Real.pi/8)≤(3:ℝ)^30 := by
    calc
      _ ≤ Real.exp 30 := Real.exp_le_exp.mpr (by
        have hmul := mul_le_mul_of_nonneg_right hx Real.pi_pos.le
        nlinarith [Real.pi_lt_four])
      _ = (Real.exp 1)^30 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ (3:ℝ)^30 := pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_one_lt_three.le 30
  have hm := mul_le_mul
    (mul_le_mul_of_nonneg_left he (by norm_num : (0:ℝ)≤2))
    hg (Real.exp_pos _).le (by positivity : (0:ℝ)≤2*3^30)
  exact h.trans (hm.trans (by norm_num))

theorem lowZeroFarAtom_scaledCoefficient_norm_le (x c h : ℝ) (k n : ℕ)
    (hx : |x|≤60) (hc : 1≤c) (hh0 : 0≤h) (hh : h≤c/16)
    (hkc : 72≤(k:ℝ)^2*c) :
    ‖scaledPowerExpCoefficient (complexThetaExponent x) (c:ℂ)
      (Real.pi*(k:ℝ)^2) h n‖≤1/(10:ℝ)^50 := by
  have hc0 : 0<c := by linarith
  have hR : 0<c/16 := by linarith
  have hn : (0:ℝ)<n.factorial := by exact_mod_cast n.factorial_pos
  have hd : DiffContOnCl ℂ
      (complexPowerExpAtom (complexThetaExponent x) (Real.pi*(k:ℝ)^2))
      (ball (c:ℂ) (c/16)) := by
    have hdiff : DifferentiableOn ℂ
        (complexPowerExpAtom (complexThetaExponent x) (Real.pi*(k:ℝ)^2))
        {z : ℂ | 0<z.re} := by
      intro z hz
      exact (complexPowerExpAtom_analyticAt _ _ _
        (Complex.mem_slitPlane_iff.mpr (Or.inl hz))).differentiableAt.differentiableWithinAt
    apply hdiff.diffContOnCl_ball
    intro z hz
    have hzR := lowZero_smallDisk_re_lower c z hz
    change 0<z.re
    linarith
  have hder := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR hd
    (fun z hz ↦ lowZeroFarAtom_disk_norm_le x c k z hx hc hkc (sphere_subset_closedBall hz))
  unfold scaledPowerExpCoefficient complexPowerExpTaylorCoefficient
  rw [norm_mul,norm_div,Complex.norm_natCast,norm_pow,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg hh0]
  have ht := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hder hn.le) (pow_nonneg hh0 n)
  have he : ((n.factorial:ℝ)*(1/(10:ℝ)^50)/(c/16)^n)/(n.factorial:ℝ)*h^n=
      (1/(10:ℝ)^50)*(h/(c/16))^n := by
    simp only [div_pow]
    field_simp
  have hq : 0≤h/(c/16) := div_nonneg hh0 hR.le
  have hq1 : h/(c/16)≤1 := (div_le_one hR).mpr hh
  rw [he] at ht
  exact ht.trans (by
    simpa using mul_le_mul_of_nonneg_left (pow_le_one₀ hq hq1)
      (by positivity : (0:ℝ)≤1/(10:ℝ)^50))

theorem lowZeroFarAtom_zeroCoefficient_error (x c h : ℝ) (k n : ℕ)
    (hx : |x|≤60) (hc : 1≤c) (hh0 : 0≤h) (hh : h≤c/16)
    (hkc : 72≤(k:ℝ)^2*c) :
    ‖ratComplexValue (0,0)-scaledPowerExpCoefficient (complexThetaExponent x)
      (c:ℂ) (Real.pi*(k:ℝ)^2) h n‖≤1/(10:ℝ)^50 := by
  simpa [ratComplexValue] using
    lowZeroFarAtom_scaledCoefficient_norm_le x c h k n hx hc hh0 hh hkc

end ReciprocalXi

