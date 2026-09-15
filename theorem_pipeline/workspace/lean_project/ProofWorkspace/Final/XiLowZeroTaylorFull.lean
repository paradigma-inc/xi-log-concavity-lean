import ProofWorkspace.Final.XiThetaDyadicIntegralFull

set_option autoImplicit false
noncomputable section
open Set Metric Complex MeasureTheory
namespace ReciprocalXi

theorem complexThetaFiniteIntegrand_lowZero_norm_le (x : ℝ) (hx : |x|≤60)
    (z : ℂ) (hz : 1/2≤z.re) :
    ‖complexThetaFiniteIntegrand x 5 z‖≤(10:ℝ)^16 := by
  have h := complexThetaFiniteIntegrand_norm_le x 5 z hz
  have he : Real.exp (|x| *Real.pi/8)≤(3:ℝ)^30 := by
    calc
      _ ≤ Real.exp 30 := Real.exp_le_exp.mpr (by
        have hp := mul_le_mul_of_nonneg_right hx Real.pi_pos.le
        nlinarith [Real.pi_lt_four])
      _ = (Real.exp 1)^30 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ (3:ℝ)^30 := pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_one_lt_three.le 30
  norm_num at h he
  nlinarith

theorem exp_96_lower_for_lowZero : (10:ℝ)^41≤Real.exp 96 := by
  have he : (27/10:ℝ)≤Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  calc
    _ ≤ (27/10:ℝ)^96 := by norm_num
    _ ≤ (Real.exp 1)^96 := pow_le_pow_left₀ (by norm_num) he 96
    _ = _ := by rw [← Real.exp_nat_mul]; norm_num

theorem F_lowZero_finite_theta_truncation_error (x : ℝ) (hx : |x|≤60) :
    |(F (x:ℂ)).re-(1-((1+x^2)/4)*
      (∫ t : ℝ in Ioc 1 32, realThetaFiniteIntegrand x 5 t))/8|≤2/(10:ℝ)^39 := by
  have h := F_real_finite_theta_sum_integral_error x 32 5 (by norm_num)
  norm_num only [Nat.cast_ofNat] at h
  have he : Real.exp (-96)≤1/(10:ℝ)^41 := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by positivity) exp_96_lower_for_lowZero
  have h1 : Real.exp (-Real.pi*32)≤1/(10:ℝ)^41 :=
    (Real.exp_le_exp.mpr (by nlinarith [Real.pi_gt_three])).trans he
  have h2 : Real.exp (-Real.pi*((5:ℝ)+1)^2)≤1/(10:ℝ)^41 :=
    (Real.exp_le_exp.mpr (by nlinarith [Real.pi_gt_three])).trans he
  have hx2 : x^2≤3600 := by
    nlinarith [pow_le_pow_left₀ (abs_nonneg x) hx 2, sq_abs x]
  apply h.trans
  apply (div_le_iff₀ (by positivity : (0:ℝ)<8*Real.pi)).mpr
  have hp : (1+x^2)*(Real.exp (-Real.pi*32)+
      Real.exp (-Real.pi*((5:ℝ)+1)^2)/((5:ℝ)+1)^2) ≤
        3601*(1/(10:ℝ)^41+(1/(10:ℝ)^41)/36) := by
    apply mul_le_mul (by linarith) _ (by positivity) (by norm_num)
    exact add_le_add h1 (by norm_num at h2 ⊢; linarith)
  norm_num at hp ⊢
  nlinarith [Real.pi_gt_three]

theorem lowZeroTheta_diffContOnCl_disk (x c : ℝ) (hc : 1≤c) :
    DiffContOnCl ℂ (complexThetaFiniteIntegrand x 5) (ball (c:ℂ) (c/2)) := by
  have hd : DifferentiableOn ℂ (complexThetaFiniteIntegrand x 5) {z : ℂ | 0<z.re} := by
    intro z hz
    exact (complexThetaFiniteIntegrand_differentiableAt x 5 z hz).differentiableWithinAt
  apply hd.diffContOnCl_ball
  intro z hz
  have h := theta_disk_re_lower c z hz
  change 0<z.re
  linarith

def lowZeroThetaTaylorCoefficient (x c : ℝ) (n : ℕ) : ℂ :=
  (n.factorial:ℂ)⁻¹*iteratedDeriv n (complexThetaFiniteIntegrand x 5) (c:ℂ)

theorem lowZeroThetaTaylorCoefficient_norm_le (x c : ℝ) (n : ℕ) (hx : |x|≤60) (hc : 1≤c) :
    ‖lowZeroThetaTaylorCoefficient x c n‖≤(10:ℝ)^16/(c/2)^n := by
  have hR : 0<c/2 := by linarith
  have hn : (0:ℝ)<n.factorial := by exact_mod_cast n.factorial_pos
  have hd := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR
    (lowZeroTheta_diffContOnCl_disk x c hc) (fun z hz ↦
      complexThetaFiniteIntegrand_lowZero_norm_le x hx z (by
        have h := theta_disk_re_lower c z (sphere_subset_closedBall hz)
        linarith))
  have h := mul_le_mul_of_nonneg_left hd (inv_nonneg.mpr hn.le)
  unfold lowZeroThetaTaylorCoefficient
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  convert h using 1
  field_simp

theorem hasSum_lowZeroThetaTaylor (x c : ℝ) (z : ℂ) (hc : 1≤c) (hz : ‖z-(c:ℂ)‖<c/2) :
    HasSum (fun n : ℕ ↦ lowZeroThetaTaylorCoefficient x c n*(z-(c:ℂ))^n)
      (complexThetaFiniteIntegrand x 5 z) := by
  have hd := (lowZeroTheta_diffContOnCl_disk x c hc).differentiableOn
  have h := Complex.hasSum_taylorSeries_on_ball hd
    (show z∈ball (c:ℂ) (c/2) by simpa only [mem_ball, dist_eq_norm] using hz)
  convert h using 1
  funext n
  simp only [lowZeroThetaTaylorCoefficient, smul_eq_mul]
  ring

def lowZeroThetaTaylorPolynomial (x c : ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  ∑ n ∈ Finset.range N, lowZeroThetaTaylorCoefficient x c n*(z-(c:ℂ))^n

theorem lowZeroThetaTaylor_term_le (x c : ℝ) (z : ℂ) (n : ℕ) (hx : |x|≤60) (hc : 1≤c)
    (hz : ‖z-(c:ℂ)‖≤c/16) :
    ‖lowZeroThetaTaylorCoefficient x c n*(z-(c:ℂ))^n‖≤(10:ℝ)^16*(1/8:ℝ)^n := by
  have hR : 0<c/2 := by linarith
  have hq : ‖z-(c:ℂ)‖/(c/2)≤1/8 := (div_le_iff₀ hR).mpr (by linarith)
  rw [norm_mul, norm_pow]
  calc
    _ ≤ ((10:ℝ)^16/(c/2)^n)*‖z-(c:ℂ)‖^n :=
      mul_le_mul_of_nonneg_right (lowZeroThetaTaylorCoefficient_norm_le x c n hx hc) (by positivity)
    _ = (10:ℝ)^16*(‖z-(c:ℂ)‖/(c/2))^n := by
      generalize c/2=R
      rw [div_pow]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hq n) (by positivity)

theorem lowZeroThetaTaylor_remainder_le (x c : ℝ) (z : ℂ) (N : ℕ) (hx : |x|≤60) (hc : 1≤c)
    (hz : ‖z-(c:ℂ)‖≤c/16) :
    ‖complexThetaFiniteIntegrand x 5 z-lowZeroThetaTaylorPolynomial x c N z‖≤
      (10:ℝ)^16*(1/8:ℝ)^N/(1-1/8) := by
  have hzr : ‖z-(c:ℂ)‖<c/2 := by linarith
  have ht := (hasSum_nat_add_iff' N).mpr (hasSum_lowZeroThetaTaylor x c z hc hzr)
  have hg := (hasSum_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/8)
    (by norm_num : (1/8:ℝ)<1)).mul_left ((10:ℝ)^16*(1/8:ℝ)^N)
  have hb : ∀ n : ℕ, ‖lowZeroThetaTaylorCoefficient x c (n+N)*(z-(c:ℂ))^(n+N)‖≤
      (10:ℝ)^16*(1/8:ℝ)^N*(1/8:ℝ)^n := by
    intro n
    have h := lowZeroThetaTaylor_term_le x c z (n+N) hx hc hz
    convert h using 1
    rw [pow_add]
    ring
  have h := ht.norm_le_of_bounded hg hb
  simpa only [lowZeroThetaTaylorPolynomial, div_eq_mul_inv] using h

theorem lowZeroThetaTaylor80_remainder_le (x c : ℝ) (z : ℂ) (hx : |x|≤60) (hc : 1≤c)
    (hz : ‖z-(c:ℂ)‖≤c/16) :
    ‖complexThetaFiniteIntegrand x 5 z-lowZeroThetaTaylorPolynomial x c 80 z‖≤1/(10:ℝ)^56 := by
  apply (lowZeroThetaTaylor_remainder_le x c z 80 hx hc hz).trans
  norm_num


end ReciprocalXi
