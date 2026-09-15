import ProofWorkspace.Final.XiThetaComplexFull
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.TaylorSeries

set_option autoImplicit false
noncomputable section
open Set Metric Complex
namespace ReciprocalXi

theorem theta_disk_re_lower (c : ℝ) (z : ℂ) (hz : z∈closedBall (c:ℂ) (c/2)) :
    c/2≤z.re := by
  have hn : ‖z-(c:ℂ)‖≤c/2 := by simpa only [mem_closedBall, dist_eq_norm] using hz
  have ha := (Complex.abs_re_le_norm (z-(c:ℂ))).trans hn
  simp only [Complex.sub_re, Complex.ofReal_re] at ha
  linarith [(abs_le.mp ha).1]

theorem theta48_diffContOnCl_disk (c : ℝ) (hc : 1≤c) :
    DiffContOnCl ℂ (complexThetaFiniteIntegrand 48 4) (ball (c:ℂ) (c/2)) := by
  have hd : DifferentiableOn ℂ (complexThetaFiniteIntegrand 48 4) {z : ℂ | 0<z.re} := by
    intro z hz
    exact (complexThetaFiniteIntegrand_differentiableAt 48 4 z hz).differentiableWithinAt
  apply hd.diffContOnCl_ball
  intro z hz
  have h := theta_disk_re_lower c z hz
  change 0<z.re
  linarith

def theta48TaylorCoefficient (c : ℝ) (n : ℕ) : ℂ :=
  (n.factorial:ℂ)⁻¹*iteratedDeriv n (complexThetaFiniteIntegrand 48 4) (c:ℂ)

theorem theta48TaylorCoefficient_norm_le (c : ℝ) (n : ℕ) (hc : 1≤c) :
    ‖theta48TaylorCoefficient c n‖≤(10:ℝ)^14/(c/2)^n := by
  have hR : 0<c/2 := by linarith
  have hn : (0:ℝ)<n.factorial := by exact_mod_cast n.factorial_pos
  have hd := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR
    (theta48_diffContOnCl_disk c hc) (fun z hz ↦
      complexThetaFiniteIntegrand_48_norm_le z (by
        have h := theta_disk_re_lower c z (sphere_subset_closedBall hz)
        linarith))
  have h := mul_le_mul_of_nonneg_left hd (inv_nonneg.mpr hn.le)
  unfold theta48TaylorCoefficient
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  convert h using 1
  field_simp

theorem hasSum_theta48Taylor (c : ℝ) (z : ℂ) (hc : 1≤c) (hz : ‖z-(c:ℂ)‖<c/2) :
    HasSum (fun n : ℕ ↦ theta48TaylorCoefficient c n*(z-(c:ℂ))^n)
      (complexThetaFiniteIntegrand 48 4 z) := by
  have hd := (theta48_diffContOnCl_disk c hc).differentiableOn
  have h := Complex.hasSum_taylorSeries_on_ball hd
    (show z∈ball (c:ℂ) (c/2) by simpa only [mem_ball, dist_eq_norm] using hz)
  convert h using 1
  funext n
  simp only [theta48TaylorCoefficient, smul_eq_mul]
  ring

def theta48TaylorPolynomial (c : ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  ∑ n ∈ Finset.range N, theta48TaylorCoefficient c n*(z-(c:ℂ))^n

theorem theta48Taylor_term_le (c : ℝ) (z : ℂ) (n : ℕ) (hc : 1≤c)
    (hz : ‖z-(c:ℂ)‖≤c/16) :
    ‖theta48TaylorCoefficient c n*(z-(c:ℂ))^n‖≤(10:ℝ)^14*(1/8:ℝ)^n := by
  have hR : 0<c/2 := by linarith
  have hq : ‖z-(c:ℂ)‖/(c/2)≤1/8 := (div_le_iff₀ hR).mpr (by linarith)
  rw [norm_mul, norm_pow]
  calc
    _ ≤ ((10:ℝ)^14/(c/2)^n)*‖z-(c:ℂ)‖^n :=
      mul_le_mul_of_nonneg_right (theta48TaylorCoefficient_norm_le c n hc) (by positivity)
    _ = (10:ℝ)^14*(‖z-(c:ℂ)‖/(c/2))^n := by
      generalize c/2=R
      rw [div_pow]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hq n) (by positivity)

theorem theta48Taylor_remainder_le (c : ℝ) (z : ℂ) (N : ℕ) (hc : 1≤c)
    (hz : ‖z-(c:ℂ)‖≤c/16) :
    ‖complexThetaFiniteIntegrand 48 4 z-theta48TaylorPolynomial c N z‖≤
      (10:ℝ)^14*(1/8:ℝ)^N/(1-1/8) := by
  have hzr : ‖z-(c:ℂ)‖<c/2 := by linarith
  have ht := (hasSum_nat_add_iff' N).mpr (hasSum_theta48Taylor c z hc hzr)
  have hg := (hasSum_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/8)
    (by norm_num : (1/8:ℝ)<1)).mul_left ((10:ℝ)^14*(1/8:ℝ)^N)
  have hb : ∀ n : ℕ, ‖theta48TaylorCoefficient c (n+N)*(z-(c:ℂ))^(n+N)‖≤
      (10:ℝ)^14*(1/8:ℝ)^N*(1/8:ℝ)^n := by
    intro n
    have h := theta48Taylor_term_le c z (n+N) hc hz
    convert h using 1
    rw [pow_add]
    ring
  have h := ht.norm_le_of_bounded hg hb
  simpa only [theta48TaylorPolynomial, div_eq_mul_inv] using h

theorem theta48Taylor40_remainder_le (c : ℝ) (z : ℂ) (hc : 1≤c)
    (hz : ‖z-(c:ℂ)‖≤c/16) :
    ‖complexThetaFiniteIntegrand 48 4 z-theta48TaylorPolynomial c 40 z‖≤1/(10:ℝ)^22 := by
  apply (theta48Taylor_remainder_le c z 40 hc hz).trans
  norm_num

end ReciprocalXi
