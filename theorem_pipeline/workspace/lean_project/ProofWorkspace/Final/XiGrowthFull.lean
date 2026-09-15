import ProofWorkspace.Final.XiZeroGeometryFull
import ProofWorkspace.Final.XiStripBoundsFull
import ProofWorkspace.Final.ZetaVerticalBoundsFull
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.Convex.Jensen

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace ReciprocalXi

theorem complexGamma_norm_le_real (s : ℂ) (hs : 0 < s.re) :
    ‖Complex.Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Complex.Gamma_eq_integral hs, Complex.GammaIntegral, Real.Gamma_eq_integral hs]
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), Complex.norm_cpow_eq_rpow_re_of_pos ht,
    Complex.sub_re, Complex.one_re]

theorem realGamma_le_factorial (x : ℝ) (n : ℕ) (hx : 1 ≤ x) (hxn : x ≤ n+1) :
    Real.Gamma x ≤ (n.factorial:ℝ) := by
  have h := Real.convexOn_Gamma.le_max_of_mem_Icc
    (by norm_num : (1:ℝ) ∈ Ioi 0)
    (by show 0 < (n:ℝ)+1; positivity : (n:ℝ)+1 ∈ Ioi 0) ⟨hx,hxn⟩
  rw [Real.Gamma_one, Real.Gamma_nat_eq_factorial] at h
  have hn : (1:ℝ) ≤ n.factorial := by
    have hp := Nat.factorial_pos n
    exact_mod_cast (show 1 ≤ n.factorial by omega)
  simpa only [max_eq_right hn] using h

theorem xi_norm_le_factorial_of_two_le_re (s : ℂ) (n : ℕ)
    (hs : 2 ≤ s.re) (hn : s.re ≤ 2*((n:ℝ)+1)) :
    ‖xi s‖ ≤ ‖s‖*(‖s‖+1)*(n.factorial:ℝ) := by
  have hspos : 0 < s.re := by linarith
  have h0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have h1 : s ≠ 1 := by intro h; norm_num [h] at hs
  have hg : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hspos
  have hc : completedRiemannZeta s = riemannZeta s * Complex.Gammaℝ s :=
    ((eq_div_iff hg).mp (riemannZeta_def_of_ne_zero h0)).symm
  have hg' : ‖Complex.Gamma (s/2)‖ ≤ (n.factorial:ℝ) := by
    have h := complexGamma_norm_le_real (s/2) (by simp; linarith)
    apply h.trans
    apply realGamma_le_factorial <;> simp only [Complex.div_ofNat_re] <;> linarith
  have hp : ‖(Real.pi:ℂ)^(-s/2)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three])
    simp only [Complex.div_ofNat_re, Complex.neg_re]
    linarith
  have hgr : ‖Complex.Gammaℝ s‖ ≤ (n.factorial:ℝ) := by
    rw [Complex.Gammaℝ_def, norm_mul]
    calc
      _ ≤ 1*(n.factorial:ℝ) := mul_le_mul hp hg' (norm_nonneg _) (by norm_num)
      _ = _ := one_mul _
  rw [xi_eq_completed s h0 h1, hc, norm_div, norm_mul, norm_mul, norm_mul]
  have hsm : ‖s-1‖ ≤ ‖s‖+1 := by simpa only [norm_one] using norm_sub_le s (1:ℂ)
  have hz := riemannZeta_norm_le_two s hs
  have hprod : ‖s‖*‖s-1‖*(‖riemannZeta s‖*‖Complex.Gammaℝ s‖) ≤
      ‖s‖*(‖s‖+1)*(2*(n.factorial:ℝ)) := by
    gcongr
  norm_num only [Complex.norm_ofNat]
  linarith

theorem xi_norm_le_quadratic_central (s : ℂ)
    (hs0 : -1 ≤ s.re) (hs1 : s.re ≤ 2) :
    ‖xi s‖ ≤ (‖s‖*(‖s‖+1)+1)/2 := by
  have hz : ‖completedRiemannZeta₀ s‖ ≤ 1 := by
    linarith [completedRiemannZeta₀_norm_lt_one_eighth s hs0 hs1]
  have hsm : ‖s-1‖ ≤ ‖s‖+1 := by simpa only [norm_one] using norm_sub_le s (1:ℂ)
  have hp : ‖s*(s-1)*completedRiemannZeta₀ s‖ ≤ ‖s‖*(‖s‖+1) := by
    rw [norm_mul, norm_mul]
    calc
      _ ≤ ‖s‖*(‖s‖+1)*1 := by gcongr
      _ = _ := mul_one _
  have ha := norm_add_le (s*(s-1)*completedRiemannZeta₀ s) 1
  rw [xi, norm_div]
  norm_num only [Complex.norm_ofNat]
  norm_num only [norm_one] at ha
  linarith

/-- A global bound for the actual entire Xi, with no zero-counting assumption. -/
theorem xi_norm_le_factorial (s : ℂ) (n : ℕ) (hn : ‖s‖ ≤ n) :
    ‖xi s‖ ≤ ((n:ℝ)+2)^2 * (n.factorial:ℝ) := by
  have hf : (1:ℝ) ≤ n.factorial := by
    have hp := Nat.factorial_pos n
    exact_mod_cast (show 1 ≤ n.factorial by omega)
  have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have hf0 : (0:ℝ) ≤ n.factorial := by positivity
  have hsn := norm_nonneg s
  by_cases hr : 2 ≤ s.re
  · have h := xi_norm_le_factorial_of_two_le_re s n hr
      (by linarith [Complex.re_le_norm s])
    apply h.trans
    apply mul_le_mul_of_nonneg_right _ hf0
    nlinarith [mul_self_le_mul_self hsn hn]
  by_cases hl : -1 ≤ s.re
  · have h := xi_norm_le_quadratic_central s hl (by linarith)
    have hq : (‖s‖*(‖s‖+1)+1)/2 ≤ ((n:ℝ)+2)^2 := by
      nlinarith [mul_self_le_mul_self hsn hn]
    exact h.trans (hq.trans (le_mul_of_one_le_right (sq_nonneg _) hf))
  · have hnorm : ‖(1:ℂ)-s‖ ≤ (n:ℝ)+1 := by
      have h := norm_sub_le (1:ℂ) s
      norm_num only [norm_one] at h
      linarith
    have hσ : ((1:ℂ)-s).re ≤ (n:ℝ)+1 := (Complex.re_le_norm _).trans hnorm
    have h := xi_norm_le_factorial_of_two_le_re (1-s) n
      (by simp only [Complex.sub_re, Complex.one_re]; linarith)
      (by linarith)
    rw [xi_one_sub] at h
    apply h.trans
    apply mul_le_mul_of_nonneg_right _ hf0
    have hnprod : ‖(1:ℂ)-s‖ * (‖(1:ℂ)-s‖+1) ≤
        ((n:ℝ)+1)*((n:ℝ)+2) :=
      mul_le_mul hnorm (by linarith) (by positivity) (by positivity)
    nlinarith

theorem F_norm_le_factorial (z : ℂ) (n : ℕ) (hz : ‖z‖+1 ≤ 2*(n:ℝ)) :
    ‖F z‖ ≤ ((n:ℝ)+2)^2 * (n.factorial:ℝ) / 4 := by
  have hs : ‖(1:ℂ)/2+Complex.I*z/2‖ ≤ (n:ℝ) := by
    have h := norm_add_le ((1:ℂ)/2) (Complex.I*z/2)
    norm_num [norm_div, norm_mul, Complex.norm_I] at h
    linarith
  have h := xi_norm_le_factorial (1/2+Complex.I*z/2) n hs
  rw [F, norm_div]
  norm_num only [Complex.norm_ofNat]
  exact div_le_div_of_nonneg_right h (by norm_num)

end ReciprocalXi

