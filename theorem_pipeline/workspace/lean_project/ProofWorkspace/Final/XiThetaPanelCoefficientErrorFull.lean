import ProofWorkspace.Final.XiThetaCoefficientFull
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
namespace ReciprocalXi

def theta48ScaledIntegralWeight (h : ℝ) (n : ℕ) : ℝ :=
  h*(1-(-1:ℝ)^(n+1))/(n+1:ℕ)

theorem theta48ScaledIntegralWeight_abs_le_one (h : ℝ) (n : ℕ)
    (hh0 : 0≤h) (hh1 : h≤1/2) : |theta48ScaledIntegralWeight h n|≤1 := by
  have hp : |1-(-1:ℝ)^(n+1)|≤2 := by
    simpa only [abs_one,abs_pow,abs_neg,one_pow,one_add_one_eq_two] using abs_sub (1:ℝ) ((-1:ℝ)^(n+1))
  have hn : (1:ℝ)≤(n+1:ℕ) := by exact_mod_cast (by omega : 1≤n+1)
  unfold theta48ScaledIntegralWeight
  rw [abs_div,abs_mul,abs_of_nonneg hh0,abs_of_nonneg (by linarith : (0:ℝ)≤(n+1:ℕ))]
  have hm : h*|1-(-1:ℝ)^(n+1)|≤1 := by nlinarith [abs_nonneg (1-(-1:ℝ)^(n+1))]
  exact (div_le_self (mul_nonneg hh0 (abs_nonneg _)) hn).trans hm

def theta48ApproxPanelValue (h : ℝ) (w : ℕ → ℕ → ℂ) : ℝ :=
  ∑ n ∈ Finset.range 40, theta48ScaledIntegralWeight h n*
    (2*(∑ k ∈ Finset.range 4, (w k n).re))

theorem theta48Panel_coefficient_error (c h epsilon : ℝ) (w : ℕ → ℕ → ℂ)
    (hc : 0<c) (hh0 : 0≤h) (hh1 : h≤1/2) (he : 0≤epsilon)
    (hw : ∀ k : ℕ, k<4 → ∀ n : ℕ, n<40 →
      ‖scaledPowerExpCoefficient (complexThetaExponent 48) (c:ℂ)
        (Real.pi*((k:ℝ)+1)^2) h n-w k n‖≤epsilon) :
    |theta48TaylorPanelValue c h 40-theta48ApproxPanelValue h w|≤320*epsilon := by
  rw [theta48TaylorPanelValue_scaled]
  unfold theta48ApproxPanelValue
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ n ∈ Finset.range 40, |theta48ScaledIntegralWeight h n*
        (theta48TaylorCoefficient c n*(h:ℂ)^n).re-
        theta48ScaledIntegralWeight h n*(2*∑ k ∈ Finset.range 4, (w k n).re)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Finset.range 40, 8*epsilon := by
      apply Finset.sum_le_sum
      intro n hn
      have hn40 : n<40 := Finset.mem_range.mp hn
      rw [← mul_sub,abs_mul,theta48TaylorCoefficient_scaled_atoms c h n hc]
      have hRe : (2*∑ k ∈ Finset.range 4,
          scaledPowerExpCoefficient (complexThetaExponent 48) (c:ℂ)
            (Real.pi*((k:ℝ)+1)^2) h n).re-
          2*∑ k ∈ Finset.range 4, (w k n).re=
          2*∑ k ∈ Finset.range 4,
            (scaledPowerExpCoefficient (complexThetaExponent 48) (c:ℂ)
              (Real.pi*((k:ℝ)+1)^2) h n-w k n).re := by
        norm_num [Complex.mul_re,Complex.re_sum,Complex.sub_re,Finset.sum_sub_distrib]
        <;> ring
      rw [hRe,abs_mul]
      have hsum : |∑ k ∈ Finset.range 4,
          (scaledPowerExpCoefficient (complexThetaExponent 48) (c:ℂ)
            (Real.pi*((k:ℝ)+1)^2) h n-w k n).re|≤4*epsilon := by
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        calc
          _ ≤ ∑ _k ∈ Finset.range 4, epsilon := by
            apply Finset.sum_le_sum
            intro k hk
            exact (Complex.abs_re_le_norm _).trans (hw k (Finset.mem_range.mp hk) n hn40)
          _ = _ := by simp
      have hweight := theta48ScaledIntegralWeight_abs_le_one h n hh0 hh1
      have hprod := mul_le_mul hweight hsum (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
      norm_num at hprod ⊢
      nlinarith
    _ = _ := by simp; ring

end ReciprocalXi
