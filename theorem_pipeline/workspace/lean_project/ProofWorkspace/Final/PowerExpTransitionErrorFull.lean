import ProofWorkspace.Final.PowerExpScaledTransitionFull
import ProofWorkspace.Final.SourcePiMidpointFull

set_option autoImplicit false
noncomputable section
namespace ReciprocalXi

theorem abs_mul_div_le_of_unit (x y d E : ℝ) (hx : |x|≤E)
    (hy0 : 0≤y) (hy1 : y≤1) (hd : 1≤d) : |x*y/d|≤E := by
  rw [abs_div, abs_mul, abs_of_nonneg hy0, abs_of_nonneg (by linarith : 0≤d)]
  have hm : |x| *y≤E := by
    have ht := mul_le_mul_of_nonneg_left hy1 (abs_nonneg x)
    linarith
  exact (div_le_self (mul_nonneg (abs_nonneg _) hy0) hd).trans hm

theorem powerExpScaledFirst_perturbation (s : ℂ) (c h lambda mu delta : ℝ)
    (hc : c≠0) (hh0 : 0≤h) (hh1 : h≤1) (hl : |lambda-mu|≤delta) :
    ‖powerExpScaledFirst s c h lambda-powerExpScaledFirst s c h mu‖≤delta := by
  rw [powerExpScaledFirst_sub _ _ _ _ _ hc]
  simpa only [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_neg, div_one] using
    abs_mul_div_le_of_unit (lambda-mu) h 1 delta hl hh0 hh1 (by norm_num)

theorem powerExpScaledA_perturbation (s : ℂ) (c h lambda mu delta : ℝ) (n : ℕ)
    (hc : c≠0) (hh0 : 0≤h) (hh1 : h≤1) (hl : |lambda-mu|≤delta) :
    ‖powerExpScaledA s c h lambda n-powerExpScaledA s c h mu n‖≤delta := by
  rw [powerExpScaledA_sub _ _ _ _ _ _ hc]
  simpa only [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_neg] using
    abs_mul_div_le_of_unit (lambda-mu) h (n+2:ℕ) delta hl hh0 hh1 (by
      exact_mod_cast (by omega : 1≤n+2))

theorem powerExpScaledB_perturbation (c h lambda mu delta : ℝ) (n : ℕ)
    (hc : 1≤c) (hh0 : 0≤h) (hh1 : h≤1) (hl : |lambda-mu|≤delta) :
    ‖powerExpScaledB c h lambda n-powerExpScaledB c h mu n‖≤delta := by
  rw [powerExpScaledB_sub]
  simpa only [Complex.norm_real, Real.norm_eq_abs] using
    abs_mul_div_le_of_unit (lambda-mu) (h^2) (c*(n+2:ℕ)) delta hl
      (sq_nonneg _) (by nlinarith) (by
        have hn : (1:ℝ)≤(n+2:ℕ) := by exact_mod_cast (by omega : 1≤n+2)
        nlinarith)

theorem theta48Lambda_midpoint_error (k : ℕ) (hk : k≤4) :
    |Real.pi*(k:ℝ)^2-(sourcePiMidpoint:ℝ)*(k:ℝ)^2|≤1/(10:ℝ)^140 := by
  have hp : |Real.pi-(sourcePiMidpoint:ℝ)|≤1/(10:ℝ)^150 := by
    simpa only [abs_sub_comm] using sourcePiMidpoint_error
  have hk0 : (0:ℝ)≤k := Nat.cast_nonneg k
  have hk4 : (k:ℝ)≤4 := by exact_mod_cast hk
  have hk2 : (k:ℝ)^2≤16 := by nlinarith
  have habs : |(k:ℝ)^2|=(k:ℝ)^2 := abs_of_nonneg (sq_nonneg (k:ℝ))
  rw [← sub_mul, abs_mul, habs]
  have hm := mul_le_mul hp hk2 (sq_nonneg (k:ℝ)) (by positivity : 0≤1/(10:ℝ)^150)
  apply hm.trans
  norm_num

end ReciprocalXi
