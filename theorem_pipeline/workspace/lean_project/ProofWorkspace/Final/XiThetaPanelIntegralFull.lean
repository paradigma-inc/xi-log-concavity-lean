import ProofWorkspace.Final.XiThetaTaylorFull
import ProofWorkspace.Final.XiThetaFiniteIntegralFull
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
namespace ReciprocalXi

def realTheta48TaylorPolynomial (c : ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, (theta48TaylorCoefficient c n).re*(t-c)^n

def theta48TaylorPanelValue (c h : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, (theta48TaylorCoefficient c n).re*
    ((h^(n+1)-(-h)^(n+1))/(n+1:ℕ))

theorem realTheta48TaylorPolynomial_eq_re (c t : ℝ) (N : ℕ) :
    realTheta48TaylorPolynomial c N t=(theta48TaylorPolynomial c N (t:ℂ)).re := by
  unfold realTheta48TaylorPolynomial theta48TaylorPolynomial
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Complex.mul_re]
  simp only [← Complex.ofReal_sub, ← Complex.ofReal_pow, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]

theorem continuous_realTheta48TaylorPolynomial (c : ℝ) (N : ℕ) :
    Continuous (realTheta48TaylorPolynomial c N) := by
  unfold realTheta48TaylorPolynomial
  fun_prop

theorem integral_realTheta48TaylorPolynomial (c h : ℝ) (N : ℕ) :
    (∫ t : ℝ in (c-h)..(c+h), realTheta48TaylorPolynomial c N t)=
      theta48TaylorPanelValue c h N := by
  unfold realTheta48TaylorPolynomial theta48TaylorPanelValue
  rw [intervalIntegral.integral_finset_sum (fun n hn ↦
    (show Continuous (fun t : ℝ ↦ (theta48TaylorCoefficient c n).re*(t-c)^n) by fun_prop).intervalIntegrable _ _)]
  apply Finset.sum_congr rfl
  intro n hn
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_right (fun t : ℝ ↦ t^n), integral_pow]
  congr 2 <;> push_cast <;> ring

theorem realTheta48Taylor40_error (c h t : ℝ) (hc : 1≤c)
    (hh : h≤c/16) (ht : t∈Icc (c-h) (c+h)) :
    |realThetaFiniteIntegrand 48 4 t-realTheta48TaylorPolynomial c 40 t|≤1/(10:ℝ)^22 := by
  have ht0 : 0<t := by linarith [ht.1]
  have hz : ‖(t:ℂ)-(c:ℂ)‖≤c/16 := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have he := (Complex.abs_re_le_norm
    (complexThetaFiniteIntegrand 48 4 (t:ℂ)-theta48TaylorPolynomial c 40 (t:ℂ))).trans
      (theta48Taylor40_remainder_le c t hc hz)
  simpa only [Complex.sub_re, complexThetaFiniteIntegrand_re 48 t 4 ht0,
    ← realTheta48TaylorPolynomial_eq_re] using he

theorem realTheta48Taylor40_panel_error (c h : ℝ) (hc : 1≤c)
    (hh0 : 0≤h) (hh : h≤c/16) :
    |(∫ t : ℝ in (c-h)..(c+h), realThetaFiniteIntegrand 48 4 t)-
      theta48TaylorPanelValue c h 40|≤2*h/(10:ℝ)^22 := by
  have hab : c-h≤c+h := by linarith
  have hi : IntervalIntegrable (realThetaFiniteIntegrand 48 4) volume (c-h) (c+h) :=
    ((continuousOn_realThetaFiniteIntegrand 48 4).mono
      (show Icc (c-h) (c+h)⊆Ioi 0 from fun t ht ↦ by
        change 0<t
        linarith [ht.1])).intervalIntegrable_of_Icc hab
  have hj : IntervalIntegrable (realTheta48TaylorPolynomial c 40) volume (c-h) (c+h) :=
    (continuous_realTheta48TaylorPolynomial c 40).intervalIntegrable (c-h) (c+h)
  rw [← integral_realTheta48TaylorPolynomial, ← intervalIntegral.integral_sub hi hj]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a:=c-h) (b:=c+h) (C:=1/(10:ℝ)^22)
    (f:=fun t ↦ realThetaFiniteIntegrand 48 4 t-realTheta48TaylorPolynomial c 40 t) (by
      intro t ht
      rw [uIoc_of_le hab] at ht
      simpa only [Real.norm_eq_abs] using realTheta48Taylor40_error c h t hc hh ⟨ht.1.le,ht.2⟩)
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : 0≤(c+h)-(c-h))] at hb
  convert hb using 1 <;> ring

end ReciprocalXi
