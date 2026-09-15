import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.PSeries
import Mathlib.Tactic

/-!
# A vertical lower bound for the actual Gamma function

The bound is derived from finite Euler approximants and their proved limit,
not from an assumed infinite-product representation.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace ReciprocalXi

/-- The finite shifted reciprocal-square sum is bounded uniformly in its
length, throughout the real half-line x≥1. -/
theorem sum_shifted_inv_sq_le_two (x : ℝ) (hx : 1 ≤ x) (n : ℕ) :
    (∑ k ∈ Finset.range n, ((x + (k : ℝ)) ^ 2)⁻¹) ≤ 2 := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hbase := sum_Ioo_inv_sq_le (α := ℝ) 0 (n + 1)
  have hset : Finset.Ioo 0 (n + 1) = Finset.Ico 1 (n + 1) := by
    ext k
    simp only [Finset.mem_Ioo, Finset.mem_Ico]
    omega
  rw [hset, Finset.sum_Ico_eq_sum_range] at hbase
  have hbase' : (∑ k ∈ Finset.range n, (((k : ℝ) + 1) ^ 2)⁻¹) ≤ 2 := by
    simpa only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, Nat.cast_zero,
      zero_add, div_one, add_comm] using hbase
  apply le_trans (Finset.sum_le_sum (fun k _ => ?_)) hbase'
  apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
  apply (sq_le_sq₀ (by positivity) (by positivity)).mpr
  linarith

/-- A single complex denominator factor, with the crucial one-half in the
exponent obtained by comparing squared norms. -/
theorem norm_vertical_factor_le (s t : ℝ) (hs : 0 < s) :
    ‖(s : ℂ) + (t : ℂ) * Complex.I‖ ≤
      s * Real.exp (t ^ 2 / (2 * s ^ 2)) := by
  have hnorm : ‖(s : ℂ) + (t : ℂ) * Complex.I‖ ^ 2 = s ^ 2 + t ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, pow_two]
  have he := Real.add_one_le_exp (t ^ 2 / s ^ 2)
  have hpow : (Real.exp (t ^ 2 / (2 * s ^ 2))) ^ 2 = Real.exp (t ^ 2 / s ^ 2) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hs.le (Real.exp_pos _).le)).mp
  rw [hnorm, mul_pow, hpow]
  have h := mul_le_mul_of_nonneg_left he (sq_nonneg s)
  have heq : s ^ 2 * (t ^ 2 / s ^ 2 + 1) = s ^ 2 + t ^ 2 := by
    field_simp
    ring
  rwa [heq] at h

/-- Finite Euler-product denominator comparison, uniform in the truncation. -/
theorem prod_norm_vertical_factor_le (x t : ℝ) (hx : 1 ≤ x) (n : ℕ) :
    (∏ k ∈ Finset.range n, ‖(x : ℂ) + (t : ℂ) * Complex.I + (k : ℂ)‖) ≤
      (∏ k ∈ Finset.range n, (x + (k : ℝ))) * Real.exp (t ^ 2) := by
  have hprod : (∏ k ∈ Finset.range n, ‖(x : ℂ) + (t : ℂ) * Complex.I + (k : ℂ)‖) ≤
      ∏ k ∈ Finset.range n, (x + (k : ℝ)) * Real.exp (t ^ 2 / (2 * (x + k) ^ 2)) := by
    apply Finset.prod_le_prod (fun k _ => norm_nonneg _)
    intro k _
    have heq : (x : ℂ) + (t : ℂ) * Complex.I + (k : ℂ) =
        ((x + k : ℝ) : ℂ) + (t : ℂ) * Complex.I := by
      push_cast
      ring
    rw [heq]
    exact norm_vertical_factor_le (x + k) t (by positivity)
  rw [Finset.prod_mul_distrib, ← Real.exp_sum] at hprod
  apply hprod.trans
  apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg (fun k _ => by positivity))
  apply Real.exp_le_exp.mpr
  have hsum := mul_le_mul_of_nonneg_left (sum_shifted_inv_sq_le_two x hx n)
    (show 0 ≤ t ^ 2 / 2 by positivity)
  have heq : (∑ k ∈ Finset.range n, t ^ 2 / (2 * (x + k) ^ 2)) =
      (t ^ 2 / 2) * ∑ k ∈ Finset.range n, ((x + (k : ℝ)) ^ 2)⁻¹ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    field_simp
  rw [heq]
  linarith

theorem norm_GammaSeq_vertical_eq (x t : ℝ) (n : ℕ) (hn : 0 < n) :
    ‖Complex.GammaSeq ((x : ℂ) + (t : ℂ) * Complex.I) n‖ =
      ((n : ℝ) ^ x * (n.factorial : ℝ)) /
        ∏ k ∈ Finset.range (n + 1), ‖(x : ℂ) + (t : ℂ) * Complex.I + (k : ℂ)‖ := by
  simp only [Complex.GammaSeq, norm_div, norm_mul, norm_prod,
    Complex.norm_natCast_cpow_of_pos hn, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, zero_mul, sub_zero, add_zero, Complex.norm_natCast]

/-- Every nonzero-index Euler approximant satisfies the required lower bound. -/
theorem GammaSeq_vertical_lower_bound (x t : ℝ) (hx : 1 ≤ x)
    (n : ℕ) (hn : 0 < n) :
    Real.GammaSeq x n * Real.exp (-(t ^ 2)) ≤
      ‖Complex.GammaSeq ((x : ℂ) + (t : ℂ) * Complex.I) n‖ := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hP := prod_norm_vertical_factor_le x t hx (n + 1)
  have hreal : 0 < ∏ k ∈ Finset.range (n + 1), (x + (k : ℝ)) :=
    Finset.prod_pos (fun k _ => by positivity)
  have hcomplex : 0 < ∏ k ∈ Finset.range (n + 1),
      ‖(x : ℂ) + (t : ℂ) * Complex.I + (k : ℂ)‖ := by
    apply Finset.prod_pos
    intro k _
    apply norm_pos_iff.mpr
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.natCast_re,
      Complex.zero_re, mul_zero, zero_mul, sub_zero, add_zero] at hr
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hnum : 0 ≤ (n : ℝ) ^ x * (n.factorial : ℝ) := by positivity
  rw [Real.GammaSeq, norm_GammaSeq_vertical_eq x t n hn]
  calc
    (n : ℝ) ^ x * (n.factorial : ℝ) /
        (∏ k ∈ Finset.range (n + 1), (x + (k : ℝ))) * Real.exp (-(t ^ 2)) =
        ((n : ℝ) ^ x * (n.factorial : ℝ)) /
          ((∏ k ∈ Finset.range (n + 1), (x + (k : ℝ))) * Real.exp (t ^ 2)) := by
      rw [Real.exp_neg]
      ring
    _ ≤ _ := div_le_div_of_nonneg_left hnum hcomplex hP

/-- A vertical lower bound for the actual Gamma function, obtained by passing
the finite Euler-approximant inequality to its known limit. -/
theorem gamma_vertical_lower_bound (x t : ℝ) (hx : 1 ≤ x) :
    Real.Gamma x * Real.exp (-(t ^ 2)) ≤
      ‖Complex.Gamma ((x : ℂ) + (t : ℂ) * Complex.I)‖ := by
  apply le_of_tendsto_of_tendsto
    ((Real.GammaSeq_tendsto_Gamma x).mul_const (Real.exp (-(t ^ 2))))
    ((Complex.GammaSeq_tendsto_Gamma ((x : ℂ) + (t : ℂ) * Complex.I)).norm)
  filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with n hn
  exact GammaSeq_vertical_lower_bound x t hx n hn

/-- Equivalent ratio form for controlling reciprocal Gamma factors. -/
theorem gamma_vertical_ratio_le_exp (x t : ℝ) (hx : 1 ≤ x) :
    Real.Gamma x / ‖Complex.Gamma ((x : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      Real.exp (t ^ 2) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hg := Real.Gamma_pos_of_pos hx0
  have h := gamma_vertical_lower_bound x t hx
  have hn : 0 < ‖Complex.Gamma ((x : ℂ) + (t : ℂ) * Complex.I)‖ :=
    lt_of_lt_of_le (mul_pos hg (Real.exp_pos _)) h
  apply (div_le_iff₀ hn).mpr
  have hmul := mul_le_mul_of_nonneg_right h (Real.exp_pos (t ^ 2)).le
  have he : Real.exp (-(t ^ 2)) * Real.exp (t ^ 2) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  calc
    Real.Gamma x = (Real.Gamma x * Real.exp (-(t ^ 2))) * Real.exp (t ^ 2) := by
      rw [mul_assoc, he, mul_one]
    _ ≤ _ := hmul
    _ = _ := mul_comm _ _

end ReciprocalXi

end
