import ProofWorkspace.Final.RationalExpBoundsFull
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

noncomputable section
open scoped BigOperators
open MeasureTheory Set
namespace ReciprocalXi

def etaEulerWeight (N j : ℕ) : ℝ :=
  (∑ k ∈ (Finset.range (N + 1)).filter (fun k => j < k), (N.choose k : ℝ)) / 2 ^ N

def etaEulerPolynomial (N : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range N, (-1 : ℝ) ^ j * etaEulerWeight N j * x ^ (j + 1)

theorem etaEulerPolynomial_eq_binomial_sum (N : ℕ) (x : ℝ) :
    etaEulerPolynomial N x =
      (∑ k ∈ Finset.range (N + 1), (N.choose k : ℝ) *
        ∑ j ∈ Finset.range k, (-1 : ℝ) ^ j * x ^ (j + 1)) / 2 ^ N := by
  unfold etaEulerPolynomial etaEulerWeight
  simp_rw [Finset.sum_filter]
  simp only [← mul_div_assoc, div_mul_eq_mul_div, ← Finset.sum_div]
  congr 1
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  have hkN : k ≤ N := by have := Finset.mem_range.mp hk; omega
  have hfilter : (Finset.range N).filter (fun j => j < k) = Finset.range k := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [← hfilter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> ring

theorem etaEuler_geometric_identity (k : ℕ) (x : ℝ) (hx : x ≠ -1) :
    (∑ j ∈ Finset.range k, (-1 : ℝ) ^ j * x ^ (j + 1)) =
      x / (1 + x) * (1 - (-x) ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, pow_succ (-x), pow_succ x, ← neg_one_mul x,
      mul_pow]
    have hden : 1 + x ≠ 0 := by intro h; apply hx; linarith
    field_simp
    ring

theorem etaEulerPolynomial_identity (N : ℕ) (x : ℝ) (hx : x ≠ -1) :
    etaEulerPolynomial N x = x / (1 + x) * (1 - ((1 - x) / 2) ^ N) := by
  rw [etaEulerPolynomial_eq_binomial_sum]
  simp_rw [etaEuler_geometric_identity _ x hx]
  have hb : (∑ k ∈ Finset.range (N + 1), (N.choose k : ℝ) * (-x) ^ k) =
      (1 - x) ^ N := by
    have h := (add_pow (-x) (1 : ℝ) N).symm
    simpa only [one_pow, mul_one, mul_comm, neg_add_eq_sub] using h
  have hc : (∑ k ∈ Finset.range (N + 1), (N.choose k : ℝ)) = (2 : ℝ) ^ N := by
    exact_mod_cast Nat.sum_range_choose N
  calc
    _ = (x / (1 + x)) *
        ((∑ k ∈ Finset.range (N + 1), (N.choose k : ℝ)) -
         (∑ k ∈ Finset.range (N + 1), (N.choose k : ℝ) * (-x) ^ k)) / 2 ^ N := by
      rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = _ := by rw [hb, hc, div_pow]; field_simp

theorem etaEulerPolynomial_remainder (N : ℕ) (x : ℝ) (hx : x ≠ -1) :
    x / (1 + x) - etaEulerPolynomial N x =
      x / (1 + x) * ((1 - x) / 2) ^ N := by
  rw [etaEulerPolynomial_identity N x hx]
  ring

theorem etaEulerPolynomial_remainder_bounds (N : ℕ) (x : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ x / (1 + x) - etaEulerPolynomial N x ∧
    x / (1 + x) - etaEulerPolynomial N x ≤ x / 2 ^ N := by
  rw [etaEulerPolynomial_remainder N x (by linarith)]
  have hsub : 0 ≤ (1 - x) / 2 := by linarith
  have hfrac0 : 0 ≤ x / (1 + x) := div_nonneg hx0 (by linarith)
  constructor
  · exact mul_nonneg hfrac0 (pow_nonneg hsub N)
  · have hfrac : x / (1 + x) ≤ x := by
      exact (div_le_iff₀ (by positivity)).mpr (by nlinarith)
    have hp : ((1 - x) / 2) ^ N ≤ (1 / 2 : ℝ) ^ N :=
      pow_le_pow_left₀ hsub (by linarith) N
    calc
      _ ≤ x * (1 / 2 : ℝ) ^ N := mul_le_mul hfrac hp (pow_nonneg hsub N) hx0
      _ = _ := by rw [div_pow]; ring

theorem eta_euler_400_error_lt : (1 : ℝ) / 2 ^ 400 < 1 / 10 ^ 120 := by
  have h : ((10 : ℝ) ^ 3) ^ 40 < ((2 : ℝ) ^ 10) ^ 40 :=
    pow_lt_pow_left₀ (by norm_num) (by norm_num) (by norm_num)
  rw [← pow_mul, ← pow_mul] at h
  exact one_div_lt_one_div_of_lt (by positivity) h

theorem etaEulerPolynomial_nonneg (N : ℕ) (x : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : 0 ≤ etaEulerPolynomial N x := by
  rw [etaEulerPolynomial_identity N x (by linarith)]
  have hq0 : 0 ≤ (1 - x) / 2 := by linarith
  have hq1 : (1 - x) / 2 ≤ 1 := by linarith
  have hp : ((1 - x) / 2) ^ N ≤ 1 := by
    simpa using pow_le_pow_left₀ hq0 hq1 N
  exact mul_nonneg (by positivity) (sub_nonneg.mpr hp)

theorem etaEulerPolynomial_le (N : ℕ) (x : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : etaEulerPolynomial N x ≤ x := by
  have h := (etaEulerPolynomial_remainder_bounds N x hx0 hx1).1
  have hf : x / (1 + x) ≤ x := (div_le_iff₀ (by positivity)).mpr (by nlinarith)
  linarith

theorem continuous_etaEulerPolynomial (N : ℕ) : Continuous (etaEulerPolynomial N) := by
  unfold etaEulerPolynomial
  fun_prop

def etaEulerIntegrand (N : ℕ) (s t : ℝ) : ℝ :=
  t ^ (s - 1) * etaEulerPolynomial N (Real.exp (-t))

theorem etaEulerIntegrand_bounds (N : ℕ) (s t : ℝ) (ht : 0 < t) :
    0 ≤ etaEulerIntegrand N s t ∧
    etaEulerIntegrand N s t ≤ Real.exp (-t) * t ^ (s - 1) := by
  have hx0 : 0 ≤ Real.exp (-t) := (Real.exp_pos _).le
  have hx1 : Real.exp (-t) ≤ 1 := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (by linarith : -t ≤ 0)
  have hr : 0 ≤ t ^ (s - 1) := Real.rpow_nonneg ht.le _
  constructor
  · exact mul_nonneg hr (etaEulerPolynomial_nonneg N _ hx0 hx1)
  · exact (mul_le_mul_of_nonneg_left (etaEulerPolynomial_le N _ hx0 hx1) hr).trans_eq
      (mul_comm _ _)

theorem integrableOn_etaEulerIntegrand (N : ℕ) (s : ℝ) (hs : 0 < s) :
    IntegrableOn (etaEulerIntegrand N s) (Ioi 0) := by
  have hc : ContinuousOn (etaEulerIntegrand N s) (Ioi 0) := by
    exact (continuousOn_id.rpow_const (by intro t ht; exact Or.inl (ne_of_gt ht))).mul
      ((continuous_etaEulerPolynomial N).comp continuous_neg.rexp).continuousOn
  refine (Real.GammaIntegral_convergent hs).mono'
    (hc.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (etaEulerIntegrand_bounds N s t ht).1]
  exact (etaEulerIntegrand_bounds N s t ht).2

theorem etaEulerIntegrand_remainder_bounds (N : ℕ) (s t : ℝ) (ht : 0 < t) :
    0 ≤ t ^ (s - 1) * Real.exp (-t) / (1 + Real.exp (-t)) - etaEulerIntegrand N s t ∧
    t ^ (s - 1) * Real.exp (-t) / (1 + Real.exp (-t)) - etaEulerIntegrand N s t ≤
      (Real.exp (-t) * t ^ (s - 1)) / 2 ^ N := by
  have hx0 := (Real.exp_pos (-t)).le
  have hx1 : Real.exp (-t) ≤ 1 := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (by linarith : -t ≤ 0)
  have hr := Real.rpow_nonneg ht.le (s - 1)
  have h := etaEulerPolynomial_remainder_bounds N (Real.exp (-t)) hx0 hx1
  have he : t ^ (s - 1) * Real.exp (-t) / (1 + Real.exp (-t)) - etaEulerIntegrand N s t =
      t ^ (s - 1) * (Real.exp (-t) / (1 + Real.exp (-t)) -
        etaEulerPolynomial N (Real.exp (-t))) := by unfold etaEulerIntegrand; ring
  rw [he]
  constructor
  · exact mul_nonneg hr h.1
  · convert mul_le_mul_of_nonneg_left h.2 hr using 1
    ring

end ReciprocalXi

