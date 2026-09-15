import ProofWorkspace.Final.GammaVerticalBoundsFull
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import ProofWorkspace.Final.EtaIntegralFull

noncomputable section
open Filter
open scoped BigOperators
namespace ReciprocalXi

def gammaLogCorrection (z : ℝ) (n : ℕ) : ℝ :=
  2 * z * Real.log (1 + (1 / 2 : ℝ) / ((n : ℝ) + 1)) -
    Real.log (1 + z / ((n : ℝ) + 1))

theorem gammaLogCorrection_eq (z : ℝ) (hz : -1 < z) (n : ℕ) :
    gammaLogCorrection z n =
      2 * z * Real.log (3 / 2 + (n : ℝ)) - Real.log (1 + z + (n : ℝ)) +
        (1 - 2 * z) * Real.log (1 + (n : ℝ)) := by
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hz' : 0 < 1 + z + (n : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have h1 : 1 + (1 / 2 : ℝ) / ((n : ℝ) + 1) = (3 / 2 + (n : ℝ)) / ((n : ℝ) + 1) := by
    field_simp; ring
  have h2 : 1 + z / ((n : ℝ) + 1) = (1 + z + (n : ℝ)) / ((n : ℝ) + 1) := by
    field_simp; ring
  unfold gammaLogCorrection
  rw [h1, h2, Real.log_div (by positivity) (ne_of_gt hn),
    Real.log_div (ne_of_gt hz') (ne_of_gt hn)]
  rw [add_comm (1 : ℝ) (n : ℝ)]
  ring

theorem gammaLogCorrection_sum (z : ℝ) (hz : -1 < z) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), gammaLogCorrection z n) =
      Real.BohrMollerup.logGammaSeq (1 + z) N -
      2 * z * Real.BohrMollerup.logGammaSeq (3 / 2) N -
      (1 - 2 * z) * Real.BohrMollerup.logGammaSeq 1 N := by
  simp_rw [gammaLogCorrection_eq z hz]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Real.BohrMollerup.logGammaSeq]
  ring

theorem tendsto_gammaLogCorrection_sum (z : ℝ) (hz : -1 < z) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (N + 1), gammaLogCorrection z n)
      atTop (nhds (Real.log (Real.Gamma (1 + z)) - 2 * z * Real.log (Real.Gamma (3 / 2)))) := by
  simp_rw [gammaLogCorrection_sum z hz]
  have h1 := Real.BohrMollerup.tendsto_log_gamma (by linarith : 0 < 1 + z)
  have h2 := Real.BohrMollerup.tendsto_log_gamma (by norm_num : (0 : ℝ) < 3 / 2)
  have h3 := Real.BohrMollerup.tendsto_log_gamma (by norm_num : (0 : ℝ) < 1)
  simpa using (h1.sub (h2.const_mul (2 * z))).sub (h3.const_mul (1 - 2 * z))

def gammaLogTaylorCoefficient (z : ℝ) (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k * (z ^ (k + 2) - 2 * z * (1 / 2 : ℝ) ^ (k + 2)) / (k + 2)

def gammaLogCorrectionTaylor (z : ℝ) (N n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, gammaLogTaylorCoefficient z k / ((n : ℝ) + 1) ^ (k + 2)

theorem gamma_log_taylor_remainder_bound (y d : ℝ) (N : ℕ)
    (hy : |y| ≤ 1 / 2) (hd : 1 ≤ d) :
    |Real.log (1 + y / d) +
      ∑ i ∈ Finset.range (N + 1), (-y / d) ^ (i + 1) / (i + 1)| ≤
      2 * (1 / 2 : ℝ) ^ (N + 2) / d ^ 2 := by
  have hd0 : 0 < d := by linarith
  have hx : |-y / d| ≤ (1 / 2 : ℝ) / d := by
    rw [abs_div, abs_neg, abs_of_pos hd0]
    exact div_le_div_of_nonneg_right hy hd0.le
  have hx2 : |-y / d| ≤ 1 / 2 := hx.trans (by
    apply (div_le_iff₀ hd0).mpr
    linarith)
  have h := Real.abs_log_sub_add_sum_range_le (lt_of_le_of_lt hx2 (by norm_num)) (N + 1)
  have heq : (1 : ℝ) - -y / d = 1 + y / d := by ring
  rw [heq, add_comm] at h
  apply h.trans
  have hpow : d ^ 2 ≤ d ^ (N + 2) := by
    rw [pow_add]
    have hn : (1 : ℝ) ≤ d ^ N := one_le_pow₀ hd
    nlinarith [sq_nonneg d]
  calc
    _ ≤ ((1 / 2 : ℝ) / d) ^ (N + 2) / (1 / 2) :=
      div_le_div₀ (by positivity)
        (pow_le_pow_left₀ (abs_nonneg _) hx (N + 2)) (by norm_num) (by linarith)
    _ = 2 * ((1 / 2 : ℝ) ^ (N + 2) / d ^ (N + 2)) := by rw [div_pow]; ring
    _ ≤ 2 * ((1 / 2 : ℝ) ^ (N + 2) / d ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact div_le_div₀ (by positivity) (le_refl _) (by positivity) hpow
    _ = _ := by ring

theorem gammaLogCorrectionTaylor_eq (z : ℝ) (N n : ℕ) :
    gammaLogCorrectionTaylor z N n =
      (∑ i ∈ Finset.range (N + 1), (-z / ((n : ℝ) + 1)) ^ (i + 1) / (i + 1)) -
      2 * z * (∑ i ∈ Finset.range (N + 1), (-(1 / 2 : ℝ) / ((n : ℝ) + 1)) ^ (i + 1) / (i + 1)) := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_range_succ']
  simp only [pow_one, Nat.cast_zero, zero_add, div_one]
  have hz0 : -z / ((n : ℝ) + 1) - 2 * z * (-(1 / 2 : ℝ) / ((n : ℝ) + 1)) = 0 := by ring
  rw [hz0, add_zero]
  unfold gammaLogCorrectionTaylor
  apply Finset.sum_congr rfl
  intro k hk
  unfold gammaLogTaylorCoefficient
  rw [show k + 1 + 1 = k + 2 by omega]
  simp only [div_pow]
  rw [neg_pow z, neg_pow (1 / 2 : ℝ)]
  simp only [pow_add (-1 : ℝ) k 2]
  norm_num only [neg_one_sq, mul_one]
  push_cast
  simp only [one_div]
  ring_nf
  norm_num
  ring

theorem gammaLogCorrection_error_bound (z : ℝ) (N n : ℕ) (hz : |z| ≤ 1 / 2) :
    |gammaLogCorrection z n - gammaLogCorrectionTaylor z N n| ≤
      4 * (1 / 2 : ℝ) ^ (N + 2) / ((n : ℝ) + 1) ^ 2 := by
  have hd : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hzerr := gamma_log_taylor_remainder_bound z ((n : ℝ) + 1) N hz hd
  have hherr := gamma_log_taylor_remainder_bound (1 / 2) ((n : ℝ) + 1) N (by norm_num) hd
  have h2z : |2 * z| ≤ 1 := by rw [abs_mul]; norm_num; linarith
  rw [gammaLogCorrectionTaylor_eq]
  unfold gammaLogCorrection
  have hid :
      2 * z * Real.log (1 + (1 / 2 : ℝ) / ((n : ℝ) + 1)) - Real.log (1 + z / ((n : ℝ) + 1)) -
      ((∑ i ∈ Finset.range (N + 1), (-z / ((n : ℝ) + 1)) ^ (i + 1) / (i + 1)) -
      2 * z * (∑ i ∈ Finset.range (N + 1), (-(1 / 2 : ℝ) / ((n : ℝ) + 1)) ^ (i + 1) / (i + 1))) =
      (2 * z) * (Real.log (1 + (1 / 2 : ℝ) / ((n : ℝ) + 1)) +
        ∑ i ∈ Finset.range (N + 1), (-(1 / 2 : ℝ) / ((n : ℝ) + 1)) ^ (i + 1) / (i + 1)) -
      (Real.log (1 + z / ((n : ℝ) + 1)) +
        ∑ i ∈ Finset.range (N + 1), (-z / ((n : ℝ) + 1)) ^ (i + 1) / (i + 1)) := by ring
  rw [hid]
  rw [sub_eq_add_neg]
  apply (abs_add_le _ _).trans
  rw [abs_neg, abs_mul]
  have hm := mul_le_mul h2z hherr (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  push_cast at hzerr hherr hm ⊢
  simp only [one_div] at hzerr hherr hm ⊢
  convert add_le_add hm hzerr using 1
  ring

theorem gammaLogCorrection_sum_error_bound (z : ℝ) (N M : ℕ) (hz : |z| ≤ 1 / 2) :
    |(∑ n ∈ Finset.range (M + 1), gammaLogCorrection z n) -
      ∑ n ∈ Finset.range (M + 1), gammaLogCorrectionTaylor z N n| ≤
      8 * (1 / 2 : ℝ) ^ (N + 2) := by
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply (Finset.sum_le_sum (fun n _ => gammaLogCorrection_error_bound z N n hz)).trans
  have hs := sum_shifted_inv_sq_le_two 1 (by norm_num) (M + 1)
  have he : (∑ n ∈ Finset.range (M + 1), 4 * (1 / 2 : ℝ) ^ (N + 2) / ((n : ℝ) + 1) ^ 2) =
      (4 * (1 / 2 : ℝ) ^ (N + 2)) * ∑ n ∈ Finset.range (M + 1), ((1 + (n : ℝ)) ^ 2)⁻¹ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [add_comm (n : ℝ) 1]
    ring
  rw [he]
  convert mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 4 * (1 / 2 : ℝ) ^ (N + 2)) using 1
  ring

theorem hasSum_reciprocal_nat_power_zeta (k : ℕ) (hk : 2 ≤ k) :
    HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ k) (riemannZeta (k : ℂ)).re := by
  have hkR : (1 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 1 < k)
  have hs : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (k : ℝ)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_rpow.mpr hkR)
  have h := hs.hasSum
  rw [← riemannZeta_re_eq_tsum_rpow (k : ℝ) hkR] at h
  simpa only [Real.rpow_natCast, Complex.ofReal_natCast] using h

def gammaLogSeriesApprox (z : ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, gammaLogTaylorCoefficient z k * (riemannZeta ((k + 2 : ℕ) : ℂ)).re

theorem tendsto_gammaLogCorrectionTaylor_sum (z : ℝ) (N : ℕ) :
    Tendsto (fun M : ℕ => ∑ n ∈ Finset.range (M + 1), gammaLogCorrectionTaylor z N n)
      atTop (nhds (gammaLogSeriesApprox z N)) := by
  have he (M : ℕ) : (∑ n ∈ Finset.range (M + 1), gammaLogCorrectionTaylor z N n) =
      ∑ k ∈ Finset.range N, gammaLogTaylorCoefficient z k *
        ∑ n ∈ Finset.range (M + 1), 1 / ((n : ℝ) + 1) ^ (k + 2) := by
    unfold gammaLogCorrectionTaylor
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  simp_rw [he]
  apply tendsto_finset_sum
  intro k hk
  apply Filter.Tendsto.const_mul
  exact (hasSum_reciprocal_nat_power_zeta (k + 2) (by omega)).tendsto_sum_nat.comp
    (tendsto_add_atTop_nat 1)

theorem logGamma_series_error_bound (z : ℝ) (N : ℕ) (hz : |z| ≤ 1 / 2) :
    |Real.log (Real.Gamma (1 + z)) - 2 * z * Real.log (Real.Gamma (3 / 2)) -
      gammaLogSeriesApprox z N| ≤ 8 * (1 / 2 : ℝ) ^ (N + 2) := by
  have hz1 : -1 < z := by have := (abs_le.mp hz).1; linarith
  have hlim := ((tendsto_gammaLogCorrection_sum z hz1).sub
    (tendsto_gammaLogCorrectionTaylor_sum z N)).abs
  exact le_of_tendsto hlim (Filter.Eventually.of_forall
    (fun M => gammaLogCorrection_sum_error_bound z N M hz))

theorem logGamma_three_halves :
    Real.log (Real.Gamma (3 / 2)) = Real.log Real.pi / 2 - Real.log 2 := by
  have hg : Real.Gamma (3 / 2) = Real.sqrt Real.pi / 2 := by
    have h := Real.Gamma_add_one (s := (1 / 2 : ℝ)) (by norm_num)
    norm_num only at h
    rw [Real.Gamma_one_half_eq] at h
    convert h using 1
    ring
  rw [hg, Real.log_div (by positivity) (by norm_num), Real.log_sqrt Real.pi_pos.le]

def logGammaApprox (z : ℝ) (N : ℕ) : ℝ :=
  z * Real.log Real.pi - 2 * z * Real.log 2 + gammaLogSeriesApprox z N

theorem logGamma_approx_error_bound (z : ℝ) (N : ℕ) (hz : |z| ≤ 1 / 2) :
    |Real.log (Real.Gamma (1 + z)) - logGammaApprox z N| ≤
      8 * (1 / 2 : ℝ) ^ (N + 2) := by
  have h := logGamma_series_error_bound z N hz
  rw [logGamma_three_halves] at h
  convert h using 1
  congr 1
  unfold logGammaApprox
  ring

set_option maxRecDepth 4096 in
theorem gamma_series_440_error_lt : 8 * (1 / 2 : ℝ) ^ (440 + 2) < 1 / 10 ^ 130 := by
  have h : ((10 : ℝ) ^ 3) ^ 43 < ((2 : ℝ) ^ 10) ^ 43 :=
    pow_lt_pow_left₀ (by norm_num) (by norm_num) (by norm_num)
  rw [← pow_mul, ← pow_mul] at h
  have hm := mul_lt_mul_of_pos_right h (by norm_num : (0 : ℝ) < 10)
  have hm2 := mul_lt_mul_of_pos_left (by norm_num : (10 : ℝ) < 2 ^ 9)
    (by positivity : (0 : ℝ) < 2 ^ (10 * 43))
  have hp : (10 : ℝ) ^ 130 < 2 ^ 439 := by
    have ht := hm.trans hm2
    change (10 : ℝ) ^ 129 * 10 < 2 ^ 430 * 2 ^ 9 at ht
    rw [← pow_succ (10 : ℝ) 129, ← pow_add (2 : ℝ) 430 9] at ht
    exact ht
  have hinv := one_div_lt_one_div_of_lt (by positivity : (0 : ℝ) < 10 ^ 130) hp
  apply lt_of_eq_of_lt _ hinv
  rw [div_pow, one_pow]
  have he : (2 : ℝ) ^ 442 = 2 ^ 439 * 8 := by
    calc
      _ = (2 : ℝ) ^ (439 + 3) := by rfl
      _ = _ := by rw [pow_add]; norm_num
  rw [he]
  field_simp

theorem logGamma_approx_440_error (z : ℝ) (hz : |z| ≤ 1 / 2) :
    |Real.log (Real.Gamma (1 + z)) - logGammaApprox z 440| < 1 / 10 ^ 130 :=
  (logGamma_approx_error_bound z 440 hz).trans_lt gamma_series_440_error_lt

end ReciprocalXi

