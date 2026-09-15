import ProofWorkspace.Final.FastGammaBoundsFull
import Mathlib.Analysis.PSeries

/-!
# Uniform bounds for rounded log-Gamma evaluation

Both Fast log-Gamma endpoints have absolute value at most 32 when the
centered offset has absolute value at most 1/2 and each truncation order
is at most the positive rounding scale. This discharges the scaled
exponential range checks uniformly, without evaluating endpoint tables.
-/

set_option autoImplicit false

namespace ReciprocalXi

theorem ratRound_abs_le (q : ℚ) (B : ℕ) (hB : 0 < B) :
    |ratRoundLower q B| ≤ |q| + 1/(B:ℚ) ∧
      |ratRoundUpper q B| ≤ |q| + 1/(B:ℚ) := by
  have he := ratRound_enclosure q B hB
  have hw := ratRound_width_le q B hB
  have hbp : (0:ℚ) < B := by exact_mod_cast hB
  have hi : (0:ℚ) ≤ 1/(B:ℚ) := by positivity
  have hq0 := neg_abs_le q
  have hq1 := le_abs_self q
  constructor <;> rw [abs_le] <;> constructor <;> linarith

theorem ratEtaEulerWeight_bounds (M j : ℕ) :
    0 ≤ ratEtaEulerWeight M j ∧ ratEtaEulerWeight M j ≤ 1 := by
  have hp : (0:ℚ) < 2^M := by positivity
  unfold ratEtaEulerWeight
  constructor
  · positivity
  · apply (div_le_iff₀ hp).mpr
    have hs : (∑ n ∈ (Finset.range (M+1)).filter (fun n => j < n),
        (M.choose n : ℚ)) ≤ ∑ n ∈ Finset.range (M+1), (M.choose n : ℚ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro n hn hn'
      positivity
    have he : (∑ n ∈ Finset.range (M+1), (M.choose n : ℚ)) = 2^M := by
      exact_mod_cast Nat.sum_range_choose M
    simpa [he] using hs

theorem ratEtaIntegerTerm_abs_le (M k j : ℕ) (hk : 2 ≤ k) :
    |ratEtaIntegerTerm M k j| ≤ (((j:ℚ)+1)^2)⁻¹ := by
  have hw := ratEtaEulerWeight_bounds M j
  have hj : (1:ℚ) ≤ (j:ℚ)+1 := by have := (Nat.cast_nonneg j : (0:ℚ) ≤ j); linarith
  have hpow : ((j:ℚ)+1)^2 ≤ ((j:ℚ)+1)^k := pow_le_pow_right₀ hj hk
  unfold ratEtaIntegerTerm
  rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg hw.1, abs_of_nonneg (by positivity : (0:ℚ) ≤ ((j:ℚ)+1)^k)]
  calc
    _ ≤ 1 / ((j:ℚ)+1)^k := div_le_div_of_nonneg_right hw.2 (by positivity)
    _ ≤ 1 / ((j:ℚ)+1)^2 := div_le_div_of_nonneg_left (by norm_num) (by positivity) hpow
    _ = _ := one_div _

theorem ratSum_shifted_inv_sq_le_two (M : ℕ) :
    (∑ j ∈ Finset.range M, (((j:ℚ)+1)^2)⁻¹) ≤ 2 := by
  have h := sum_Ioo_inv_sq_le (α := ℚ) 0 (M+1)
  have he : Finset.Ioo 0 (M+1) = Finset.Ico 1 (M+1) := by
    ext j
    simp only [Finset.mem_Ioo, Finset.mem_Ico]
    omega
  rw [he, Finset.sum_Ico_eq_sum_range] at h
  simpa only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, Nat.cast_zero,
    zero_add, div_one, add_comm] using h

theorem ratEtaIntegerRounded_abs_le_three (M k B : ℕ)
    (hk : 2 ≤ k) (hB : 0 < B) (hM : M ≤ B) :
    |ratEtaIntegerRoundedLower M k B| ≤ 3 ∧
      |ratEtaIntegerRoundedUpper M k B| ≤ 3 := by
  have hbp : (0:ℚ) < B := by exact_mod_cast hB
  have hm : (M:ℚ)/B ≤ 1 := (div_le_one hbp).mpr (by exact_mod_cast hM)
  have hb (j : ℕ) := ratEtaIntegerTerm_abs_le M k j hk
  have hsum : (∑ j ∈ Finset.range M,
      (|ratEtaIntegerTerm M k j|+1/(B:ℚ))) ≤ 3 := by
    rw [Finset.sum_add_distrib]
    have hs := (Finset.sum_le_sum (fun j _ => hb j)).trans (ratSum_shifted_inv_sq_le_two M)
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [← div_eq_mul_one_div]
    linarith
  constructor
  · apply (Finset.abs_sum_le_sum_abs _ _).trans
    exact (Finset.sum_le_sum (fun j _ => (ratRound_abs_le _ B hB).1)).trans hsum
  · apply (Finset.abs_sum_le_sum_abs _ _).trans
    exact (Finset.sum_le_sum (fun j _ => (ratRound_abs_le _ B hB).2)).trans hsum

theorem ratZetaNatRounded_abs_le_nine (M k B : ℕ)
    (hk : 2 ≤ k) (hB : 0 < B) (hM : M ≤ B) :
    |ratZetaNatRoundedLower M k B| ≤ 9 ∧
      |ratZetaNatRoundedUpper M k B| ≤ 9 := by
  have he := ratEtaIntegerRounded_abs_le_three M k B hk hB hM
  have hf0 := (ratZetaNatFactor_pos k hk).le
  have hf2 := ratZetaNatFactor_le_two k hk
  have hi : (1:ℚ)/B ≤ 1 := by apply (div_le_one (by exact_mod_cast hB)).mpr; exact_mod_cast hB
  have htail : |(2:ℚ)/2^M| ≤ 2 := by
    rw [abs_of_nonneg (by positivity)]
    exact (div_le_self (by norm_num) (one_le_pow₀ (by norm_num)))
  have hlo : |ratZetaNatFactor k * ratEtaIntegerRoundedLower M k B| ≤ 6 := by
    rw [abs_mul, abs_of_nonneg hf0]
    nlinarith [mul_le_mul hf2 he.1 (abs_nonneg _) (by norm_num : (0:ℚ) ≤ 2)]
  have hup : |ratZetaNatFactor k * ratEtaIntegerRoundedUpper M k B| ≤ 6 := by
    rw [abs_mul, abs_of_nonneg hf0]
    nlinarith [mul_le_mul hf2 he.2 (abs_nonneg _) (by norm_num : (0:ℚ) ≤ 2)]
  constructor
  · exact (ratRound_abs_le _ B hB).1.trans (by linarith)
  · apply (ratRound_abs_le _ B hB).2.trans
    have ht := abs_add_le (ratZetaNatFactor k * ratEtaIntegerRoundedUpper M k B) ((2:ℚ)/2^M)
    linarith

theorem ratGammaLogCoefficient_abs_le (z : ℚ) (k : ℕ) (hz : |z| ≤ 1/2) :
    |ratGammaLogCoefficient z k| ≤ (1/2:ℚ)^(k+2) := by
  have hk : (2:ℚ) ≤ k+2 := by have := (Nat.cast_nonneg k : (0:ℚ) ≤ k); linarith
  have hpow := pow_le_pow_left₀ (abs_nonneg z) hz (k+2)
  have hp : 0 ≤ (1/2:ℚ)^(k+2) := by positivity
  have hmul : 2 * |z| * (1/2:ℚ)^(k+2) ≤ (1/2:ℚ)^(k+2) := by nlinarith
  unfold ratGammaLogCoefficient
  rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (by positivity : (0:ℚ) ≤ k+2)]
  apply (div_le_iff₀ (by positivity : (0:ℚ) < k+2)).mpr
  have ht : |z^(k+2)-2*z*(1/2:ℚ)^(k+2)| ≤
      |z^(k+2)| + |2*z*(1/2:ℚ)^(k+2)| := by
    simpa only [sub_eq_add_neg, abs_neg] using
      abs_add_le (z^(k+2)) (-(2*z*(1/2:ℚ)^(k+2)))
  rw [abs_pow, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℚ) ≤ 2), abs_of_nonneg hp] at ht
  nlinarith [mul_le_mul_of_nonneg_left hk hp]

theorem ratGammaLogCoefficient_sum_abs_le (z : ℚ) (N : ℕ) (hz : |z| ≤ 1/2) :
    (∑ k ∈ Finset.range N, |ratGammaLogCoefficient z k|) ≤ 1/2 := by
  have hg := geom_sum_mul (1/2:ℚ) N
  have hs : (∑ k ∈ Finset.range N, (1/2:ℚ)^k) ≤ 2 := by
    nlinarith [pow_nonneg (by norm_num : (0:ℚ) ≤ 1/2) N]
  have hb := Finset.sum_le_sum (fun k (_ : k ∈ Finset.range N) => ratGammaLogCoefficient_abs_le z k hz)
  have he : (∑ k ∈ Finset.range N, (1/2:ℚ)^(k+2)) =
      (∑ k ∈ Finset.range N, (1/2:ℚ)^k) * (1/2:ℚ)^2 := by
    simp_rw [pow_add]
    exact (Finset.sum_mul _ _ _).symm
  rw [he] at hb
  norm_num at hb
  linarith

private theorem ratRound_deviation (q : ℚ) (B : ℕ) (hB : 0 < B) :
    q - 1/(B:ℚ) ≤ ratRoundLower q B ∧ ratRoundUpper q B ≤ q + 1/(B:ℚ) := by
  have he := ratRound_enclosure q B hB
  have hw := ratRound_width_le q B hB
  constructor <;> linarith

theorem ratLogArgument_bounds_one_four (q : ℚ) (hq : 1 ≤ q) (hq4 : q ≤ 4) :
    0 ≤ ratLogArgument q ∧ ratLogArgument q ≤ 3/5 := by
  have h := ratLogArgument_bound_on_one_four q hq hq4
  have hn : 0 ≤ ratLogArgument q := by
    unfold ratLogArgument
    exact div_nonneg (sub_nonneg.mpr hq) (by linarith)
  exact ⟨hn, (abs_le.mp h).2⟩

theorem ratLogTaylor_bounds_one_four (q : ℚ) (L : ℕ) (hq : 1 ≤ q) (hq4 : q ≤ 4) :
    0 ≤ ratLogTaylor q L ∧ ratLogTaylor q L ≤ 3 := by
  have ht := ratLogArgument_bounds_one_four q hq hq4
  have hg := geom_sum_mul (3/5:ℚ) L
  have hs : (∑ k ∈ Finset.range L, (3/5:ℚ)^k) ≤ 5/2 := by
    nlinarith [pow_nonneg (by norm_num : (0:ℚ) ≤ 3/5) L]
  have hb (k : ℕ) : ratLogArgument q^(2*k+1)/(2*(k:ℚ)+1) ≤ (3/5:ℚ)^(k+1) := by
    calc
      _ ≤ ratLogArgument q^(2*k+1) :=
        div_le_self (pow_nonneg ht.1 _) (by have := (Nat.cast_nonneg k : (0:ℚ) ≤ k); linarith)
      _ ≤ (3/5:ℚ)^(2*k+1) := pow_le_pow_left₀ ht.1 ht.2 _
      _ ≤ (3/5:ℚ)^(k+1) := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ Finset.range L) => hb k)
  have he : (∑ k ∈ Finset.range L, (3/5:ℚ)^(k+1)) =
      (3/5:ℚ) * ∑ k ∈ Finset.range L, (3/5:ℚ)^k := by
    simp_rw [pow_succ']; rw [Finset.mul_sum]
  rw [he] at hsum
  unfold ratLogTaylor
  constructor
  · apply mul_nonneg (by norm_num)
    exact Finset.sum_nonneg (fun k _ => div_nonneg (pow_nonneg ht.1 _) (by positivity))
  · nlinarith

theorem ratLogUniformError_le_two (r : ℚ) (L : ℕ) (hr0 : 0 ≤ r) (hr : r ≤ 3/5) :
    0 ≤ ratLogUniformError r L ∧ ratLogUniformError r L ≤ 2 := by
  have hs := pow_le_pow_left₀ hr0 hr 2
  have hd : 0 < 1-r^2 := by norm_num at hs; linarith
  have hp : r^(2*L+1) ≤ r := by
    simpa using pow_le_pow_of_le_one hr0 (show r ≤ 1 by linarith) (show 1 ≤ 2*L+1 by omega)
  unfold ratLogUniformError
  constructor
  · positivity
  · apply (div_le_iff₀ hd).mpr
    norm_num at hs
    nlinarith

theorem ratLogTermRounded_range (q : ℚ) (B k : ℕ) (hB : 0 < B)
    (hq : 1 ≤ q) (hq4 : q ≤ 4) :
    0 ≤ (ratLogTermRounded q B k).1 ∧
      (ratLogTermRounded q B k).2 ≤
        ratLogArgument q^(2*k+1)/((2*k+1:ℕ):ℚ) + 2/(B:ℚ) := by
  have ht := ratLogArgument_bounds_one_four q hq hq4
  have hbp : (0:ℚ) < B := by exact_mod_cast hB
  have hdiv : (2:ℚ)/B = 2*(1/(B:ℚ)) := by ring
  induction k with
  | zero =>
    have hb := (ratRound_deviation (ratLogArgument q) B hB).2
    constructor
    · exact ratRoundLower_nonneg _ B ht.1
    · simpa only [ratLogTermRounded, Nat.mul_zero, Nat.zero_add, Nat.cast_one,
        pow_one, div_one] using (hb.trans (by rw [hdiv]; linarith [show (0:ℚ) ≤ 1/(B:ℚ) by positivity]))
  | succ k ih =>
    let c : ℚ := ratLogArgument q^2 * ((2*k+1:ℕ):ℚ) / ((2*k+3:ℕ):ℚ)
    have hc0 : 0 ≤ c := by dsimp [c]; positivity
    have hc : c ≤ 1/2 := by
      have hs := pow_le_pow_left₀ ht.1 ht.2 2
      have hden : (0:ℚ) < ((2*k+3:ℕ):ℚ) := by positivity
      have hb : c ≤ ratLogArgument q^2 := by
        apply (div_le_iff₀ hden).mpr
        have hrat : ((2*k+1:ℕ):ℚ) ≤ ((2*k+3:ℕ):ℚ) := by exact_mod_cast (show 2*k+1 ≤ 2*k+3 by omega)
        exact mul_le_mul_of_nonneg_left hrat (sq_nonneg _)
      norm_num at hs
      linarith
    have he : ratLogArgument q^(2*(k+1)+1)/((2*(k+1)+1:ℕ):ℚ) =
        (ratLogArgument q^(2*k+1)/((2*k+1:ℕ):ℚ))*c := by
      have hexp : 2*(k+1)+1 = (2*k+1)+2 := by omega
      rw [hexp, pow_add]
      have hd : ((2*k+1:ℕ):ℚ) ≠ 0 := by positivity
      dsimp [c]
      push_cast at hd ⊢
      field_simp
      ring
    constructor
    · exact ratRoundLower_nonneg _ B (mul_nonneg ih.1 hc0)
    · change ratRoundUpper ((ratLogTermRounded q B k).2*c) B ≤ _
      rw [he]
      have hu := (ratRound_deviation ((ratLogTermRounded q B k).2*c) B hB).2
      have hm := mul_le_mul_of_nonneg_right ih.2 hc0
      have hc' := mul_le_mul_of_nonneg_left hc (show (0:ℚ) ≤ 2/(B:ℚ) by positivity)
      rw [hdiv] at hm hc' ⊢
      nlinarith

theorem ratLogTaylorRounded_range (q : ℚ) (L B : ℕ) (hB : 0 < B) (hL : L ≤ B)
    (hq : 1 ≤ q) (hq4 : q ≤ 4) :
    0 ≤ ratLogTaylorRoundedLower q L B ∧ ratLogTaylorRoundedLower q L B ≤ 3 ∧
      0 ≤ ratLogTaylorRoundedUpper q L B ∧ ratLogTaylorRoundedUpper q L B ≤ 7 := by
  have ht := ratLogTaylor_bounds_one_four q L hq hq4
  have he := ratLogTaylorRounded_enclosure q L B hB
  have hsum : (∑ k ∈ Finset.range L, (ratLogTermRounded q B k).2) ≤
      (∑ k ∈ Finset.range L, ratLogArgument q^(2*k+1)/((2*k+1:ℕ):ℚ)) + (L:ℚ)*(2/B) := by
    have h := Finset.sum_le_sum (fun k (_ : k ∈ Finset.range L) => (ratLogTermRounded_range q B k hB hq hq4).2)
    simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] using h
  have hl : (L:ℚ)/B ≤ 1 := (div_le_one (by exact_mod_cast hB)).mpr (by exact_mod_cast hL)
  refine ⟨?_, he.1.trans ht.2, ht.1.trans he.2, ?_⟩
  · apply mul_nonneg (by norm_num)
    exact Finset.sum_nonneg (fun k _ => (ratLogTermRounded_range q B k hB hq hq4).1)
  · unfold ratLogTaylorRoundedUpper
    unfold ratLogTaylor at ht
    push_cast at hsum
    have hmul : (L:ℚ)*(2/B) ≤ 2 := by
      have he : (L:ℚ)*(2/B) = 2*((L:ℚ)/B) := by ring
      rw [he]
      linarith
    nlinarith [ht.2]

theorem ratLogFullyRounded_abs_le_ten (q r : ℚ) (L B : ℕ)
    (hB : 0 < B) (hL : L ≤ B) (hq : 1 ≤ q) (hq4 : q ≤ 4)
    (hr0 : 0 ≤ r) (hr : r ≤ 3/5) :
    |ratLogFullyRoundedLower q r L B| ≤ 10 ∧
      |ratLogFullyRoundedUpper q r L B| ≤ 10 := by
  have ht := ratLogTaylorRounded_range q L B hB hL hq hq4
  have he := ratLogUniformError_le_two r L hr0 hr
  have hi : (1:ℚ)/B ≤ 1 := by apply (div_le_one (by exact_mod_cast hB)).mpr; exact_mod_cast hB
  have hl : |ratLogTaylorRoundedLower q L B-ratLogUniformError r L| ≤ 5 := by
    rw [abs_le]; constructor <;> linarith
  have hu : |ratLogTaylorRoundedUpper q L B+ratLogUniformError r L| ≤ 9 := by
    rw [abs_of_nonneg (add_nonneg ht.2.2.1 he.1)]; linarith
  constructor
  · exact (ratRound_abs_le _ B hB).1.trans (by linarith)
  · exact (ratRound_abs_le _ B hB).2.trans (by linarith)

private theorem rounded_signed_abs_bound (c a b R : ℚ) (B : ℕ) (hB : 0 < B)
    (ha : |a| ≤ R) (hb : |b| ≤ R) :
    |ratRoundLower (min (c*a) (c*b)) B| ≤ |c| * R+1/(B:ℚ) ∧
      |ratRoundUpper (max (c*a) (c*b)) B| ≤ |c| * R+1/(B:ℚ) := by
  have hca : |c*a| ≤ |c| * R := by rw [abs_mul]; exact mul_le_mul_of_nonneg_left ha (abs_nonneg c)
  have hcb : |c*b| ≤ |c| * R := by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hb (abs_nonneg c)
  have hra := ratRound_abs_le (c*a) B hB
  have hrb := ratRound_abs_le (c*b) B hB
  rcases le_total (c*a) (c*b) with h | h
  · rw [min_eq_left h, max_eq_right h]
    constructor <;> linarith only [hra.1, hrb.2, hca, hcb]
  · rw [min_eq_right h, max_eq_left h]
    constructor <;> linarith only [hrb.1, hra.2, hca, hcb]

theorem ratGammaConstantFast_abs_le_seventeen (z : ℚ) (L B : ℕ)
    (hz : |z| ≤ 1/2) (hB : 0 < B) (hL : L ≤ B) :
    |ratGammaConstantFastLower z L B| ≤ 17 ∧
      |ratGammaConstantFastUpper z L B| ≤ 17 := by
  have he := machinPi_endpoints_one_four
  have hpL := ratLogFullyRounded_abs_le_ten machinPiLower (3/5) L B hB hL
    he.1.1 he.1.2 (by norm_num) (by norm_num)
  have hpU := ratLogFullyRounded_abs_le_ten machinPiUpper (3/5) L B hB hL
    he.2.1 he.2.2 (by norm_num) (by norm_num)
  have ht := ratLogFullyRounded_abs_le_ten 2 (1/3) L B hB hL
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hpr := rounded_signed_abs_bound z (ratPiLogFullyRoundedLower L B)
    (ratPiLogFullyRoundedUpper L B) 10 B hB hpL.1 hpU.2
  have htr := rounded_signed_abs_bound (-2*z) _ _ 10 B hB ht.1 ht.2
  have hi : (1:ℚ)/B ≤ 1 := by apply (div_le_one (by exact_mod_cast hB)).mpr; exact_mod_cast hB
  have hz2 : |(-2:ℚ)*z| ≤ 1 := by rw [abs_mul]; norm_num; linarith
  unfold ratGammaConstantFastLower ratGammaConstantFastUpper
  constructor
  · apply (abs_add_le _ _).trans
    change |ratRoundLower (min _ _) B| + _ ≤ _
    linarith [hpr.1, htr.1]
  · apply (abs_add_le _ _).trans
    change |ratRoundUpper (max _ _) B| + _ ≤ _
    linarith [hpr.2, htr.2]

theorem ratGammaCoefficientRounded_sum_abs_bound (z : ℚ) (N M B : ℕ)
    (hz : |z| ≤ 1/2) (hB : 0 < B) (hN : N ≤ B) (hM : M ≤ B) :
    |∑ k ∈ Finset.range N, ratGammaCoefficientRoundedLower z k M B| ≤ 11/2 ∧
      |∑ k ∈ Finset.range N, ratGammaCoefficientRoundedUpper z k M B| ≤ 11/2 := by
  have hcoef := ratGammaLogCoefficient_sum_abs_le z N hz
  have hi : (N:ℚ)/B ≤ 1 := (div_le_one (by exact_mod_cast hB)).mpr (by exact_mod_cast hN)
  have ht (k : ℕ) :
      |ratGammaCoefficientRoundedLower z k M B| ≤ |ratGammaLogCoefficient z k| * 9+1/(B:ℚ) ∧
      |ratGammaCoefficientRoundedUpper z k M B| ≤ |ratGammaLogCoefficient z k| * 9+1/(B:ℚ) := by
    have he := ratZetaNatRounded_abs_le_nine M (k+2) B (by omega) hB hM
    exact rounded_signed_abs_bound _ _ _ 9 B hB he.1 he.2
  have hs : (∑ k ∈ Finset.range N, (|ratGammaLogCoefficient z k| * 9+1/(B:ℚ))) ≤ 11/2 := by
    rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [← div_eq_mul_one_div]
    linarith
  constructor
  · exact (Finset.abs_sum_le_sum_abs _ _).trans
      ((Finset.sum_le_sum (fun k _ => (ht k).1)).trans hs)
  · exact (Finset.abs_sum_le_sum_abs _ _).trans
      ((Finset.sum_le_sum (fun k _ => (ht k).2)).trans hs)

theorem ratLogGammaFast_abs_le_thirtytwo (z : ℚ) (N M L B : ℕ)
    (hz : |z| ≤ 1/2) (hB : 0 < B) (hN : N ≤ B) (hM : M ≤ B) (hL : L ≤ B) :
    |ratLogGammaFastLower z N M L B| ≤ 32 ∧
      |ratLogGammaFastUpper z N M L B| ≤ 32 := by
  have hc := ratGammaConstantFast_abs_le_seventeen z L B hz hB hL
  have hs := ratGammaCoefficientRounded_sum_abs_bound z N M B hz hB hN hM
  have he : |8*(1/2:ℚ)^(N+2)| ≤ 2 := by
    rw [abs_of_nonneg (by positivity)]
    have h := pow_le_pow_of_le_one (by norm_num : (0:ℚ) ≤ 1/2)
      (by norm_num : (1/2:ℚ) ≤ 1) (show 2 ≤ N+2 by omega)
    norm_num at h
    linarith
  have hi : (1:ℚ)/B ≤ 1 := by apply (div_le_one (by exact_mod_cast hB)).mpr; exact_mod_cast hB
  have hl : |ratGammaConstantFastLower z L B +
      (∑ k ∈ Finset.range N, ratGammaCoefficientRoundedLower z k M B) -
      8*(1/2:ℚ)^(N+2)| ≤ 49/2 := by
    have h := abs_add_le (ratGammaConstantFastLower z L B)
      (∑ k ∈ Finset.range N, ratGammaCoefficientRoundedLower z k M B)
    have h' := abs_add_le (ratGammaConstantFastLower z L B +
      (∑ k ∈ Finset.range N, ratGammaCoefficientRoundedLower z k M B)) (-(8*(1/2:ℚ)^(N+2)))
    rw [abs_neg, ← sub_eq_add_neg] at h'
    linarith
  have hu : |ratGammaConstantFastUpper z L B +
      (∑ k ∈ Finset.range N, ratGammaCoefficientRoundedUpper z k M B) +
      8*(1/2:ℚ)^(N+2)| ≤ 49/2 := by
    have h := abs_add_le (ratGammaConstantFastUpper z L B)
      (∑ k ∈ Finset.range N, ratGammaCoefficientRoundedUpper z k M B)
    have h' := abs_add_le (ratGammaConstantFastUpper z L B +
      (∑ k ∈ Finset.range N, ratGammaCoefficientRoundedUpper z k M B)) (8*(1/2:ℚ)^(N+2))
    linarith
  exact ⟨(ratRound_abs_le _ B hB).1.trans (by linarith),
    (ratRound_abs_le _ B hB).2.trans (by linarith)⟩

theorem ratLogGammaFast_scaled_checks (z : ℚ) (N M L B m : ℕ)
    (hz : |z| ≤ 1/2) (hB : 0 < B) (hN : N ≤ B) (hM : M ≤ B) (hL : L ≤ B)
    (hm : 32 ≤ m) :
    |ratLogGammaFastLower z N M L B / m| ≤ 1 ∧
      |ratLogGammaFastUpper z N M L B / m| ≤ 1 := by
  have h := ratLogGammaFast_abs_le_thirtytwo z N M L B hz hB hN hM hL
  have hmR : (32:ℚ) ≤ m := by exact_mod_cast hm
  have hm0 : (0:ℚ) < m := by linarith
  constructor <;> rw [abs_div, abs_of_pos hm0, div_le_one hm0] <;> linarith

end ReciprocalXi

