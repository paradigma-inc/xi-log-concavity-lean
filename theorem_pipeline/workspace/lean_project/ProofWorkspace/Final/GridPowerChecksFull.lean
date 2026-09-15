import ProofWorkspace.Final.RoundedEtaGridBoundsFull

/-! Uniform rational initial range checks for all eta-grid bases 1 through 512.
The geometric-series proof holds for every logarithm order, including zero. -/

set_option autoImplicit false

namespace ReciprocalXi

theorem ratLogArgument_mem_Icc_of_one_le (r : ℚ) (hr : 1 ≤ r) (hr2 : r ≤ 2) :
    ratLogArgument r ∈ Set.Icc (0 : ℚ) (1/3) := by
  have hd : 0 < r + 1 := by linarith
  unfold ratLogArgument
  constructor
  · exact div_nonneg (by linarith) hd.le
  · apply (div_le_iff₀ hd).mpr
    linarith

theorem ratLogTaylor_bounds_unit_mantissa (r : ℚ) (L : ℕ)
    (hr : 1 ≤ r) (hr2 : r ≤ 2) :
    0 ≤ ratLogTaylor r L ∧ ratLogTaylor r L ≤ 1 := by
  have ht := ratLogArgument_mem_Icc_of_one_le r hr hr2
  have hsum : (∑ k ∈ Finset.range L, (1/3 : ℚ)^k) ≤ 3/2 := by
    have he := geom_sum_mul (1/3 : ℚ) L
    nlinarith [pow_nonneg (by norm_num : (0 : ℚ) ≤ 1/3) L]
  have hterm (k : ℕ) : ratLogArgument r ^ (2*k+1) / (2*(k:ℚ)+1) ≤
      (1/3 : ℚ)^(k+1) := by
    calc
      _ ≤ ratLogArgument r ^ (2*k+1) := by
        apply div_le_self (pow_nonneg ht.1 _) (by have := (Nat.cast_nonneg k : (0:ℚ) ≤ k); linarith)
      _ ≤ (1/3 : ℚ)^(2*k+1) := pow_le_pow_left₀ ht.1 ht.2 _
      _ ≤ (1/3 : ℚ)^(k+1) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hbound : (∑ k ∈ Finset.range L,
      ratLogArgument r ^ (2*k+1) / (2*(k:ℚ)+1)) ≤
      (1/3 : ℚ) * ∑ k ∈ Finset.range L, (1/3 : ℚ)^k := by
    calc
      _ ≤ ∑ k ∈ Finset.range L, (1/3 : ℚ)^(k+1) :=
        Finset.sum_le_sum fun k _ => hterm k
      _ = _ := by simp_rw [pow_succ']; rw [Finset.mul_sum]
  unfold ratLogTaylor
  constructor
  · apply mul_nonneg (by norm_num)
    apply Finset.sum_nonneg
    intro k hk
    exact div_nonneg (pow_nonneg ht.1 _) (by positivity)
  · exact (mul_le_mul_of_nonneg_left hbound (by norm_num)).trans (by nlinarith)

theorem ratLogError_bounds_unit_mantissa (r : ℚ) (L : ℕ)
    (hr : 1 ≤ r) (hr2 : r ≤ 2) :
    0 ≤ ratLogError r L ∧ ratLogError r L ≤ 1 := by
  have ht := ratLogArgument_mem_Icc_of_one_le r hr hr2
  have hs : ratLogArgument r ^ 2 ≤ (1/3 : ℚ)^2 :=
    pow_le_pow_left₀ ht.1 ht.2 2
  have hd : 0 < 1 - ratLogArgument r ^ 2 := by norm_num at hs; linarith
  have hp : ratLogArgument r ^ (2*L+1) ≤ 1/3 := by
    calc
      _ ≤ ratLogArgument r ^ 1 :=
        pow_le_pow_of_le_one ht.1 (by linarith [ht.2]) (by omega)
      _ ≤ 1/3 := by simpa using ht.2
  unfold ratLogError
  rw [abs_of_nonneg ht.1]
  constructor
  · exact div_nonneg (mul_nonneg (by norm_num) (pow_nonneg ht.1 _)) hd.le
  · apply (div_le_iff₀ hd).mpr
    norm_num at hs
    nlinarith

theorem ratLogDyadic_bounds_small (r : ℚ) (d L : ℕ)
    (hr : 1 ≤ r) (hr2 : r ≤ 2) (hd : d ≤ 9) :
    |ratLogDyadicLower r d L| ≤ 20 ∧ |ratLogDyadicUpper r d L| ≤ 20 := by
  have ht := ratLogTaylor_bounds_unit_mantissa r L hr hr2
  have he := ratLogError_bounds_unit_mantissa r L hr hr2
  have ht2 := ratLogTaylor_bounds_unit_mantissa 2 L (by norm_num) (by norm_num)
  have he2 := ratLogError_bounds_unit_mantissa 2 L (by norm_num) (by norm_num)
  have hd0 : (0 : ℚ) ≤ d := Nat.cast_nonneg d
  have hd9 : (d : ℚ) ≤ 9 := by exact_mod_cast hd
  have hl0 : -(d:ℚ) ≤ (d:ℚ)*(ratLogTaylor 2 L-ratLogError 2 L) := by
    nlinarith [mul_le_mul_of_nonneg_left (show (-1:ℚ) ≤ ratLogTaylor 2 L-ratLogError 2 L by linarith) hd0]
  have hl1 : (d:ℚ)*(ratLogTaylor 2 L-ratLogError 2 L) ≤ d := by
    nlinarith [mul_le_mul_of_nonneg_left (show ratLogTaylor 2 L-ratLogError 2 L ≤ (1:ℚ) by linarith) hd0]
  have hu0 : 0 ≤ (d:ℚ)*(ratLogTaylor 2 L+ratLogError 2 L) :=
    mul_nonneg hd0 (add_nonneg ht2.1 he2.1)
  have hu1 : (d:ℚ)*(ratLogTaylor 2 L+ratLogError 2 L) ≤ 2*d := by
    nlinarith [mul_le_mul_of_nonneg_left (show ratLogTaylor 2 L+ratLogError 2 L ≤ (2:ℚ) by linarith) hd0]
  unfold ratLogDyadicLower ratLogDyadicUpper
  constructor <;> rw [abs_le] <;> constructor <;> linarith

theorem ratPowerDyadic_scaled_checks (r q : ℚ) (d L : ℕ)
    (hr : 1 ≤ r) (hr2 : r ≤ 2) (hd : d ≤ 9) (hq : |q| ≤ 1/2) :
    |ratPowerDyadicLogLower r q d L / 16| ≤ 1 ∧
      |ratPowerDyadicLogUpper r q d L / 16| ≤ 1 := by
  have h := ratLogDyadic_bounds_small r d L hr hr2 hd
  have hl : |q*ratLogDyadicLower r d L| ≤ 10 := by
    rw [abs_mul]
    nlinarith [mul_le_mul hq h.1 (abs_nonneg _) (by norm_num : (0:ℚ) ≤ 1/2)]
  have hu : |q*ratLogDyadicUpper r d L| ≤ 10 := by
    rw [abs_mul]
    nlinarith [mul_le_mul hq h.2 (abs_nonneg _) (by norm_num : (0:ℚ) ≤ 1/2)]
  have hll := (abs_le.mp hl).1
  have hlu := (abs_le.mp hl).2
  have hul := (abs_le.mp hu).1
  have huu := (abs_le.mp hu).2
  have hmin : |min (q*ratLogDyadicLower r d L) (q*ratLogDyadicUpper r d L)| ≤ 10 := by
    rw [abs_le]
    exact ⟨le_min hll hul, (min_le_left _ _).trans hlu⟩
  have hmax : |max (q*ratLogDyadicLower r d L) (q*ratLogDyadicUpper r d L)| ≤ 10 := by
    rw [abs_le]
    exact ⟨hll.trans (le_max_left _ _), max_le hlu huu⟩
  unfold ratPowerDyadicLogLower ratPowerDyadicLogUpper
  constructor <;> rw [abs_div] <;> norm_num <;> linarith

theorem gridPowerChecks_512 (a L : ℕ) (ha : 1 ≤ a) (ha512 : a ≤ 512) :
    GridPowerChecks a L 16 := by
  have hm := ratPowerNatMantissa_mem_Ico a (by omega)
  have hd : Nat.log2 a ≤ 9 := by
    by_contra hn
    have hexp : 2^10 ≤ 2^Nat.log2 a :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hb := Nat.log2_self_le (n := a) (by omega)
    norm_num at hexp
    omega
  have hhalf := ratPowerDyadic_scaled_checks (ratPowerNatMantissa a) (-(1/2))
    (Nat.log2 a) L hm.1 hm.2.le hd (by norm_num)
  have hstep := ratPowerDyadic_scaled_checks (ratPowerNatMantissa a) (-(1/80))
    (Nat.log2 a) L hm.1 hm.2.le hd (by norm_num)
  exact ⟨hhalf.1, hhalf.2, hstep.1, hstep.2⟩

theorem gridPowerChecks_range (N L : ℕ) (hN : N ≤ 512) :
    ∀ j ∈ Finset.range N, GridPowerChecks (j+1) L 16 := by
  intro j hj
  have hjN := Finset.mem_range.mp hj
  exact gridPowerChecks_512 (j+1) L (by omega) (by omega)


private theorem scaledCheck_mono (x : ℚ) (m n : ℕ)
    (hm : 0 < m) (hmn : m ≤ n) (hx : |x / m| ≤ 1) : |x / n| ≤ 1 := by
  have hmR : (0 : ℚ) < m := by exact_mod_cast hm
  have hmnR : (m : ℚ) ≤ n := by exact_mod_cast hmn
  have hnR : (0 : ℚ) < n := hmR.trans_le hmnR
  rw [abs_div, abs_of_pos hmR] at hx
  rw [abs_div, abs_of_pos hnR]
  exact (div_le_div_of_nonneg_left (abs_nonneg x) hmR hmnR).trans hx

theorem gridPowerChecks_mono (a L m n : ℕ) (hm : 0 < m) (hmn : m ≤ n)
    (h : GridPowerChecks a L m) : GridPowerChecks a L n := by
  exact ⟨scaledCheck_mono _ m n hm hmn h.half_lower,
    scaledCheck_mono _ m n hm hmn h.half_upper,
    scaledCheck_mono _ m n hm hmn h.step_lower,
    scaledCheck_mono _ m n hm hmn h.step_upper⟩

theorem gridPowerChecks_range_of_sixteen_le (N L m : ℕ)
    (hN : N ≤ 512) (hm : 16 ≤ m) :
    ∀ j ∈ Finset.range N, GridPowerChecks (j+1) L m := by
  intro j hj
  exact gridPowerChecks_mono (j+1) L 16 m (by norm_num) hm
    (gridPowerChecks_range N L hN j hj)


end ReciprocalXi
