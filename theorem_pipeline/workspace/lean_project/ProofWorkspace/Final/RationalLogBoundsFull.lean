import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
# Exact rational logarithm enclosures

The transformation t=(q-1)/(q+1) maps every positive rational input to
(-1,1). A finite odd power series with a proved remainder bounds the actual
real logarithm, including inputs below one.
-/

namespace ReciprocalXi

def ratLogArgument (q : ℚ) : ℚ := (q - 1) / (q + 1)

def ratLogTaylor (q : ℚ) (n : ℕ) : ℚ :=
  2 * ∑ k ∈ Finset.range n, ratLogArgument q ^ (2 * k + 1) / (2 * k + 1)

def ratLogError (q : ℚ) (n : ℕ) : ℚ :=
  2 * |ratLogArgument q| ^ (2 * n + 1) / (1 - ratLogArgument q ^ 2)

theorem ratLogArgument_abs_lt_one (q : ℚ) (hq : 0 < q) :
    |(ratLogArgument q : ℝ)| < 1 := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hd : (0 : ℝ) < q + 1 := by linarith
  unfold ratLogArgument
  push_cast
  rw [abs_lt]
  constructor
  · apply (lt_div_iff₀ hd).mpr
    linarith
  · apply (div_lt_iff₀ hd).mpr
    linarith

theorem ratLogArgument_ratio (q : ℚ) (hq : 0 < q) :
    (1 + (ratLogArgument q : ℝ)) / (1 - (ratLogArgument q : ℝ)) = q := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hd : (q : ℝ) + 1 ≠ 0 := by linarith
  unfold ratLogArgument
  push_cast
  field_simp
  ring

theorem ratLogTaylor_cast (q : ℚ) (n : ℕ) :
    (ratLogTaylor q n : ℝ) =
      2 * ∑ k ∈ Finset.range n, (ratLogArgument q : ℝ) ^ (2 * k + 1) / (2 * k + 1) := by
  unfold ratLogTaylor
  push_cast
  rfl

theorem ratLogError_cast (q : ℚ) (n : ℕ) :
    (ratLogError q n : ℝ) =
      2 * |(ratLogArgument q : ℝ)| ^ (2 * n + 1) / (1 - (ratLogArgument q : ℝ) ^ 2) := by
  unfold ratLogError
  push_cast
  rfl

theorem ratLogTaylor_error (q : ℚ) (n : ℕ) (hq : 0 < q) :
    |Real.log (q : ℝ) - (ratLogTaylor q n : ℝ)| ≤ (ratLogError q n : ℝ) := by
  have h := Real.sum_range_sub_log_div_le (ratLogArgument_abs_lt_one q hq) n
  rw [ratLogArgument_ratio q hq] at h
  rw [ratLogTaylor_cast, ratLogError_cast]
  calc
    _ = 2 * |1 / 2 * Real.log (q : ℝ) -
        ∑ k ∈ Finset.range n, (ratLogArgument q : ℝ) ^ (2 * k + 1) / (2 * k + 1)| := by
      rw [← abs_of_pos (by norm_num : (0 : ℝ) < 2), ← abs_mul]
      congr 1
      ring
    _ ≤ 2 * (|(ratLogArgument q : ℝ)| ^ (2 * n + 1) /
        (1 - (ratLogArgument q : ℝ) ^ 2)) := mul_le_mul_of_nonneg_left h (by norm_num)
    _ = _ := by ring

/-- Every positive rational input has sound exact lower and upper endpoints. -/
theorem ratLog_enclosure (q : ℚ) (n : ℕ) (hq : 0 < q) :
    ((ratLogTaylor q n - ratLogError q n : ℚ) : ℝ) ≤ Real.log (q : ℝ) ∧
      Real.log (q : ℝ) ≤ ((ratLogTaylor q n + ratLogError q n : ℚ) : ℝ) := by
  have h := abs_le.mp (ratLogTaylor_error q n hq)
  push_cast
  constructor <;> linarith

/-- The bound is for the entire positive interval, not just its endpoints. -/
theorem ratLog_interval_enclosure (a b : ℚ) (x : ℝ) (n : ℕ)
    (ha : 0 < a) (hax : (a : ℝ) ≤ x) (hxb : x ≤ (b : ℝ)) :
    ((ratLogTaylor a n - ratLogError a n : ℚ) : ℝ) ≤ Real.log x ∧
      Real.log x ≤ ((ratLogTaylor b n + ratLogError b n : ℚ) : ℝ) := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hx : 0 < x := ha'.trans_le hax
  have hb : 0 < b := by exact_mod_cast (hx.trans_le hxb)
  exact ⟨(ratLog_enclosure a n ha).1.trans (Real.log_le_log ha' hax),
    (Real.log_le_log hx hxb).trans (ratLog_enclosure b n hb).2⟩

def ratLogDyadicLower (r : ℚ) (m n : ℕ) : ℚ :=
  m * (ratLogTaylor 2 n - ratLogError 2 n) + ratLogTaylor r n - ratLogError r n

def ratLogDyadicUpper (r : ℚ) (m n : ℕ) : ℚ :=
  m * (ratLogTaylor 2 n + ratLogError 2 n) + ratLogTaylor r n + ratLogError r n

/-- Exact dyadic range reduction: a large input 2^m*r can be checked using
only logarithm series at 2 and r, with no loss hidden in floating arithmetic. -/
theorem ratLog_dyadic_enclosure (r : ℚ) (m n : ℕ) (hr : 0 < r) :
    (ratLogDyadicLower r m n : ℝ) ≤ Real.log (((2 : ℚ) ^ m * r : ℚ) : ℝ) ∧
      Real.log (((2 : ℚ) ^ m * r : ℚ) : ℝ) ≤ (ratLogDyadicUpper r m n : ℝ) := by
  have h2 := ratLog_enclosure 2 n (by norm_num)
  have hrb := ratLog_enclosure r n hr
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hlog : Real.log (((2 : ℚ) ^ m * r : ℚ) : ℝ) =
      (m : ℝ) * Real.log 2 + Real.log (r : ℝ) := by
    push_cast
    rw [Real.log_mul (by positivity) (ne_of_gt hr'), Real.log_pow]
  rw [hlog]
  unfold ratLogDyadicLower ratLogDyadicUpper
  push_cast at h2 hrb ⊢
  have hl := mul_le_mul_of_nonneg_left h2.1 (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
  have hu := mul_le_mul_of_nonneg_left h2.2 (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
  constructor <;> linarith [hrb.1, hrb.2]

/-- A kernel-checked eight-decimal enclosure, not a trusted decimal input. -/
theorem log_two_certified :
    (69314718 : ℝ) / 100000000 ≤ Real.log 2 ∧
      Real.log 2 ≤ (69314719 : ℝ) / 100000000 := by
  have h := ratLog_enclosure 2 10 (by norm_num)
  norm_num [ratLogTaylor, ratLogError, ratLogArgument, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

end ReciprocalXi
