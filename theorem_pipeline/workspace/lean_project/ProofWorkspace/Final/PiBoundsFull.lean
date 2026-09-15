import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
# Exact rational Machin pi bounds

Finite arctangent sums of lengths 150 and 45 have proved geometric tails.
The resulting directed rational interval contains actual pi and has width
less than 10^-160, without trusting decimal values or native evaluation.
-/

noncomputable section
open scoped BigOperators
namespace ReciprocalXi

def ratArctanTaylor (q : ℚ) (N : ℕ) : ℚ :=
  ∑ n ∈ Finset.range N, (-1 : ℚ) ^ n * q ^ (2 * n + 1) / (2 * n + 1)

def ratArctanError (q : ℚ) (N : ℕ) : ℚ :=
  |q| ^ (2 * N + 1) / (1 - q ^ 2)

theorem arctanTaylor_error (x : ℝ) (N : ℕ) (hx : |x| < 1) :
    |Real.arctan x - ∑ n ∈ Finset.range N,
      (-1 : ℝ) ^ n * x ^ (2 * n + 1) / (2 * n + 1)| ≤
      |x| ^ (2 * N + 1) / (1 - x ^ 2) := by
  have hs := Real.hasSum_arctan (by simpa only [Real.norm_eq_abs] using hx)
  have ht := (hasSum_nat_add_iff' N).mpr hs
  have hx2 : |x| ^ 2 < 1 := by nlinarith [abs_nonneg x]
  have hg := (hasSum_geometric_of_lt_one (sq_nonneg |x|) hx2).mul_left
    (|x| ^ (2 * N + 1))
  have hb := ht.norm_le_of_bounded hg (fun n => by
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_pow]
    norm_num only [abs_neg, abs_one, one_pow, one_mul]
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 * (n + N) + 1 : ℕ))]
    calc
      _ ≤ |x| ^ (2 * (n + N) + 1) := div_le_self (by positivity) (by norm_cast; omega)
      _ = _ := by ring)
  simpa only [Real.norm_eq_abs, sq_abs, div_eq_mul_inv, Nat.cast_add,
    Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hb

theorem ratArctanTaylor_error (q : ℚ) (N : ℕ) (hq : |q| < 1) :
    |Real.arctan (q : ℝ) - (ratArctanTaylor q N : ℝ)| ≤
      (ratArctanError q N : ℝ) := by
  have h := arctanTaylor_error (q : ℝ) N (by exact_mod_cast hq)
  convert h using 1 <;> simp [ratArctanTaylor, ratArctanError]

def machinPiMidpoint : ℚ :=
  16 * ratArctanTaylor (1 / 5) 150 - 4 * ratArctanTaylor (1 / 239) 45

def machinPiRadius : ℚ :=
  16 * ratArctanError (1 / 5) 150 + 4 * ratArctanError (1 / 239) 45

def machinPiLower : ℚ := machinPiMidpoint - machinPiRadius
def machinPiUpper : ℚ := machinPiMidpoint + machinPiRadius

theorem machinPi_error : |Real.pi - (machinPiMidpoint : ℝ)| ≤ (machinPiRadius : ℝ) := by
  have h5 := ratArctanTaylor_error (1 / 5) 150 (by norm_num)
  have h239 := ratArctanTaylor_error (1 / 239) 45 (by norm_num)
  have hm := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at h5 h239
  unfold machinPiMidpoint machinPiRadius
  push_cast
  have heq : Real.pi - (16 * (ratArctanTaylor (1 / 5) 150 : ℝ) -
      4 * (ratArctanTaylor (1 / 239) 45 : ℝ)) =
      16 * (Real.arctan (1 / 5) - (ratArctanTaylor (1 / 5) 150 : ℝ)) -
      4 * (Real.arctan (1 / 239) - (ratArctanTaylor (1 / 239) 45 : ℝ)) := by
    norm_num only [one_div] at *
    linarith
  rw [heq]
  calc
    _ ≤ |16 * (Real.arctan (1 / 5) - (ratArctanTaylor (1 / 5) 150 : ℝ))| +
        |4 * (Real.arctan (1 / 239) - (ratArctanTaylor (1 / 239) 45 : ℝ))| := abs_sub _ _
    _ = 16 * |Real.arctan (1 / 5) - (ratArctanTaylor (1 / 5) 150 : ℝ)| +
        4 * |Real.arctan (1 / 239) - (ratArctanTaylor (1 / 239) 45 : ℝ)| := by
      rw [abs_mul, abs_mul]
      norm_num
    _ ≤ _ := by linarith

theorem machinPi_enclosure : (machinPiLower : ℝ) ≤ Real.pi ∧ Real.pi ≤ (machinPiUpper : ℝ) := by
  have h := abs_le.mp machinPi_error
  unfold machinPiLower machinPiUpper
  push_cast
  constructor <;> linarith

set_option exponentiation.threshold 512 in
theorem machinPi_width_lt : machinPiUpper - machinPiLower < 1 / (10 : ℚ) ^ 160 := by
  unfold machinPiUpper machinPiLower
  ring_nf
  norm_num [machinPiRadius, ratArctanError]

theorem machinPiLower_pos : 0 < machinPiLower := by
  have hw : (machinPiUpper : ℝ) - (machinPiLower : ℝ) < 1 := by
    have h := machinPi_width_lt
    have h' : machinPiUpper - machinPiLower < 1 :=
      h.trans (by norm_num)
    exact_mod_cast h'
  have hp := machinPi_enclosure.2
  have h3 := Real.pi_gt_three
  have hl : (0 : ℝ) < machinPiLower := by linarith
  exact_mod_cast hl

end ReciprocalXi
