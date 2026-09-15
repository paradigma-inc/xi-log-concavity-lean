import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

/-!
# Exact rational exponential enclosures

Rational Taylor endpoints are proved to enclose the actual real exponential.
The computations are mathematical witnesses checked by Lean's kernel, not
assumptions about the accuracy of an external floating-point implementation.
-/

namespace ReciprocalXi

def ratExpTaylor (q : ℚ) (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n, q ^ k / k.factorial

def ratExpError (q : ℚ) (n : ℕ) : ℚ :=
  |q| ^ n * (n + 1) / (n.factorial * n)

theorem ratExpTaylor_cast (q : ℚ) (n : ℕ) :
    (ratExpTaylor q n : ℝ) = ∑ k ∈ Finset.range n, (q : ℝ) ^ k / k.factorial := by
  unfold ratExpTaylor
  push_cast
  rfl

theorem ratExpError_cast (q : ℚ) (n : ℕ) :
    (ratExpError q n : ℝ) = |(q : ℝ)| ^ n * ((n + 1) / (n.factorial * n)) := by
  unfold ratExpError
  push_cast
  ring

theorem ratExpTaylor_error (q : ℚ) (n : ℕ) (hq : |q| ≤ 1) (hn : 0 < n) :
    |Real.exp (q : ℝ) - (ratExpTaylor q n : ℝ)| ≤ (ratExpError q n : ℝ) := by
  have hq' : |(q : ℝ)| ≤ 1 := by exact_mod_cast hq
  have h := Real.exp_bound hq' hn
  rw [ratExpTaylor_cast, ratExpError_cast]
  simpa only [Nat.cast_succ] using h

/-- Exact rational lower and upper endpoints, with proved analytic meaning. -/
theorem ratExp_enclosure (q : ℚ) (n : ℕ) (hq : |q| ≤ 1) (hn : 0 < n) :
    ((ratExpTaylor q n - ratExpError q n : ℚ) : ℝ) ≤ Real.exp (q : ℝ) ∧
      Real.exp (q : ℝ) ≤ ((ratExpTaylor q n + ratExpError q n : ℚ) : ℝ) := by
  have h := abs_le.mp (ratExpTaylor_error q n hq hn)
  push_cast
  constructor <;> linarith

/-- Monotonicity turns endpoint checks into an enclosure for a whole interval. -/
theorem ratExp_interval_enclosure (a b : ℚ) (x : ℝ) (n : ℕ)
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hn : 0 < n) (hax : (a : ℝ) ≤ x) (hxb : x ≤ (b : ℝ)) :
    ((ratExpTaylor a n - ratExpError a n : ℚ) : ℝ) ≤ Real.exp x ∧
      Real.exp x ≤ ((ratExpTaylor b n + ratExpError b n : ℚ) : ℝ) :=
  ⟨(ratExp_enclosure a n ha hn).1.trans (Real.exp_le_exp.mpr hax),
    (Real.exp_le_exp.mpr hxb).trans (ratExp_enclosure b n hb hn).2⟩

def ratExpScaledLower (q : ℚ) (m n : ℕ) : ℚ :=
  (max 0 (ratExpTaylor (q / m) n - ratExpError (q / m) n)) ^ m

def ratExpScaledUpper (q : ℚ) (m n : ℕ) : ℚ :=
  (ratExpTaylor (q / m) n + ratExpError (q / m) n) ^ m

/-- Exact range reduction extends the evaluator beyond the unit interval.
Clamping the lower endpoint to zero makes powering sound even at low order. -/
theorem ratExp_scaled_enclosure (q : ℚ) (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hq : |q / m| ≤ 1) :
    (ratExpScaledLower q m n : ℝ) ≤ Real.exp (q : ℝ) ∧
      Real.exp (q : ℝ) ≤ (ratExpScaledUpper q m n : ℝ) := by
  have h := ratExp_enclosure (q / m) n hq hn
  have hl : max (0 : ℝ) ((ratExpTaylor (q / m) n - ratExpError (q / m) n : ℚ) : ℝ) ≤
      Real.exp ((q / m : ℚ) : ℝ) := max_le (Real.exp_pos _).le h.1
  have hlp := pow_le_pow_left₀ (le_max_left (0 : ℝ) _) hl m
  have hup := pow_le_pow_left₀ (Real.exp_pos _).le h.2 m
  have he : Real.exp ((q / m : ℚ) : ℝ) ^ m = Real.exp (q : ℝ) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hm)
    field_simp
  rw [he] at hlp hup
  push_cast at hlp hup
  unfold ratExpScaledLower ratExpScaledUpper
  push_cast
  exact ⟨hlp, hup⟩

/-- A concrete eight-decimal enclosure of exp(1/2), with exact rational
Taylor arithmetic rather than an external numerical receipt. -/
theorem exp_half_certified :
    (164872127 : ℝ) / 100000000 ≤ Real.exp (1 / 2) ∧
      Real.exp (1 / 2) ≤ (164872128 : ℝ) / 100000000 := by
  have h := ratExp_enclosure (1 / 2) 12 (by norm_num) (by norm_num)
  norm_num [ratExpTaylor, ratExpError, Finset.sum_range_succ, Nat.factorial] at h
  constructor <;> linarith [h.1, h.2]

end ReciprocalXi
