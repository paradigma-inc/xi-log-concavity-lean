import ProofWorkspace.Final.RationalRoundingBoundsFull
import ProofWorkspace.Final.RationalExpBoundsFull

/-!
# Rounded nonnegative powers and actual scaled exponentials

Induction proves that fixed-grid rounding after every multiplication
preserves the enclosure of an actual nonnegative power. Applying this to
the proved Taylor interval yields actual exponential enclosures with
rounded initial endpoints and rounded stored powering products.
-/

set_option autoImplicit false

namespace ReciprocalXi

def ratPowRoundLower (a : ℚ) (B : ℕ) : ℕ → ℚ
  | 0 => 1
  | n + 1 => ratRoundLower (ratPowRoundLower a B n * a) B

def ratPowRoundUpper (a : ℚ) (B : ℕ) : ℕ → ℚ
  | 0 => 1
  | n + 1 => ratRoundUpper (ratPowRoundUpper a B n * a) B

theorem ratPowRoundLower_nonneg (a : ℚ) (B n : ℕ) (ha : 0 ≤ a) :
    0 ≤ ratPowRoundLower a B n := by
  induction n with
  | zero => simp [ratPowRoundLower]
  | succ n ih => exact ratRoundLower_nonneg _ B (mul_nonneg ih ha)

theorem ratPowRoundUpper_nonneg (a : ℚ) (B n : ℕ) (ha : 0 ≤ a) :
    0 ≤ ratPowRoundUpper a B n := by
  induction n with
  | zero => simp [ratPowRoundUpper]
  | succ n ih => exact ratRoundUpper_nonneg _ B (mul_nonneg ih ha)

/-- Outward rounding after every product preserves an interval enclosing
the actual nonnegative real power. -/
theorem ratPowRound_enclosure (a b : ℚ) (x : ℝ) (B n : ℕ)
    (hB : 0 < B) (ha : 0 ≤ a) (hax : (a : ℝ) ≤ x) (hxb : x ≤ (b : ℝ)) :
    (ratPowRoundLower a B n : ℝ) ≤ x ^ n ∧ x ^ n ≤ (ratPowRoundUpper b B n : ℝ) := by
  have ha' : (0 : ℝ) ≤ a := by exact_mod_cast ha
  have hx : 0 ≤ x := ha'.trans hax
  have hb : 0 ≤ b := by exact_mod_cast hx.trans hxb
  induction n with
  | zero => simp [ratPowRoundLower, ratPowRoundUpper]
  | succ n ih =>
    have hl := (ratRound_real_enclosure (ratPowRoundLower a B n * a) B hB).1
    have hu := (ratRound_real_enclosure (ratPowRoundUpper b B n * b) B hB).2
    have hu0 : (0 : ℝ) ≤ ratPowRoundUpper b B n := by
      exact_mod_cast ratPowRoundUpper_nonneg b B n hb
    push_cast at hl hu
    constructor
    · have hmul : (ratPowRoundLower a B n : ℝ) * (a : ℝ) ≤ x ^ (n + 1) := by
        simpa only [pow_succ] using mul_le_mul ih.1 hax ha' (pow_nonneg hx n)
      exact hl.trans hmul
    · have hmul : x ^ (n + 1) ≤ (ratPowRoundUpper b B n : ℝ) * (b : ℝ) := by
        simpa only [pow_succ] using mul_le_mul ih.2 hxb hx hu0
      exact hmul.trans hu

theorem ratPowRound_mem_grid (a : ℚ) (B n : ℕ) (hB : 0 < B) :
    ∃ l u : ℤ, (B : ℚ) * ratPowRoundLower a B n = l ∧
      (B : ℚ) * ratPowRoundUpper a B n = u := by
  cases n with
  | zero => exact ⟨B, B, by simp [ratPowRoundLower], by simp [ratPowRoundUpper]⟩
  | succ n =>
    obtain ⟨l, u, hl, hu⟩ := ratRound_mem_grid (ratPowRoundLower a B n * a) B hB
    obtain ⟨l', u', hl', hu'⟩ := ratRound_mem_grid (ratPowRoundUpper a B n * a) B hB
    exact ⟨l, u', hl, hu'⟩

def ratExpRoundedLower (q : ℚ) (m n B : ℕ) : ℚ :=
  ratPowRoundLower
    (ratRoundLower (max 0 (ratExpTaylor (q / m) n - ratExpError (q / m) n)) B) B m

def ratExpRoundedUpper (q : ℚ) (m n B : ℕ) : ℚ :=
  ratPowRoundUpper
    (ratRoundUpper (ratExpTaylor (q / m) n + ratExpError (q / m) n) B) B m

/-- Scaled exponential evaluation with a fixed-denominator rounding after
each powering product. The enclosure is for the actual exponential. -/
theorem ratExpRounded_enclosure (q : ℚ) (m n B : ℕ)
    (hm : 0 < m) (hn : 0 < n) (hB : 0 < B) (hq : |q / m| ≤ 1) :
    (ratExpRoundedLower q m n B : ℝ) ≤ Real.exp (q : ℝ) ∧
      Real.exp (q : ℝ) ≤ (ratExpRoundedUpper q m n B : ℝ) := by
  have h := ratExp_enclosure (q / m) n hq hn
  have hl : ((max 0 (ratExpTaylor (q / m) n - ratExpError (q / m) n) : ℚ) : ℝ) ≤
      Real.exp ((q / m : ℚ) : ℝ) := by
    simp only [Rat.cast_max, Rat.cast_zero]
    exact max_le (Real.exp_pos _).le h.1
  have hp := ratPowRound_enclosure
    (ratRoundLower (max 0 (ratExpTaylor (q / m) n - ratExpError (q / m) n)) B)
    (ratRoundUpper (ratExpTaylor (q / m) n + ratExpError (q / m) n) B)
    (Real.exp ((q / m : ℚ) : ℝ)) B m hB
    (ratRoundLower_nonneg _ B (le_max_left _ _))
    ((ratRound_real_enclosure _ B hB).1.trans hl)
    (h.2.trans (ratRound_real_enclosure _ B hB).2)
  have he : Real.exp ((q / m : ℚ) : ℝ) ^ m = Real.exp (q : ℝ) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hm
    field_simp
  rw [he] at hp
  exact hp

end ReciprocalXi
