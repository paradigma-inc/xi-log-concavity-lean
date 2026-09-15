import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic

/-!
# Sound outward rounding on an exact rational grid

Floor and ceiling produce lower and upper rational endpoints on a fixed
positive integer scale. Actual-real enclosure, interval preservation,
nonnegativity, grid membership, and a one-cell singleton width are proved.
-/

set_option autoImplicit false

namespace ReciprocalXi

def ratRoundLower (q : ℚ) (B : ℕ) : ℚ := (Int.floor ((B : ℚ) * q) : ℚ) / B
def ratRoundUpper (q : ℚ) (B : ℕ) : ℚ := (Int.ceil ((B : ℚ) * q) : ℚ) / B

theorem ratRound_enclosure (q : ℚ) (B : ℕ) (hB : 0 < B) :
    ratRoundLower q B ≤ q ∧ q ≤ ratRoundUpper q B := by
  have hB' : (0 : ℚ) < B := by exact_mod_cast hB
  unfold ratRoundLower ratRoundUpper
  constructor
  · apply (div_le_iff₀ hB').mpr
    simpa only [mul_comm] using Int.floor_le ((B : ℚ) * q)
  · apply (le_div_iff₀ hB').mpr
    simpa only [mul_comm] using Int.le_ceil ((B : ℚ) * q)

theorem ratRound_real_enclosure (q : ℚ) (B : ℕ) (hB : 0 < B) :
    (ratRoundLower q B : ℝ) ≤ (q : ℝ) ∧ (q : ℝ) ≤ (ratRoundUpper q B : ℝ) := by
  exact ⟨(Rat.cast_le (K := ℝ)).mpr (ratRound_enclosure q B hB).1,
    (Rat.cast_le (K := ℝ)).mpr (ratRound_enclosure q B hB).2⟩

theorem ratRound_interval_enclosure (a b : ℚ) (x : ℝ) (B : ℕ) (hB : 0 < B)
    (hax : (a : ℝ) ≤ x) (hxb : x ≤ (b : ℝ)) :
    (ratRoundLower a B : ℝ) ≤ x ∧ x ≤ (ratRoundUpper b B : ℝ) :=
  ⟨(ratRound_real_enclosure a B hB).1.trans hax,
    hxb.trans (ratRound_real_enclosure b B hB).2⟩

theorem ratRoundLower_nonneg (q : ℚ) (B : ℕ) (hq : 0 ≤ q) : 0 ≤ ratRoundLower q B := by
  unfold ratRoundLower
  apply div_nonneg _ (Nat.cast_nonneg B)
  exact_mod_cast (Int.floor_nonneg.mpr (mul_nonneg (Nat.cast_nonneg B) hq))

theorem ratRoundUpper_nonneg (q : ℚ) (B : ℕ) (hq : 0 ≤ q) : 0 ≤ ratRoundUpper q B := by
  unfold ratRoundUpper
  apply div_nonneg _ (Nat.cast_nonneg B)
  exact_mod_cast (Int.ceil_nonneg (mul_nonneg (Nat.cast_nonneg B) hq))

/-- Rounding a singleton increases its width by at most one grid cell. -/
theorem ratRound_width_le (q : ℚ) (B : ℕ) (hB : 0 < B) :
    ratRoundUpper q B - ratRoundLower q B ≤ 1 / (B : ℚ) := by
  have hB' : (0 : ℚ) < B := by exact_mod_cast hB
  have hi := Int.ceil_le_floor_add_one ((B : ℚ) * q)
  have hi' : (Int.ceil ((B : ℚ) * q) : ℚ) ≤ (Int.floor ((B : ℚ) * q) : ℚ) + 1 := by
    exact_mod_cast hi
  unfold ratRoundUpper ratRoundLower
  rw [← sub_div]
  exact (div_le_div_iff_of_pos_right hB').mpr (by linarith)

theorem ratRound_width_nonneg (q : ℚ) (B : ℕ) (hB : 0 < B) :
    0 ≤ ratRoundUpper q B - ratRoundLower q B := by
  have h := ratRound_enclosure q B hB
  linarith [h.1, h.2]

theorem ratRound_mem_grid (q : ℚ) (B : ℕ) (hB : 0 < B) :
    ∃ l u : ℤ, (B : ℚ) * ratRoundLower q B = l ∧
      (B : ℚ) * ratRoundUpper q B = u := by
  refine ⟨Int.floor ((B : ℚ) * q), Int.ceil ((B : ℚ) * q), ?_, ?_⟩ <;>
    simp [ratRoundLower, ratRoundUpper, ne_of_gt hB, mul_div_cancel₀]

/-- Existing grid points are preserved exactly, including negative ones. -/
theorem ratRound_grid_exact (k : ℤ) (B : ℕ) (hB : 0 < B) :
    ratRoundLower ((k : ℚ) / B) B = (k : ℚ) / B ∧
      ratRoundUpper ((k : ℚ) / B) B = (k : ℚ) / B := by
  have hB' : (B : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hB
  have he : (B : ℚ) * ((k : ℚ) / B) = (k : ℚ) := by field_simp
  simp [ratRoundLower, ratRoundUpper, he]

end ReciprocalXi
