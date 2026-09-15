import ProofWorkspace.Final.PiBoundsFull
import Mathlib.Tactic

namespace ReciprocalXi

/-- The exact rational midpoint used by the compact-certificate generator.

The source script first builds a directed 160-digit Decimal interval for pi,
then computes `(lo + hi) / 2` under ROUND_HALF_EVEN.  This literal is the
resulting rounded decimal, represented exactly as a rational.
-/
def sourcePiMidpoint : ℚ :=
  (3141592653589793238462643383279502884197169399375105820974944592307816406286208998628034825342117067982148086513282306647093844609550582231725359408128481117446 : ℚ) /
    (10 : ℚ) ^ 159

theorem sourcePiMidpoint_ge_three : (3 : ℚ) ≤ sourcePiMidpoint := by
  norm_num [sourcePiMidpoint]

theorem sourcePiMidpoint_close_to_machin_midpoint :
    |sourcePiMidpoint - machinPiMidpoint| ≤ 1 / (10 : ℚ) ^ 151 := by
  norm_num [sourcePiMidpoint, machinPiMidpoint, ratArctanTaylor,
    Finset.sum_range_succ, div_pow, pow_succ]

theorem sourcePiMidpoint_error :
    |(sourcePiMidpoint : ℝ) - Real.pi| ≤ (1 : ℝ) / (10 : ℝ) ^ 150 := by
  have hpi := machinPi_error
  have hpm := sourcePiMidpoint_close_to_machin_midpoint
  have hpm' : |(sourcePiMidpoint : ℝ) - (machinPiMidpoint : ℝ)| ≤
      (1 : ℝ) / (10 : ℝ) ^ 151 := by
    have hpm0 : ((|sourcePiMidpoint - machinPiMidpoint| : ℚ) : ℝ) ≤
        ((1 / (10 : ℚ) ^ 151 : ℚ) : ℝ) := by
      exact_mod_cast hpm
    simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_div, Rat.cast_one,
      Rat.cast_pow] using hpm0
  have hpi' : |(machinPiMidpoint : ℝ) - Real.pi| ≤
      (machinPiRadius : ℝ) := by
    simpa [abs_sub_comm] using hpi
  have hrad : (machinPiRadius : ℝ) < (1 : ℝ) / (10 : ℝ) ^ 160 := by
    have h := machinPi_width_lt
    have h' : ((machinPiUpper : ℝ) - (machinPiLower : ℝ)) <
        (1 : ℝ) / (10 : ℝ) ^ 160 := by
      have h0 : ((machinPiUpper - machinPiLower : ℚ) : ℝ) <
          ((1 / (10 : ℚ) ^ 160 : ℚ) : ℝ) := by
        exact_mod_cast h
      simpa only [Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_pow]
        using h0
    rw [show (machinPiRadius : ℝ) =
        ((machinPiUpper : ℝ) - (machinPiLower : ℝ)) / 2 by
          simp [machinPiUpper, machinPiLower, machinPiRadius]]
    linarith
  calc
    |(sourcePiMidpoint : ℝ) - Real.pi| ≤
        |(sourcePiMidpoint : ℝ) - (machinPiMidpoint : ℝ)| +
          |(machinPiMidpoint : ℝ) - Real.pi| := by
      rw [show (sourcePiMidpoint : ℝ) - Real.pi =
        ((sourcePiMidpoint : ℝ) - (machinPiMidpoint : ℝ)) +
          ((machinPiMidpoint : ℝ) - Real.pi) by ring]
      exact abs_add_le _ _
    _ ≤ (1 : ℝ) / (10 : ℝ) ^ 151 + (machinPiRadius : ℝ) :=
      add_le_add hpm' hpi'
    _ ≤ (1 : ℝ) / (10 : ℝ) ^ 150 := by
      norm_num at hrad ⊢
      linarith

end ReciprocalXi
