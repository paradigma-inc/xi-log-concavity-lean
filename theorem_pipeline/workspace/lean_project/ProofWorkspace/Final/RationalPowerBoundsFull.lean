import ProofWorkspace.Final.RationalLogBoundsFull
import ProofWorkspace.Final.RationalExpBoundsFull
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Exact rational enclosures of real powers

The actual value a^r is bounded by composing proved logarithm and exponential
enclosures. Both signs of the rational exponent are covered; all endpoint
computations and range preconditions use exact rational arithmetic.
-/

namespace ReciprocalXi

def ratPowerLogLower (a r : ℚ) (nLog : ℕ) : ℚ :=
  min (r * (ratLogTaylor a nLog - ratLogError a nLog))
    (r * (ratLogTaylor a nLog + ratLogError a nLog))

def ratPowerLogUpper (a r : ℚ) (nLog : ℕ) : ℚ :=
  max (r * (ratLogTaylor a nLog - ratLogError a nLog))
    (r * (ratLogTaylor a nLog + ratLogError a nLog))

def ratPowerLower (a r : ℚ) (nLog m nExp : ℕ) : ℚ :=
  ratExpScaledLower (ratPowerLogLower a r nLog) m nExp

def ratPowerUpper (a r : ℚ) (nLog m nExp : ℕ) : ℚ :=
  ratExpScaledUpper (ratPowerLogUpper a r nLog) m nExp

/-- Multiplication of a certified logarithm interval is sound for either
sign of the rational exponent. -/
theorem ratPower_log_enclosure (a r : ℚ) (nLog : ℕ) (ha : 0 < a) :
    (ratPowerLogLower a r nLog : ℝ) ≤ (r : ℝ) * Real.log (a : ℝ) ∧
      (r : ℝ) * Real.log (a : ℝ) ≤ (ratPowerLogUpper a r nLog : ℝ) := by
  have h := ratLog_enclosure a nLog ha
  unfold ratPowerLogLower ratPowerLogUpper
  push_cast at h ⊢
  rcases le_total (0 : ℝ) (r : ℝ) with hr | hr
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_left h.1 hr),
      (mul_le_mul_of_nonneg_left h.2 hr).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left h.2 hr),
      (mul_le_mul_of_nonpos_left h.1 hr).trans (le_max_left _ _)⟩

/-- The computed rational endpoints bound the actual real power. All
analytic error bounds come from the proved logarithm and exponential series. -/
theorem ratPower_enclosure (a r : ℚ) (nLog m nExp : ℕ)
    (ha : 0 < a) (hm : 0 < m) (hn : 0 < nExp)
    (hl : |ratPowerLogLower a r nLog / m| ≤ 1)
    (hu : |ratPowerLogUpper a r nLog / m| ≤ 1) :
    (ratPowerLower a r nLog m nExp : ℝ) ≤ (a : ℝ) ^ (r : ℝ) ∧
      (a : ℝ) ^ (r : ℝ) ≤ (ratPowerUpper a r nLog m nExp : ℝ) := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hp := ratPower_log_enclosure a r nLog ha
  have hlo := ratExp_scaled_enclosure (ratPowerLogLower a r nLog) m nExp hm hn hl
  have hup := ratExp_scaled_enclosure (ratPowerLogUpper a r nLog) m nExp hm hn hu
  rw [Real.rpow_def_of_pos ha', mul_comm (Real.log (a : ℝ))]
  exact ⟨hlo.1.trans (Real.exp_le_exp.mpr hp.1),
    (Real.exp_le_exp.mpr hp.2).trans hup.2⟩

/-- A negative, noninteger exponent exercises sign reversal in the
logarithm interval. The numerical inequalities are exact rational checks. -/
theorem negative_third_power_certified :
    (87 : ℝ) / 100 < (3 / 2 : ℝ) ^ (-1 / 3 : ℝ) ∧
      (3 / 2 : ℝ) ^ (-1 / 3 : ℝ) < (88 : ℝ) / 100 := by
  have hl : |ratPowerLogLower (3 / 2) (-1 / 3) 4 / 1| ≤ 1 := by
    norm_num [ratPowerLogLower, ratLogTaylor, ratLogError, ratLogArgument,
      Finset.sum_range_succ]
  have hu : |ratPowerLogUpper (3 / 2) (-1 / 3) 4 / 1| ≤ 1 := by
    norm_num [ratPowerLogUpper, ratLogTaylor, ratLogError, ratLogArgument,
      Finset.sum_range_succ]
  have h := ratPower_enclosure (3 / 2) (-1 / 3) 4 1 6 (by norm_num)
    (by norm_num) (by norm_num) hl hu
  have hlo : (87 : ℚ) / 100 < ratPowerLower (3 / 2) (-1 / 3) 4 1 6 := by
    norm_num [ratPowerLower, ratPowerLogLower, ratLogTaylor, ratLogError,
      ratLogArgument, ratExpScaledLower, ratExpTaylor, ratExpError,
      Finset.sum_range_succ, Nat.factorial]
  have hup : ratPowerUpper (3 / 2) (-1 / 3) 4 1 6 < (88 : ℚ) / 100 := by
    norm_num [ratPowerUpper, ratPowerLogUpper, ratLogTaylor, ratLogError,
      ratLogArgument, ratExpScaledUpper, ratExpTaylor, ratExpError,
      Finset.sum_range_succ, Nat.factorial]
  have hlo' : (87 : ℝ) / 100 < (ratPowerLower (3 / 2) (-1 / 3) 4 1 6 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using
      (Rat.cast_lt (K := ℝ)).mpr hlo
  have hup' : (ratPowerUpper (3 / 2) (-1 / 3) 4 1 6 : ℝ) < (88 : ℝ) / 100 := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using
      (Rat.cast_lt (K := ℝ)).mpr hup
  have hh := And.intro (hlo'.trans_le h.1) (h.2.trans_lt hup')
  convert hh using 1 <;> norm_num

end ReciprocalXi
