import ProofWorkspace.Final.RationalPowerBoundsFull
import Mathlib.Data.Nat.Log

/-!
# Dyadic rational enclosures of actual real powers

Positive integer bases are reduced exactly using Nat.log2 to a mantissa in
[1,2). The proved logarithm series argument is then in [0,1/3), and verified
scaled exponential endpoints bound the actual real power for either sign
of the rational exponent.
-/

set_option autoImplicit false

namespace ReciprocalXi

def ratPowerDyadicLogLower (r q : ℚ) (d nLog : ℕ) : ℚ :=
  min (q * ratLogDyadicLower r d nLog) (q * ratLogDyadicUpper r d nLog)

def ratPowerDyadicLogUpper (r q : ℚ) (d nLog : ℕ) : ℚ :=
  max (q * ratLogDyadicLower r d nLog) (q * ratLogDyadicUpper r d nLog)

def ratPowerDyadicLower (r q : ℚ) (d nLog m nExp : ℕ) : ℚ :=
  ratExpScaledLower (ratPowerDyadicLogLower r q d nLog) m nExp

def ratPowerDyadicUpper (r q : ℚ) (d nLog m nExp : ℕ) : ℚ :=
  ratExpScaledUpper (ratPowerDyadicLogUpper r q d nLog) m nExp

theorem ratPowerDyadic_log_enclosure (r q : ℚ) (d nLog : ℕ) (hr : 0 < r) :
    (ratPowerDyadicLogLower r q d nLog : ℝ) ≤
        (q : ℝ) * Real.log (((2 : ℚ) ^ d * r : ℚ) : ℝ) ∧
      (q : ℝ) * Real.log (((2 : ℚ) ^ d * r : ℚ) : ℝ) ≤
        (ratPowerDyadicLogUpper r q d nLog : ℝ) := by
  have h := ratLog_dyadic_enclosure r d nLog hr
  unfold ratPowerDyadicLogLower ratPowerDyadicLogUpper
  push_cast at h ⊢
  rcases le_total (0 : ℝ) (q : ℝ) with hq | hq
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_left h.1 hq),
      (mul_le_mul_of_nonneg_left h.2 hq).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left h.2 hq),
      (mul_le_mul_of_nonpos_left h.1 hq).trans (le_max_left _ _)⟩

theorem ratPowerDyadic_enclosure (r q : ℚ) (d nLog m nExp : ℕ)
    (hr : 0 < r) (hm : 0 < m) (hn : 0 < nExp)
    (hl : |ratPowerDyadicLogLower r q d nLog / m| ≤ 1)
    (hu : |ratPowerDyadicLogUpper r q d nLog / m| ≤ 1) :
    (ratPowerDyadicLower r q d nLog m nExp : ℝ) ≤
        (((2 : ℚ) ^ d * r : ℚ) : ℝ) ^ (q : ℝ) ∧
      (((2 : ℚ) ^ d * r : ℚ) : ℝ) ^ (q : ℝ) ≤
        (ratPowerDyadicUpper r q d nLog m nExp : ℝ) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have ha : (0 : ℝ) < (((2 : ℚ) ^ d * r : ℚ) : ℝ) := by
    push_cast
    positivity
  have hp := ratPowerDyadic_log_enclosure r q d nLog hr
  have hlo := ratExp_scaled_enclosure (ratPowerDyadicLogLower r q d nLog) m nExp hm hn hl
  have hup := ratExp_scaled_enclosure (ratPowerDyadicLogUpper r q d nLog) m nExp hm hn hu
  rw [Real.rpow_def_of_pos ha, mul_comm (Real.log _)]
  exact ⟨hlo.1.trans (Real.exp_le_exp.mpr hp.1),
    (Real.exp_le_exp.mpr hp.2).trans hup.2⟩

def ratPowerNatMantissa (a : ℕ) : ℚ := (a : ℚ) / 2 ^ Nat.log2 a

def ratPowerNatLower (a : ℕ) (q : ℚ) (nLog m nExp : ℕ) : ℚ :=
  ratPowerDyadicLower (ratPowerNatMantissa a) q (Nat.log2 a) nLog m nExp

def ratPowerNatUpper (a : ℕ) (q : ℚ) (nLog m nExp : ℕ) : ℚ :=
  ratPowerDyadicUpper (ratPowerNatMantissa a) q (Nat.log2 a) nLog m nExp

theorem ratPowerNatMantissa_pos (a : ℕ) (ha : 0 < a) : 0 < ratPowerNatMantissa a := by
  unfold ratPowerNatMantissa
  positivity

theorem ratPowerNat_decomposition (a : ℕ) :
    (2 : ℚ) ^ Nat.log2 a * ratPowerNatMantissa a = a := by
  unfold ratPowerNatMantissa
  field_simp

theorem ratPowerNatMantissa_mem_Ico (a : ℕ) (ha : 0 < a) :
    ratPowerNatMantissa a ∈ Set.Ico (1 : ℚ) 2 := by
  have hd : (0 : ℚ) < 2 ^ Nat.log2 a := by positivity
  have hlo : (2 : ℚ) ^ Nat.log2 a ≤ (a : ℚ) := by
    exact_mod_cast Nat.log2_self_le (ne_of_gt ha)
  have hup : (a : ℚ) < (2 : ℚ) ^ (Nat.log2 a + 1) := by
    exact_mod_cast (Nat.lt_log2_self (n := a))
  unfold ratPowerNatMantissa
  constructor
  · exact (le_div_iff₀ hd).mpr (by simpa using hlo)
  · apply (div_lt_iff₀ hd).mpr
    simpa [pow_succ, mul_comm] using hup

theorem ratPowerNatMantissa_logArgument_mem_Ico (a : ℕ) (ha : 0 < a) :
    ratLogArgument (ratPowerNatMantissa a) ∈ Set.Ico (0 : ℚ) (1 / 3) := by
  have hr := ratPowerNatMantissa_mem_Ico a ha
  have hd : 0 < ratPowerNatMantissa a + 1 := by linarith [hr.1]
  unfold ratLogArgument
  constructor
  · exact div_nonneg (by linarith [hr.1]) hd.le
  · apply (div_lt_iff₀ hd).mpr
    linarith [hr.2]

/-- Positive integer bases are reduced exactly to a mantissa in [1,2),
so neither the base decomposition nor any transcendental value is assumed. -/
theorem ratPowerNat_enclosure (a : ℕ) (q : ℚ) (nLog m nExp : ℕ)
    (ha : 0 < a) (hm : 0 < m) (hn : 0 < nExp)
    (hl : |ratPowerDyadicLogLower (ratPowerNatMantissa a) q (Nat.log2 a) nLog / m| ≤ 1)
    (hu : |ratPowerDyadicLogUpper (ratPowerNatMantissa a) q (Nat.log2 a) nLog / m| ≤ 1) :
    (ratPowerNatLower a q nLog m nExp : ℝ) ≤ (a : ℝ) ^ (q : ℝ) ∧
      (a : ℝ) ^ (q : ℝ) ≤ (ratPowerNatUpper a q nLog m nExp : ℝ) := by
  have h := ratPowerDyadic_enclosure (ratPowerNatMantissa a) q (Nat.log2 a) nLog m nExp
    (ratPowerNatMantissa_pos a ha) hm hn hl hu
  rw [ratPowerNat_decomposition] at h
  simpa only [Rat.cast_natCast] using h

end ReciprocalXi
