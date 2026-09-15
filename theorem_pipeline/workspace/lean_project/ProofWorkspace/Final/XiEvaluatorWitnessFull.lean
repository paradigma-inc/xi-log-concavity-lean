import ProofWorkspace.Final.RationalXiBoundsFull

/-!
# A finite kernel-checked witness for the complete Xi evaluator

This intentionally coarse nonremovable-node witness checks every rational
side condition and endpoint inequality. It is not a high-precision source-node
certificate. No runtime-only evaluation is used in its proof.
-/

set_option autoImplicit false

namespace ReciprocalXi

private theorem xiTwo_log2_one : Nat.log2 1 = 0 := by
  apply (Nat.log2_eq_iff (by decide : (1 : ℕ) ≠ 0)).mpr
  norm_num

private theorem xiTwo_log2_three : Nat.log2 3 = 1 := by
  apply (Nat.log2_eq_iff (by decide : (3 : ℕ) ≠ 0)).mpr
  norm_num

private theorem xiTwo_log2_four : Nat.log2 4 = 2 := by
  apply (Nat.log2_eq_iff (by decide : (4 : ℕ) ≠ 0)).mpr
  norm_num

def xiTwoWitnessParams : XiEvalParams := ⟨4, 4, 8, 3, 4, 8⟩

local macro "xi_two_norm" : tactic => `(tactic| norm_num [xiTwoWitnessParams,
  ratXiGridLower, ratXiGridUpper, xiGridArgument, ratXiBracketLower, ratXiBracketUpper,
  ratXiDenominatorLower, ratXiDenominatorUpper, ratGammaGridLower, ratGammaGridUpper,
  gammaGridOffset, gammaGridBase, gammaGridMultiplier, gammaGridArgument,
  ratGammaShiftProduct, ratGammaLower, ratGammaUpper, ratLogGammaLower, ratLogGammaUpper,
  ratLogGammaCenter, ratLogGammaRadius, ratGammaLogSeries, ratGammaLogSeriesError,
  ratGammaLogCoefficient, ratGammaPiLogCenter, ratGammaPiLogRadius,
  ratGammaPiLogLower, ratGammaPiLogUpper, machinPiLower, machinPiUpper,
  machinPiMidpoint, machinPiRadius, ratArctanTaylor, ratArctanError,
  ratPiPowerLower, ratPiPowerUpper, ratPiPowerLogLower, ratPiPowerLogUpper,
  ratPowerLower, ratPowerUpper, ratPowerLogLower, ratPowerLogUpper,
  ratEtaNatLower, ratEtaNatUpper, ratEtaNatTermLower, ratEtaNatTermUpper,
  ratEtaCoefficient, ratEtaEulerWeight, ratZetaNatLower, ratZetaNatFactor,
  ratEtaNatSum, ratPowerNatLower, ratPowerNatUpper, ratPowerDyadicLower,
  ratPowerDyadicUpper, ratPowerDyadicLogLower, ratPowerDyadicLogUpper,
  ratPowerNatMantissa, ratLogDyadicLower, ratLogDyadicUpper,
  ratLogTaylor, ratLogError, ratLogArgument, ratExpScaledLower,
  ratExpScaledUpper, ratExpTaylor, ratExpError, Finset.sum_range_succ,
  Finset.prod_range_succ, Finset.sum_filter, Nat.choose_succ_succ, Nat.factorial, xiTwo_log2_one, xiTwo_log2_three,
  xiTwo_log2_four])

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
set_option exponentiation.threshold 512 in
theorem xiTwoWitnessChecks : XiEvalChecks 120 xiTwoWitnessParams := by
  constructor
  · xi_two_norm
  · xi_two_norm
  · xi_two_norm
  · xi_two_norm
  · xi_two_norm
  · xi_two_norm
  · intro j hj
    have hj' : j < 4 := Finset.mem_range.mp hj
    interval_cases j <;> xi_two_norm
  · intro j hj
    have hj' : j < 4 := Finset.mem_range.mp hj
    interval_cases j <;> xi_two_norm
  · xi_two_norm
  · xi_two_norm
  · xi_two_norm

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
set_option exponentiation.threshold 512 in
theorem xiTwoWitnessEndpoints : (1 / 4 : ℚ) < ratXiGridLower 120 xiTwoWitnessParams ∧
    ratXiGridUpper 120 xiTwoWitnessParams < 1 := by
  constructor <;> xi_two_norm

/-- A finite kernel-checked use of the complete evaluator at a nonremovable node. -/
theorem xi_two_rational_evaluator_witness :
    (1 / 4 : ℝ) < (xi (2 : ℂ)).re ∧ (xi (2 : ℂ)).re < 1 := by
  have h := ratXiGrid_enclosure 120 xiTwoWitnessParams (fun _ => xiTwoWitnessChecks)
  norm_num only [xiGridArgument, Rat.cast_div, Rat.cast_add, Rat.cast_natCast,
    Rat.cast_ofNat] at h
  have hl : (1 / 4 : ℝ) < (ratXiGridLower 120 xiTwoWitnessParams : ℝ) := by
    have hc := (Rat.cast_lt (K := ℝ)).mpr xiTwoWitnessEndpoints.1
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hc
    exact hc
  have hu : (ratXiGridUpper 120 xiTwoWitnessParams : ℝ) < 1 := by
    exact_mod_cast xiTwoWitnessEndpoints.2
  exact ⟨hl.trans_le h.1, h.2.trans_lt hu⟩

end ReciprocalXi

