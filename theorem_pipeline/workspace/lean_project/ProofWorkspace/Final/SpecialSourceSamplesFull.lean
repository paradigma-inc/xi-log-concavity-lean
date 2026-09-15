import ProofWorkspace.Final.FirstSourceNodeCertificateFull
import ProofWorkspace.Final.CosineQuadratureFull

set_option autoImplicit false
set_option maxRecDepth 32768
noncomputable section
namespace ReciprocalXi

theorem xiCentral_certified_candidate_enclosure :
    (candidateXiZeroValues.1:ℝ) ≤ (xi (1/2)).re ∧
      (xi (1/2)).re ≤ (candidateXiZeroValues.2:ℝ) := by
  have he := candidateXiZero_eq_grid (candidateGammaZero_eq_grid gammaNodeZero_fast_literals)
  have hl := congrArg Prod.fst he
  have hu := congrArg Prod.snd he
  dsimp only at hl hu
  have h := ratXiRootGrid_enclosure 0 firstNodeParams firstNodeGrid rootLowerFor rootUpperFor
    (fun _ => firstNode_zero_root_eval_checks)
  rw [hl, hu, candidateXiZero_literals] at h
  norm_num only [xiGridArgument, Nat.cast_zero, zero_add] at h
  norm_num at h ⊢
  exact h

theorem reciprocalTransform_at_one_re :
    (reciprocalTransform 1).re = 2*(xi (1/2)).re := by
  have h := reciprocalTransform_grid_re 40
  norm_num [xiGridArgument, xi_one] at h
  convert h using 1; ring

theorem reciprocalTransform_one_certified_enclosure :
    2*(candidateXiZeroValues.1:ℝ) ≤ (reciprocalTransform 1).re ∧
      (reciprocalTransform 1).re ≤ 2*(candidateXiZeroValues.2:ℝ) := by
  rw [reciprocalTransform_at_one_re]
  constructor
  · exact mul_le_mul_of_nonneg_left xiCentral_certified_candidate_enclosure.1 (by norm_num)
  · exact mul_le_mul_of_nonneg_left xiCentral_certified_candidate_enclosure.2 (by norm_num)

def sourceNodeFortyRoundedMidpoint : ℚ :=
  9942415563766282198255474793707954396145872191154103718664684679969910580910869704783399299567762869806383920997857747120214465513788531988194803670084998456945 / (10:ℚ)^160

theorem sourceNodeForty_candidate_precision :
    sourceNodeFortyRoundedMidpoint-2/(10:ℚ)^120 ≤ 2*candidateXiZeroValues.1 ∧
      2*candidateXiZeroValues.2 ≤ sourceNodeFortyRoundedMidpoint+2/(10:ℚ)^120 := by
  decide +kernel

theorem source_node_forty_rounded_midpoint_bound :
    |(reciprocalTransform 1).re-(sourceNodeFortyRoundedMidpoint:ℝ)| ≤ 2/(10:ℝ)^120 := by
  have hp := sourceNodeForty_candidate_precision
  have hl : ((sourceNodeFortyRoundedMidpoint-2/(10:ℚ)^120:ℚ):ℝ) ≤
      ((2*candidateXiZeroValues.1:ℚ):ℝ) := Rat.cast_le.mpr hp.1
  have hu : ((2*candidateXiZeroValues.2:ℚ):ℝ) ≤
      ((sourceNodeFortyRoundedMidpoint+2/(10:ℚ)^120:ℚ):ℝ) := Rat.cast_le.mpr hp.2
  push_cast at hl hu
  have h := reciprocalTransform_one_certified_enclosure
  rw [abs_le]
  constructor <;> linarith [h.1,h.2]

theorem source_node_zero_midpoint_bound :
    |(reciprocalTransform 0).re-1| ≤ 2/(10:ℝ)^120 := by
  rw [reciprocalTransform_zero]
  norm_num

end ReciprocalXi

