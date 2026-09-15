import ProofWorkspace.Final.RootXiGridBoundsFull
import ProofWorkspace.Final.RootPowerCertificateFull
import ProofWorkspace.Final.GammaRangeBoundsFull

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option exponentiation.threshold 1024

namespace ReciprocalXi

def firstNodeParams : XiEvalParams := ⟨400,440,480,400,256,128⟩
def firstNodeGrid : ℕ := 10^180

def sourceNodeOneLower : ℚ := 9999963898517960833946621412607506741893577633363160005099374613160132073516210730246211562525824302392320533376661936335402958728657632039607742509794756674229 / 10^160
def sourceNodeOneUpper : ℚ := 9999963898517960833946621412607506741893577633363160005099374613160132073516210730246211562525824302392320533376661936348181600028997943405671283798803563332806 / 10^160
def sourceNodeOneMidpoint : ℚ := (sourceNodeOneLower + sourceNodeOneUpper) / 2

theorem firstNode_root_checks :
    ∀ j ∈ Finset.range firstNodeParams.etaTerms,
      0 ≤ rootLowerFor (j+1) ∧ 0 ≤ rootUpperFor (j+1) ∧
      ((j:ℚ)+1)*(rootLowerFor (j+1))^80 ≤ 1 ∧
      1 ≤ ((j:ℚ)+1)*(rootUpperFor (j+1))^80 := by
  intro j hj
  have hjlt : j < 400 := Finset.mem_range.mp hj
  simpa only [Nat.cast_add, Nat.cast_one] using rootPowerGridBounds (j+1)
    (by omega) (by omega)

theorem firstNode_gamma_checks (k : ℕ) :
    |ratLogGammaFastLower (gammaGridOffset k) 440 480 400 firstNodeGrid / 256| ≤ 1 ∧
    |ratLogGammaFastUpper (gammaGridOffset k) 440 480 400 firstNodeGrid / 256| ≤ 1 :=
  ratLogGammaFast_scaled_checks (gammaGridOffset k) 440 480 400 firstNodeGrid 256
    (gammaGridOffset_bounds k) (by norm_num [firstNodeGrid])
    (by norm_num [firstNodeGrid]) (by norm_num [firstNodeGrid])
    (by norm_num [firstNodeGrid]) (by norm_num)

theorem firstNode_zero_denominator_pos :
    0 < ratXiRoundedDenominatorLower (xiGridArgument 0) 400 256 128 firstNodeGrid := by
  decide +kernel

theorem firstNode_one_denominator_pos :
    0 < ratXiRoundedDenominatorLower (xiGridArgument 1) 400 256 128 firstNodeGrid := by
  decide +kernel

theorem firstNode_zero_pi_checks :
    |ratPiPowerLogFastLower (-xiGridArgument 0 / 2) 400 firstNodeGrid / 256| ≤ 1 ∧
    |ratPiPowerLogFastUpper (-xiGridArgument 0 / 2) 400 firstNodeGrid / 256| ≤ 1 := by
  decide +kernel

theorem firstNode_one_pi_checks :
    |ratPiPowerLogFastLower (-xiGridArgument 1 / 2) 400 firstNodeGrid / 256| ≤ 1 ∧
    |ratPiPowerLogFastUpper (-xiGridArgument 1 / 2) 400 firstNodeGrid / 256| ≤ 1 := by
  decide +kernel

theorem firstNode_zero_two_checks :
    |ratPowerDyadicLogLower (ratPowerNatMantissa 2) (1-xiGridArgument 0)
      (Nat.log2 2) 400 / 256| ≤ 1 ∧
    |ratPowerDyadicLogUpper (ratPowerNatMantissa 2) (1-xiGridArgument 0)
      (Nat.log2 2) 400 / 256| ≤ 1 := by
  decide +kernel

theorem firstNode_one_two_checks :
    |ratPowerDyadicLogLower (ratPowerNatMantissa 2) (1-xiGridArgument 1)
      (Nat.log2 2) 400 / 256| ≤ 1 ∧
    |ratPowerDyadicLogUpper (ratPowerNatMantissa 2) (1-xiGridArgument 1)
      (Nat.log2 2) 400 / 256| ≤ 1 := by
  decide +kernel

theorem firstNode_zero_root_eval_checks :
    XiRootEvalChecks 0 firstNodeParams firstNodeGrid rootLowerFor rootUpperFor where
  scale_pos := by norm_num [firstNodeParams]
  expTerms_pos := by norm_num [firstNodeParams]
  grid_pos := by norm_num [firstNodeGrid]
  gamma_lower := (firstNode_gamma_checks 0).1
  gamma_upper := (firstNode_gamma_checks 0).2
  pi_lower := firstNode_zero_pi_checks.1
  pi_upper := firstNode_zero_pi_checks.2
  eta_checks := firstNode_root_checks
  two_lower := firstNode_zero_two_checks.1
  two_upper := firstNode_zero_two_checks.2
  denominator_pos := firstNode_zero_denominator_pos

theorem firstNode_one_root_eval_checks :
    XiRootEvalChecks 1 firstNodeParams firstNodeGrid rootLowerFor rootUpperFor where
  scale_pos := by norm_num [firstNodeParams]
  expTerms_pos := by norm_num [firstNodeParams]
  grid_pos := by norm_num [firstNodeGrid]
  gamma_lower := (firstNode_gamma_checks 1).1
  gamma_upper := (firstNode_gamma_checks 1).2
  pi_lower := firstNode_one_pi_checks.1
  pi_upper := firstNode_one_pi_checks.2
  eta_checks := firstNode_root_checks
  two_lower := firstNode_one_two_checks.1
  two_upper := firstNode_one_two_checks.2
  denominator_pos := firstNode_one_denominator_pos

end ReciprocalXi



