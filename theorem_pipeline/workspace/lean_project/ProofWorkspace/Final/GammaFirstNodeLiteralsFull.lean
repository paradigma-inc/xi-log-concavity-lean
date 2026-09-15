import ProofWorkspace.Final.GammaZetaChunk00Full
import ProofWorkspace.Final.GammaZetaChunk01Full
import ProofWorkspace.Final.GammaZetaChunk02Full
import ProofWorkspace.Final.GammaZetaChunk03Full
import ProofWorkspace.Final.GammaZetaChunk04Full
import ProofWorkspace.Final.GammaZetaChunk05Full
import ProofWorkspace.Final.GammaZetaChunk06Full
import ProofWorkspace.Final.GammaZetaChunk07Full
import ProofWorkspace.Final.GammaZetaChunk08Full
import ProofWorkspace.Final.GammaZetaChunk09Full
import ProofWorkspace.Final.GammaZetaChunk10Full
import ProofWorkspace.Final.RoundedLogConstantsFull
import ProofWorkspace.Final.FirstSourceCandidateArithmeticFull

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 100000000
namespace ReciprocalXi
def gammaZetaLiteralTable : List (ℚ × ℚ) := [gammaZetaLiteralChunk00, gammaZetaLiteralChunk01, gammaZetaLiteralChunk02, gammaZetaLiteralChunk03, gammaZetaLiteralChunk04, gammaZetaLiteralChunk05, gammaZetaLiteralChunk06, gammaZetaLiteralChunk07, gammaZetaLiteralChunk08, gammaZetaLiteralChunk09, gammaZetaLiteralChunk10].flatten
theorem gammaZetaLiteralTable_eq :
    gammaZetaLiteralTable = ratGammaZetaTable 440 480 (10^180) := by
  unfold gammaZetaLiteralTable
  rw [gammaZetaLiteralChunk00_eq, gammaZetaLiteralChunk01_eq, gammaZetaLiteralChunk02_eq, gammaZetaLiteralChunk03_eq, gammaZetaLiteralChunk04_eq, gammaZetaLiteralChunk05_eq, gammaZetaLiteralChunk06_eq, gammaZetaLiteralChunk07_eq, gammaZetaLiteralChunk08_eq, gammaZetaLiteralChunk09_eq, gammaZetaLiteralChunk10_eq]
  unfold ratGammaZetaTable
  rw [←gammaEulerWeights480_eq]
  rfl


private def gammaNodeCandidate (z : ℚ) (zs : List (ℚ × ℚ)) : ℚ × ℚ :=
  let B := 10^180
  let p := ratGammaSeriesFromTable z zs B
  let clo := ratRoundLower (min (z*roundedLogPiLower400B180) (z*roundedLogPiUpper400B180)) B +
    ratRoundLower (min ((-2*z)*roundedLogTwoLower400B180) ((-2*z)*roundedLogTwoUpper400B180)) B
  let chi := ratRoundUpper (max (z*roundedLogPiLower400B180) (z*roundedLogPiUpper400B180)) B +
    ratRoundUpper (max ((-2*z)*roundedLogTwoLower400B180) ((-2*z)*roundedLogTwoUpper400B180)) B
  (ratRoundLower (clo+p.1-8*(1/2:ℚ)^442) B,
    ratRoundUpper (chi+p.2+8*(1/2:ℚ)^442) B)


private theorem gammaNodeCandidate_eq (z : ℚ) :
    gammaNodeCandidate z (ratGammaZetaTable 440 480 (10^180)) =
      (ratLogGammaFastLower z 440 480 400 (10^180),
        ratLogGammaFastUpper z 440 480 400 (10^180)) := by
  rw [←ratLogGammaTablePair_eq]
  unfold gammaNodeCandidate ratLogGammaTablePair ratGammaConstantFastLower
    ratGammaConstantFastUpper ratPiPowerLogFastLower ratPiPowerLogFastUpper
  rw [roundedLogPiLower400B180_eq, roundedLogPiUpper400B180_eq,
    roundedLogTwoLower400B180_eq, roundedLogTwoUpper400B180_eq]


private theorem gammaNodeZero_literal_table :
    gammaNodeCandidate (1/4) gammaZetaLiteralTable =
      (candidateGammaNodeZeroLower,candidateGammaNodeZeroUpper) := by
  decide +kernel

theorem gammaNodeZero_fast_literals :
    (ratLogGammaFastLower (1/4) 440 480 400 (10^180),
      ratLogGammaFastUpper (1/4) 440 480 400 (10^180)) =
      (candidateGammaNodeZeroLower,candidateGammaNodeZeroUpper) := by
  rw [←gammaNodeCandidate_eq, ←gammaZetaLiteralTable_eq]
  exact gammaNodeZero_literal_table

private theorem gammaNodeOne_literal_table :
    gammaNodeCandidate (41/160) gammaZetaLiteralTable =
      (candidateGammaNodeOneLower,candidateGammaNodeOneUpper) := by
  decide +kernel

theorem gammaNodeOne_fast_literals :
    (ratLogGammaFastLower (41/160) 440 480 400 (10^180),
      ratLogGammaFastUpper (41/160) 440 480 400 (10^180)) =
      (candidateGammaNodeOneLower,candidateGammaNodeOneUpper) := by
  rw [←gammaNodeCandidate_eq, ←gammaZetaLiteralTable_eq]
  exact gammaNodeOne_literal_table

end ReciprocalXi

