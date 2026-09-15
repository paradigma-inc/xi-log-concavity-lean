import ProofWorkspace.Final.RoundedSeriesScansFull

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 15000000
set_option exponentiation.threshold 1024

namespace ReciprocalXi

/-- Exact B = 10^180 lower endpoint produced by the rounded log-pi evaluator. -/
def roundedLogPiLower400B180 : ℚ :=
  (1144729885849400174143427351353058711647294812915311571513623071472137769884826079783623270275489707702009812228697989159048205527923456587279081078810286825276393914266345902901427 : ℚ) / (10^180)

/-- Exact B = 10^180 upper endpoint produced by the rounded log-pi evaluator. -/
def roundedLogPiUpper400B180 : ℚ :=
  (1144729885849400174143427351353058711647294812915311571513623071472137769884826079783623270275489707702009812228697989159048205527923456587279081078810286825276393914266345902903719 : ℚ) / (10^180)

/-- Exact B = 10^180 lower endpoint for the q=2, r=1/3 logarithm evaluator. -/
def roundedLogTwoLower400B180 : ℚ :=
  (693147180559945309417232121458176568075500134360255254120680009493393621969694715605863326996418687542001481020570685733685520235758130557032670751635075961930727570828371435190093 : ℚ) / (10^180)

/-- Exact B = 10^180 upper endpoint for the q=2, r=1/3 logarithm evaluator. -/
def roundedLogTwoUpper400B180 : ℚ :=
  (693147180559945309417232121458176568075500134360255254120680009493393621969694715605863326996418687542001481020570685733685520235758130557032670751635075961930727570828371435190919 : ℚ) / (10^180)

theorem roundedLogPiLower400B180_eq :
    ratPiLogFullyRoundedLower 400 (10^180) = roundedLogPiLower400B180 := by
  norm_num [roundedLogPiLower400B180, ratPiLogFullyRoundedLower,
    ratLogFullyRoundedLower, ratLogTaylorRoundedLower, ratLogTermRounded,
    ratLogUniformError, ratLogArgument, ratRoundLower, ratRoundUpper,
    machinPiLower, machinPiUpper, machinPiMidpoint, machinPiRadius,
    ratArctanTaylor, ratArctanError, Finset.sum_range_succ]

theorem roundedLogPiUpper400B180_eq :
    ratPiLogFullyRoundedUpper 400 (10^180) = roundedLogPiUpper400B180 := by
  norm_num [roundedLogPiUpper400B180, ratPiLogFullyRoundedUpper,
    ratLogFullyRoundedUpper, ratLogTaylorRoundedUpper, ratLogTermRounded,
    ratLogUniformError, ratLogArgument, ratRoundLower, ratRoundUpper,
    machinPiLower, machinPiUpper, machinPiMidpoint, machinPiRadius,
    ratArctanTaylor, ratArctanError, Finset.sum_range_succ]

theorem roundedLogTwoLower400B180_eq :
    ratLogFullyRoundedLower 2 (1/3) 400 (10^180) = roundedLogTwoLower400B180 := by
  norm_num [roundedLogTwoLower400B180, ratLogFullyRoundedLower,
    ratLogTaylorRoundedLower, ratLogTermRounded, ratLogUniformError,
    ratLogArgument, ratRoundLower, ratRoundUpper, Finset.sum_range_succ]

theorem roundedLogTwoUpper400B180_eq :
    ratLogFullyRoundedUpper 2 (1/3) 400 (10^180) = roundedLogTwoUpper400B180 := by
  norm_num [roundedLogTwoUpper400B180, ratLogFullyRoundedUpper,
    ratLogTaylorRoundedUpper, ratLogTermRounded, ratLogUniformError,
    ratLogArgument, ratRoundLower, ratRoundUpper, Finset.sum_range_succ]

theorem roundedLogPiEndpoints400B180 :
    ratPiLogFullyRoundedLower 400 (10^180) = roundedLogPiLower400B180 ∧
    ratPiLogFullyRoundedUpper 400 (10^180) = roundedLogPiUpper400B180 := by
  exact ⟨roundedLogPiLower400B180_eq, roundedLogPiUpper400B180_eq⟩

theorem roundedLogTwoEndpoints400B180 :
    ratLogFullyRoundedLower 2 (1/3) 400 (10^180) = roundedLogTwoLower400B180 ∧
    ratLogFullyRoundedUpper 2 (1/3) 400 (10^180) = roundedLogTwoUpper400B180 := by
  exact ⟨roundedLogTwoLower400B180_eq, roundedLogTwoUpper400B180_eq⟩

end ReciprocalXi

