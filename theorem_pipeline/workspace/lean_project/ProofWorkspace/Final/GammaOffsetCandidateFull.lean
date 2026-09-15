import ProofWorkspace.Final.GammaFirstNodeLiteralsFull

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 100000000

namespace ReciprocalXi

/-- Residue-class parameter used by the retained Gamma offset table. -/
def gammaOffsetResidue (r : ℕ) : ℚ := ((r : ℤ) - 80) / 160

/-- The exact rational Gamma-log endpoint construction, exposed for all
residue-class offsets.  Numeric literals for individual offsets are checked
separately; this definition itself is not a retained-node certificate. -/
def gammaOffsetCandidate (z : ℚ) (zs : List (ℚ × ℚ)) : ℚ × ℚ :=
  let B := 10^180
  let p := ratGammaSeriesFromTable z zs B
  let clo :=
    ratRoundLower (min (z*roundedLogPiLower400B180) (z*roundedLogPiUpper400B180)) B +
      ratRoundLower (min ((-2*z)*roundedLogTwoLower400B180)
        ((-2*z)*roundedLogTwoUpper400B180)) B
  let chi :=
    ratRoundUpper (max (z*roundedLogPiLower400B180) (z*roundedLogPiUpper400B180)) B +
      ratRoundUpper (max ((-2*z)*roundedLogTwoLower400B180)
        ((-2*z)*roundedLogTwoUpper400B180)) B
  (ratRoundLower (clo+p.1-8*(1/2:ℚ)^442) B,
    ratRoundUpper (chi+p.2+8*(1/2:ℚ)^442) B)

theorem gammaOffsetCandidate_eq (z : ℚ) :
    gammaOffsetCandidate z (ratGammaZetaTable 440 480 (10^180)) =
      (ratLogGammaFastLower z 440 480 400 (10^180),
        ratLogGammaFastUpper z 440 480 400 (10^180)) := by
  rw [←ratLogGammaTablePair_eq]
  unfold gammaOffsetCandidate ratLogGammaTablePair ratGammaConstantFastLower
    ratGammaConstantFastUpper ratPiPowerLogFastLower ratPiPowerLogFastUpper
  rw [roundedLogPiLower400B180_eq, roundedLogPiUpper400B180_eq,
    roundedLogTwoLower400B180_eq, roundedLogTwoUpper400B180_eq]

end ReciprocalXi
