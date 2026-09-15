import ProofWorkspace.Final.RootFactorBoundsFull

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000

namespace ReciprocalXi

/-- Kernel-certified B=10^180 lower endpoint for pi^(-1/160). -/
def sourcePiRootLowerInt : ℤ :=
  992870971161979939638965016299319813401852694497651048312129297972643870699555127173708064382274262565765516022974110035560544331748862965830241888743404428630319817369051399183188

/-- Kernel-certified B=10^180 upper endpoint for pi^(-1/160). -/
def sourcePiRootUpperInt : ℤ :=
  992870971161979939638965016299319813401852694497651048312129297972643870699555127173708064382274262565765516022974110035560544331748862965830241888743408379138392639363359661452500

def sourcePiRootLower : ℚ :=
  (sourcePiRootLowerInt : ℚ) / (10 : ℚ)^180

def sourcePiRootUpper : ℚ :=
  (sourcePiRootUpperInt : ℚ) / (10 : ℚ)^180

theorem sourcePiRootLower_nonneg : (0 : ℚ) ≤ sourcePiRootLower := by
  norm_num [sourcePiRootLower, sourcePiRootLowerInt]

theorem sourcePiRootUpper_nonneg : (0 : ℚ) ≤ sourcePiRootUpper := by
  norm_num [sourcePiRootUpper, sourcePiRootUpperInt]

theorem sourcePiRootLower_poly :
    (sourcePiMidpoint + 1/(10 : ℚ)^150) * sourcePiRootLower^160 ≤ 1 := by
  decide +kernel

theorem sourcePiRootUpper_poly :
    1 ≤ (sourcePiMidpoint - 1/(10 : ℚ)^150) * sourcePiRootUpper^160 := by
  decide +kernel

theorem sourcePiRoot_actual_enclosure :
    (sourcePiRootLower:ℝ) ≤ Real.pi^(-(1/160):ℝ) ∧
      Real.pi^(-(1/160):ℝ) ≤ (sourcePiRootUpper:ℝ) :=
  sourcePi_root160_enclosure sourcePiRootLower sourcePiRootUpper
    sourcePiRootLower_nonneg sourcePiRootUpper_nonneg
    sourcePiRootLower_poly sourcePiRootUpper_poly

theorem sourcePiRoot_grid_enclosure (k : ℕ) :
    (ratPowRoundLower sourcePiRootLower (10^180) (k+40):ℝ) ≤
      Real.pi^(-(xiGridArgument k:ℝ)/2) ∧
    Real.pi^(-(xiGridArgument k:ℝ)/2) ≤
      (ratPowRoundUpper sourcePiRootUpper (10^180) (k+40):ℝ) :=
  ratPiRootGrid_enclosure sourcePiRootLower sourcePiRootUpper k (10^180)
    (by norm_num) sourcePiRootLower_nonneg sourcePiRootUpper_nonneg
    sourcePiRootLower_poly sourcePiRootUpper_poly

end ReciprocalXi

