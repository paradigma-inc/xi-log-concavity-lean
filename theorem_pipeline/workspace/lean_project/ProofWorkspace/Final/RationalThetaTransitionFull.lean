import ProofWorkspace.Final.RationalComplexFull
import ProofWorkspace.Final.PowerExpScaledTransitionFull
import ProofWorkspace.Final.XiThetaAtomSeedFull

set_option autoImplicit false
noncomputable section
namespace ReciprocalXi

def ratComplexSub (a b : ℚ × ℚ) : ℚ × ℚ := (a.1-b.1,a.2-b.2)
def ratComplexL1 (a : ℚ × ℚ) : ℚ := |a.1|+|a.2|

theorem ratComplexValue_sub (a b : ℚ × ℚ) :
    ratComplexValue (ratComplexSub a b)=ratComplexValue a-ratComplexValue b := by
  apply Complex.ext <;> simp [ratComplexValue, ratComplexSub]

def ratThetaFirst (c h p : ℚ) (k : ℕ) : ℚ × ℚ :=
  ((-3/4-p*k^2*c)*h/c,12*h/c)

def ratThetaA (c h p : ℚ) (k n : ℕ) : ℚ × ℚ :=
  ((-3/4-p*k^2*c-(n+1))*h/(c*(n+2)),12*h/(c*(n+2)))

def ratThetaB (c h p : ℚ) (k n : ℕ) : ℚ × ℚ :=
  (p*k^2*h^2/(c*(n+2)),0)

theorem ratThetaFirst_value (c h p : ℚ) (k : ℕ) :
    ratComplexValue (ratThetaFirst c h p k)=
      powerExpScaledFirst (complexThetaExponent 48) c h (p*(k:ℝ)^2) := by
  unfold ratComplexValue ratThetaFirst powerExpScaledFirst complexThetaExponent
  push_cast
  ring

theorem ratThetaA_value (c h p : ℚ) (k n : ℕ) :
    ratComplexValue (ratThetaA c h p k n)=
      powerExpScaledA (complexThetaExponent 48) c h (p*(k:ℝ)^2) n := by
  unfold ratComplexValue ratThetaA powerExpScaledA complexThetaExponent
  push_cast
  ring

theorem ratThetaB_value (c h p : ℚ) (k n : ℕ) :
    ratComplexValue (ratThetaB c h p k n)=
      powerExpScaledB c h (p*(k:ℝ)^2) n := by
  unfold ratComplexValue ratThetaB powerExpScaledB
  push_cast
  ring

end ReciprocalXi
