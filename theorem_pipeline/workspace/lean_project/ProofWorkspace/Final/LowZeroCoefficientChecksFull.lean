import ProofWorkspace.Final.RationalThetaCoefficientChecksFull
import ProofWorkspace.Final.PowerExpTransitionErrorFull
import ProofWorkspace.Final.XiLowZeroSeedFull

set_option autoImplicit false
noncomputable section
namespace ReciprocalXi

def ratLowZeroFirst (x c h p : ℚ) (k : ℕ) : ℚ × ℚ :=
  ((-3/4-p*k^2*c)*h/c,(x/4)*h/c)

def ratLowZeroA (x c h p : ℚ) (k n : ℕ) : ℚ × ℚ :=
  ((-3/4-p*k^2*c-(n+1))*h/(c*(n+2)),(x/4)*h/(c*(n+2)))

theorem ratLowZeroFirst_value (x c h p : ℚ) (k : ℕ) :
    ratComplexValue (ratLowZeroFirst x c h p k)=
      powerExpScaledFirst (complexThetaExponent x) c h (p*(k:ℝ)^2) := by
  unfold ratComplexValue ratLowZeroFirst powerExpScaledFirst complexThetaExponent
  push_cast
  ring

theorem ratLowZeroA_value (x c h p : ℚ) (k n : ℕ) :
    ratComplexValue (ratLowZeroA x c h p k n)=
      powerExpScaledA (complexThetaExponent x) c h (p*(k:ℝ)^2) n := by
  unfold ratComplexValue ratLowZeroA powerExpScaledA complexThetaExponent
  push_cast
  ring

theorem lowZeroLambda_midpoint_error (k : ℕ) (hk : k≤5) :
    |Real.pi*(k:ℝ)^2-(sourcePiMidpoint:ℝ)*(k:ℝ)^2|≤1/(10:ℝ)^140 := by
  have hp : |Real.pi-(sourcePiMidpoint:ℝ)|≤1/(10:ℝ)^150 := by
    simpa only [abs_sub_comm] using sourcePiMidpoint_error
  have hk0 : (0:ℝ)≤k := Nat.cast_nonneg k
  have hk5 : (k:ℝ)≤5 := by exact_mod_cast hk
  have hk2 : (k:ℝ)^2≤25 := by nlinarith
  rw [← sub_mul,abs_mul,abs_of_nonneg (sq_nonneg (k:ℝ))]
  exact (mul_le_mul hp hk2 (sq_nonneg (k:ℝ)) (by positivity)).trans (by norm_num)

def lowZeroCoefficientRadius (r : ℕ → ℚ) (n : ℕ) : ℚ := |r n|
def lowZeroCoefficientRoundRadius : ℚ := 1/(10:ℚ)^158
def lowZeroSeedRadius (w : ℚ × ℚ) : ℚ :=
  1/(10:ℚ)^90+(2/(10:ℚ)^68)*(ratComplexL1 w+1/(10:ℚ)^90)

def ratLowZeroCoefficientsValid (x c h p : ℚ) (k : ℕ)
    (w : ℕ → ℚ × ℚ) (r : ℕ → ℚ) : Prop :=
  k≤5 ∧ 1≤c ∧ 0≤h ∧ h≤1 ∧
  (∀ n : Fin 80, ratComplexL1 (w n)≤1) ∧
  lowZeroSeedRadius (w 0)≤lowZeroCoefficientRadius r 0 ∧
  (∀ n : Fin 80, lowZeroCoefficientRadius r n≤1/(10:ℚ)^50) ∧
  ratComplexL1 (ratComplexSub (w 1) (ratComplexMul (ratLowZeroFirst x c h p k) (w 0)))≤
    lowZeroCoefficientRoundRadius ∧
  (∀ n : Fin 78,
    ratComplexL1 (ratComplexSub (w ((n:ℕ)+2))
      (ratComplexSub (ratComplexMul (ratLowZeroA x c h p k n) (w ((n:ℕ)+1)))
        (ratComplexMul (ratThetaB c h p k n) (w n))))≤lowZeroCoefficientRoundRadius) ∧
  lowZeroCoefficientRoundRadius+thetaCoefficientTransitionDelta+
    (ratComplexL1 (ratLowZeroFirst x c h p k)+thetaCoefficientTransitionDelta)*
      lowZeroCoefficientRadius r 0≤lowZeroCoefficientRadius r 1 ∧
  (∀ n : Fin 78,
    lowZeroCoefficientRoundRadius+2*thetaCoefficientTransitionDelta+
    (ratComplexL1 (ratLowZeroA x c h p k n)+thetaCoefficientTransitionDelta)*
      lowZeroCoefficientRadius r ((n:ℕ)+1)+
    (ratComplexL1 (ratThetaB c h p k n)+thetaCoefficientTransitionDelta)*
      lowZeroCoefficientRadius r n≤lowZeroCoefficientRadius r ((n:ℕ)+2))

theorem lowZeroCoefficientRadius_nonneg (r : ℕ → ℚ) (n : ℕ) :
    0≤lowZeroCoefficientRadius r n := abs_nonneg _

theorem lowZeroSeedRadius_sound (w : ℚ × ℚ) :
    1/(10:ℝ)^90+(2/(10:ℝ)^68)*(‖ratComplexValue w‖+1/(10:ℝ)^90)≤
      (lowZeroSeedRadius w:ℝ) := by
  have hn := ratComplexValue_norm_le_L1 w
  unfold lowZeroSeedRadius
  push_cast
  nlinarith

end ReciprocalXi
