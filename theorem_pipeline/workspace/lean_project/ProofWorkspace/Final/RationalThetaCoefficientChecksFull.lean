import ProofWorkspace.Final.RationalThetaTransitionFull
import ProofWorkspace.Final.ComplexRecurrenceErrorFull

set_option autoImplicit false
noncomputable section
namespace ReciprocalXi

def thetaCoefficientRadius (n : ℕ) : ℚ := (40:ℚ)^n/n.factorial/(10:ℚ)^42
def thetaCoefficientTransitionDelta : ℚ := 1/(10:ℚ)^140
def thetaCoefficientRoundRadius : ℚ := 1/(10:ℚ)^58

def ratThetaCoefficientsValid (c h p : ℚ) (k : ℕ) (w : ℕ → ℚ × ℚ) : Prop :=
  k≤4 ∧ 1≤c ∧ 0≤h ∧ h≤1 ∧
  (∀ n : Fin 40, ratComplexL1 (w n)≤1) ∧
  ratComplexL1 (ratComplexSub (w 1) (ratComplexMul (ratThetaFirst c h p k) (w 0)))≤
    thetaCoefficientRoundRadius ∧
  (∀ n : Fin 38,
    ratComplexL1 (ratComplexSub (w ((n:ℕ)+2))
      (ratComplexSub (ratComplexMul (ratThetaA c h p k n) (w ((n:ℕ)+1)))
        (ratComplexMul (ratThetaB c h p k n) (w n))))≤thetaCoefficientRoundRadius) ∧
  thetaCoefficientRoundRadius+thetaCoefficientTransitionDelta+
    (ratComplexL1 (ratThetaFirst c h p k)+thetaCoefficientTransitionDelta)*
      thetaCoefficientRadius 0≤thetaCoefficientRadius 1 ∧
  (∀ n : Fin 38,
    thetaCoefficientRoundRadius+2*thetaCoefficientTransitionDelta+
    (ratComplexL1 (ratThetaA c h p k n)+thetaCoefficientTransitionDelta)*
      thetaCoefficientRadius ((n:ℕ)+1)+
    (ratComplexL1 (ratThetaB c h p k n)+thetaCoefficientTransitionDelta)*
      thetaCoefficientRadius n≤thetaCoefficientRadius ((n:ℕ)+2))

theorem thetaCoefficientRadius_nonneg (n : ℕ) : 0≤thetaCoefficientRadius n := by
  unfold thetaCoefficientRadius
  positivity

theorem thetaCoefficientRadius_uniform (n : ℕ) (hn : n<40) :
    thetaCoefficientRadius n≤1/(10:ℚ)^25 := by
  have h : ∀ i : Fin 40, thetaCoefficientRadius i≤1/(10:ℚ)^25 := by decide +kernel
  exact h ⟨n,hn⟩

theorem ratComplexValue_norm_le_L1 (q : ℚ × ℚ) :
    ‖ratComplexValue q‖≤(ratComplexL1 q:ℝ) := ratComplexValue_norm_le q

theorem complex_norm_le_rat_approx (z : ℂ) (q : ℚ × ℚ) (delta : ℝ)
    (he : ‖z-ratComplexValue q‖≤delta) :
    ‖z‖≤(ratComplexL1 q:ℝ)+delta := by
  have ht := norm_sub_le_norm_sub_add_norm_sub z (ratComplexValue q) 0
  simp only [sub_zero] at ht
  have hq := ratComplexValue_norm_le_L1 q
  linarith

end ReciprocalXi
