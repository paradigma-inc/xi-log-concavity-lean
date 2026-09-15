import ProofWorkspace.Final.RationalThetaTransitionFull
import ProofWorkspace.Final.XiThetaPanelCoefficientErrorFull

set_option autoImplicit false
noncomputable section
namespace ReciprocalXi

def ratThetaApproxPanelValue (h : ℚ) (w : ℕ → ℕ → ℚ × ℚ) : ℚ :=
  ∑ n ∈ Finset.range 40, (h*(1-(-1:ℚ)^(n+1))/(n+1)) *
    (2*∑ k ∈ Finset.range 4, (w k n).1)

theorem ratThetaApproxPanelValue_cast (h : ℚ) (w : ℕ → ℕ → ℚ × ℚ) :
    (ratThetaApproxPanelValue h w:ℝ)=
      theta48ApproxPanelValue h (fun k n ↦ ratComplexValue (w k n)) := by
  unfold ratThetaApproxPanelValue theta48ApproxPanelValue theta48ScaledIntegralWeight
  simp only [ratComplexValue_re]
  push_cast
  rfl

theorem ratThetaPanel_error (c : ℝ) (h : ℚ) (w : ℕ → ℕ → ℚ × ℚ)
    (hc : 0<c) (hh0 : (0:ℚ)≤h) (hh1 : h≤1/2)
    (hw : ∀ k : ℕ, k<4 → ∀ n : ℕ, n<40 →
      ‖ratComplexValue (w k n)-scaledPowerExpCoefficient (complexThetaExponent 48)
        (c:ℂ) (Real.pi*((k:ℝ)+1)^2) h n‖≤1/(10:ℝ)^25) :
    |theta48TaylorPanelValue c h 40-(ratThetaApproxPanelValue h w:ℝ)|≤320/(10:ℝ)^25 := by
  rw [ratThetaApproxPanelValue_cast]
  have he := theta48Panel_coefficient_error c h (1/(10:ℝ)^25)
    (fun k n ↦ ratComplexValue (w k n)) hc (by exact_mod_cast hh0)
    (by simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using
      (Rat.cast_le (K:=ℝ)).mpr hh1) (by positivity) (by
      intro k hk n hn
      rw [norm_sub_rev]
      exact hw k hk n hn)
  convert he using 1 <;> ring

end ReciprocalXi
