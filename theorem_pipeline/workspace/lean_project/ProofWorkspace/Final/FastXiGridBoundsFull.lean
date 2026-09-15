import ProofWorkspace.Final.RoundedXiBoundsFull
import ProofWorkspace.Final.FastGammaBoundsFull
import ProofWorkspace.Final.GridPowerChecksFull

/-! Actual Xi and reciprocal-grid enclosures using fully rounded Gamma and pi logarithms.
All remaining hypotheses are explicit checks on rational expressions. -/

set_option autoImplicit false

namespace ReciprocalXi

def ratXiFastGridLower (k : ℕ) (p : XiEvalParams) (B : ℕ) : ℚ :=
  if k = 40 then 1/2 else ratRoundLower ((xiGridArgument k / 2) *
    (max 0 (ratGammaGridFastLower k p.gammaTerms p.zetaTerms p.logTerms p.scale p.expTerms B) *
     max 0 (ratPiPowerFastLower (-xiGridArgument k / 2) p.logTerms p.scale p.expTerms B) *
     max 0 (ratEtaGridRoundedLower p.etaTerms k p.logTerms p.scale p.expTerms B) *
     max 0 (ratXiRoundedBracketLower (xiGridArgument k) p.logTerms p.scale p.expTerms B))) B

def ratXiFastGridUpper (k : ℕ) (p : XiEvalParams) (B : ℕ) : ℚ :=
  if k = 40 then 1/2 else ratRoundUpper ((xiGridArgument k / 2) *
    (ratGammaGridFastUpper k p.gammaTerms p.zetaTerms p.logTerms p.scale p.expTerms B *
     ratPiPowerFastUpper (-xiGridArgument k / 2) p.logTerms p.scale p.expTerms B *
     ratEtaGridRoundedUpper p.etaTerms k p.logTerms p.scale p.expTerms B *
     ratXiRoundedBracketUpper (xiGridArgument k) p.logTerms p.scale p.expTerms B)) B

/-- All checks concern exact rational expressions; no actual function value is an input. -/
structure XiFastEvalChecks (k : ℕ) (p : XiEvalParams) (B : ℕ) : Prop where
  scale_pos : 0 < p.scale
  expTerms_pos : 0 < p.expTerms
  grid_pos : 0 < B
  gamma_lower : |ratLogGammaFastLower (gammaGridOffset k) p.gammaTerms p.zetaTerms p.logTerms B / p.scale| ≤ 1
  gamma_upper : |ratLogGammaFastUpper (gammaGridOffset k) p.gammaTerms p.zetaTerms p.logTerms B / p.scale| ≤ 1
  pi_lower : |ratPiPowerLogFastLower (-xiGridArgument k / 2) p.logTerms B / p.scale| ≤ 1
  pi_upper : |ratPiPowerLogFastUpper (-xiGridArgument k / 2) p.logTerms B / p.scale| ≤ 1
  eta_checks : ∀ j ∈ Finset.range p.etaTerms, GridPowerChecks (j+1) p.logTerms p.scale
  two_lower : |ratPowerDyadicLogLower (ratPowerNatMantissa 2) (1-xiGridArgument k)
    (Nat.log2 2) p.logTerms / p.scale| ≤ 1
  two_upper : |ratPowerDyadicLogUpper (ratPowerNatMantissa 2) (1-xiGridArgument k)
    (Nat.log2 2) p.logTerms / p.scale| ≤ 1
  denominator_pos : 0 < ratXiRoundedDenominatorLower (xiGridArgument k) p.logTerms p.scale p.expTerms B

theorem ratXiFastGrid_enclosure_of_ne (k : ℕ) (p : XiEvalParams) (B : ℕ)
    (hk : k ≠ 40) (hc : XiFastEvalChecks k p B) :
    (ratXiFastGridLower k p B : ℝ) ≤ (xi (xiGridArgument k : ℂ)).re ∧
    (xi (xiGridArgument k : ℂ)).re ≤ (ratXiFastGridUpper k p B : ℝ) := by
  have hs : 0 < (xiGridArgument k : ℝ) := by exact_mod_cast xiGridArgument_pos k
  have hs1 : (xiGridArgument k : ℝ) ≠ 1 := by exact_mod_cast xiGridArgument_ne_one k hk
  have hG := ratGammaGridFast_enclosure k p.gammaTerms p.zetaTerms p.logTerms p.scale p.expTerms B
    hc.scale_pos hc.expTerms_pos hc.grid_pos hc.gamma_lower hc.gamma_upper
  have hP := ratPiPowerFast_enclosure (-xiGridArgument k / 2) p.logTerms p.scale p.expTerms B
    hc.scale_pos hc.expTerms_pos hc.grid_pos hc.pi_lower hc.pi_upper
  have hE := ratEtaGridRounded_enclosure p.etaTerms k p.logTerms p.scale p.expTerms B
    hc.scale_pos hc.expTerms_pos hc.grid_pos hc.eta_checks
  have hF := ratXiRoundedBracket_enclosure (xiGridArgument k) p.logTerms p.scale p.expTerms B
    (xiGridArgument_ne_one k hk) hc.scale_pos hc.expTerms_pos hc.grid_pos
    hc.two_lower hc.two_upper hc.denominator_pos
  have hxG : (gammaGridArgument k : ℝ) = (xiGridArgument k : ℝ) / 2 := by
    have h := congrArg (fun q : ℚ => (q : ℝ)) (xiGridArgument_half k)
    push_cast at h
    exact h.symm
  rw [hxG] at hG
  push_cast at hP
  have hG0 := (Real.Gamma_pos_of_pos (show 0 < (xiGridArgument k : ℝ)/2 by positivity)).le
  have hP0 := Real.rpow_nonneg Real.pi_pos.le (-(xiGridArgument k : ℝ)/2)
  have hE0 : 0 ≤ etaIntegral (xiGridArgument k : ℝ) := by
    simpa [etaEulerApprox] using (etaIntegral_euler_error_bounds 0 (xiGridArgument k : ℝ) hs).1
  have hF0 := (xiEtaBracket_pos (xiGridArgument k : ℝ) hs1).le
  have hlG := max_le hG0 hG.1
  have hlP := max_le hP0 hP.1
  have hlE := max_le hE0 hE.1
  have hlF := max_le hF0 hF.1
  have hlo := mul_le_mul
    (mul_le_mul (mul_le_mul hlG hlP (le_max_left 0 _) hG0) hlE (le_max_left 0 _)
      (mul_nonneg hG0 hP0)) hlF (le_max_left 0 _) (mul_nonneg (mul_nonneg hG0 hP0) hE0)
  have hup := mul_le_mul
    (mul_le_mul (mul_le_mul hG.2 hP.2 hP0 (hG0.trans hG.2)) hE.2 hE0
      (mul_nonneg (hG0.trans hG.2) (hP0.trans hP.2))) hF.2 hF0
    (mul_nonneg (mul_nonneg (hG0.trans hG.2) (hP0.trans hP.2)) (hE0.trans hE.2))
  have hs0 : 0 ≤ (xiGridArgument k : ℝ) / 2 := by positivity
  have hlo' := mul_le_mul_of_nonneg_left hlo hs0
  have hup' := mul_le_mul_of_nonneg_left hup hs0
  have hxi := xi_re_eq_etaIntegral (xiGridArgument k : ℝ) hs hs1
  push_cast at hxi
  unfold ratXiFastGridLower ratXiFastGridUpper
  rw [if_neg hk, if_neg hk]
  apply ratRound_interval_enclosure _ _ _ B hc.grid_pos
  · push_cast
    rw [hxi]
    unfold xiEtaBracket at hlo'
    convert hlo' using 1; ring
  · push_cast
    rw [hxi]
    unfold xiEtaBracket at hup'
    convert hup' using 1; ring

theorem ratXiFastGrid_enclosure (k : ℕ) (p : XiEvalParams) (B : ℕ)
    (hc : k ≠ 40 → XiFastEvalChecks k p B) :
    (ratXiFastGridLower k p B : ℝ) ≤ (xi (xiGridArgument k : ℂ)).re ∧
    (xi (xiGridArgument k : ℂ)).re ≤ (ratXiFastGridUpper k p B : ℝ) := by
  by_cases hk : k = 40
  · subst k
    norm_num [ratXiFastGridLower, ratXiFastGridUpper, xiGridArgument, xi_one]
  · exact ratXiFastGrid_enclosure_of_ne k p B hk (hc hk)

def ratReciprocalFastGridLower (k : ℕ) (p : XiEvalParams) (B : ℕ) : ℚ :=
  ratRoundLower (max 0 (ratXiFastGridLower 0 p B) / ratXiFastGridUpper k p B) B
def ratReciprocalFastGridUpper (k : ℕ) (p : XiEvalParams) (B : ℕ) : ℚ :=
  ratRoundUpper (ratXiFastGridUpper 0 p B / ratXiFastGridLower k p B) B

theorem ratReciprocalFastGrid_enclosure (k : ℕ) (p : XiEvalParams) (B : ℕ)
    (h0 : XiFastEvalChecks 0 p B) (hk : k ≠ 40 → XiFastEvalChecks k p B)
    (hd : 0 < ratXiFastGridLower k p B) :
    (ratReciprocalFastGridLower k p B : ℝ) ≤ (reciprocalTransform ((k : ℝ)/40)).re ∧
    (reciprocalTransform ((k : ℝ)/40)).re ≤ (ratReciprocalFastGridUpper k p B : ℝ) := by
  have hN := ratXiFastGrid_enclosure 0 p B (fun _ => h0)
  have hD := ratXiFastGrid_enclosure k p B hk
  have hdR : 0 < (ratXiFastGridLower k p B : ℝ) := by exact_mod_cast hd
  have hden := hdR.trans_le hD.1
  have hupper := hden.trans_le hD.2
  have hnum : 0 ≤ (xi (xiGridArgument 0 : ℂ)).re := by
    have h := (xi_re_pos (xiGridArgument 0 : ℝ)).le
    push_cast at h
    exact h
  have hmax := max_le hnum hN.1
  apply ratRound_interval_enclosure _ _ _ B h0.grid_pos
  · push_cast
    rw [reciprocalTransform_grid_re]
    exact (div_le_div_of_nonneg_right hmax hupper.le).trans
      (div_le_div_of_nonneg_left hnum hden hD.2)
  · push_cast
    rw [reciprocalTransform_grid_re]
    exact (div_le_div_of_nonneg_right hN.2 hden.le).trans
      (div_le_div_of_nonneg_left (hnum.trans hN.2) hdR hD.1)

end ReciprocalXi

