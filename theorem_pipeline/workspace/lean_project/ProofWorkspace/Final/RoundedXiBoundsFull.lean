import ProofWorkspace.Final.RoundedEtaGridBoundsFull

/-!
# Actual Xi and reciprocal-grid enclosures using rounded arithmetic

The real-power grid recurrence, rounded eta/zeta/Gamma-log sums and fully
rounded exponential compose with the actual Xi factorization. Only explicit
rational checks remain; the removable node is exact.
-/

set_option autoImplicit false

namespace ReciprocalXi

def ratXiRoundedDenominatorLower (s : ℚ) (L m n B : ℕ) : ℚ :=
  if s < 1 then ratPowerNatRoundedLower 2 (1-s) L m n B - 1
  else 1 - ratPowerNatRoundedUpper 2 (1-s) L m n B
def ratXiRoundedDenominatorUpper (s : ℚ) (L m n B : ℕ) : ℚ :=
  if s < 1 then ratPowerNatRoundedUpper 2 (1-s) L m n B - 1
  else 1 - ratPowerNatRoundedLower 2 (1-s) L m n B
def ratXiRoundedBracketLower (s : ℚ) (L m n B : ℕ) : ℚ :=
  ratRoundLower (|s-1| / ratXiRoundedDenominatorUpper s L m n B) B
def ratXiRoundedBracketUpper (s : ℚ) (L m n B : ℕ) : ℚ :=
  ratRoundUpper (|s-1| / ratXiRoundedDenominatorLower s L m n B) B

theorem ratXiRoundedDenominator_enclosure (s : ℚ) (L m n B : ℕ) (hs1 : s ≠ 1)
    (hm : 0 < m) (hn : 0 < n) (hB : 0 < B)
    (hl : |ratPowerDyadicLogLower (ratPowerNatMantissa 2) (1-s) (Nat.log2 2) L / m| ≤ 1)
    (hu : |ratPowerDyadicLogUpper (ratPowerNatMantissa 2) (1-s) (Nat.log2 2) L / m| ≤ 1) :
    (ratXiRoundedDenominatorLower s L m n B : ℝ) ≤ |1 - (2 : ℝ)^(1-(s : ℝ))| ∧
    |1 - (2 : ℝ)^(1-(s : ℝ))| ≤ (ratXiRoundedDenominatorUpper s L m n B : ℝ) := by
  have hp := ratPowerNatRounded_enclosure 2 (1-s) L m n B (by norm_num) hm hn hB hl hu
  push_cast at hp
  unfold ratXiRoundedDenominatorLower ratXiRoundedDenominatorUpper
  split_ifs with hs
  · have hsR : (s : ℝ) < 1 := by exact_mod_cast hs
    rw [abs_of_neg (xiEta_denominator_neg_of_lt_one _ hsR)]
    push_cast
    constructor <;> linarith [hp.1, hp.2]
  · have hsR : 1 < (s : ℝ) := by exact_mod_cast (lt_of_le_of_ne (not_lt.mp hs) (Ne.symm hs1))
    rw [abs_of_pos (xiEta_denominator_pos_of_one_lt _ hsR)]
    push_cast
    constructor <;> linarith [hp.1, hp.2]

theorem ratXiRoundedBracket_enclosure (s : ℚ) (L m n B : ℕ) (hs1 : s ≠ 1)
    (hm : 0 < m) (hn : 0 < n) (hB : 0 < B)
    (hl : |ratPowerDyadicLogLower (ratPowerNatMantissa 2) (1-s) (Nat.log2 2) L / m| ≤ 1)
    (hu : |ratPowerDyadicLogUpper (ratPowerNatMantissa 2) (1-s) (Nat.log2 2) L / m| ≤ 1)
    (hd : 0 < ratXiRoundedDenominatorLower s L m n B) :
    (ratXiRoundedBracketLower s L m n B : ℝ) ≤ xiEtaBracket (s : ℝ) ∧
    xiEtaBracket (s : ℝ) ≤ (ratXiRoundedBracketUpper s L m n B : ℝ) := by
  have h := ratXiRoundedDenominator_enclosure s L m n B hs1 hm hn hB hl hu
  have hdR : 0 < (ratXiRoundedDenominatorLower s L m n B : ℝ) := by exact_mod_cast hd
  have ha : 0 < |1 - (2 : ℝ)^(1-(s : ℝ))| := hdR.trans_le h.1
  apply ratRound_interval_enclosure _ _ _ B hB
  · rw [xiEtaBracket_eq_abs _ (by exact_mod_cast hs1)]
    push_cast
    exact div_le_div_of_nonneg_left (abs_nonneg _) ha h.2
  · rw [xiEtaBracket_eq_abs _ (by exact_mod_cast hs1)]
    push_cast
    exact div_le_div_of_nonneg_left (abs_nonneg _) hdR h.1

def ratXiRoundedGridLower (k : ℕ) (p : XiEvalParams) (B : ℕ) : ℚ :=
  if k = 40 then 1/2 else ratRoundLower ((xiGridArgument k / 2) *
    (max 0 (ratGammaGridRoundedLower k p.gammaTerms p.zetaTerms p.logTerms p.scale p.expTerms B) *
     max 0 (ratPiPowerRoundedLower (-xiGridArgument k / 2) p.logTerms p.scale p.expTerms B) *
     max 0 (ratEtaGridRoundedLower p.etaTerms k p.logTerms p.scale p.expTerms B) *
     max 0 (ratXiRoundedBracketLower (xiGridArgument k) p.logTerms p.scale p.expTerms B))) B

def ratXiRoundedGridUpper (k : ℕ) (p : XiEvalParams) (B : ℕ) : ℚ :=
  if k = 40 then 1/2 else ratRoundUpper ((xiGridArgument k / 2) *
    (ratGammaGridRoundedUpper k p.gammaTerms p.zetaTerms p.logTerms p.scale p.expTerms B *
     ratPiPowerRoundedUpper (-xiGridArgument k / 2) p.logTerms p.scale p.expTerms B *
     ratEtaGridRoundedUpper p.etaTerms k p.logTerms p.scale p.expTerms B *
     ratXiRoundedBracketUpper (xiGridArgument k) p.logTerms p.scale p.expTerms B)) B

/-- All checks concern exact rational expressions; no actual function value is an input. -/
structure XiRoundedEvalChecks (k : ℕ) (p : XiEvalParams) (B : ℕ) : Prop where
  scale_pos : 0 < p.scale
  expTerms_pos : 0 < p.expTerms
  grid_pos : 0 < B
  gamma_lower : |ratLogGammaRoundedLower (gammaGridOffset k) p.gammaTerms p.zetaTerms p.logTerms B / p.scale| ≤ 1
  gamma_upper : |ratLogGammaRoundedUpper (gammaGridOffset k) p.gammaTerms p.zetaTerms p.logTerms B / p.scale| ≤ 1
  pi_lower : |ratPiPowerLogLower (-xiGridArgument k / 2) p.logTerms / p.scale| ≤ 1
  pi_upper : |ratPiPowerLogUpper (-xiGridArgument k / 2) p.logTerms / p.scale| ≤ 1
  eta_checks : ∀ j ∈ Finset.range p.etaTerms, GridPowerChecks (j+1) p.logTerms p.scale
  two_lower : |ratPowerDyadicLogLower (ratPowerNatMantissa 2) (1-xiGridArgument k)
    (Nat.log2 2) p.logTerms / p.scale| ≤ 1
  two_upper : |ratPowerDyadicLogUpper (ratPowerNatMantissa 2) (1-xiGridArgument k)
    (Nat.log2 2) p.logTerms / p.scale| ≤ 1
  denominator_pos : 0 < ratXiRoundedDenominatorLower (xiGridArgument k) p.logTerms p.scale p.expTerms B

theorem ratXiRoundedGrid_enclosure_of_ne (k : ℕ) (p : XiEvalParams) (B : ℕ)
    (hk : k ≠ 40) (hc : XiRoundedEvalChecks k p B) :
    (ratXiRoundedGridLower k p B : ℝ) ≤ (xi (xiGridArgument k : ℂ)).re ∧
    (xi (xiGridArgument k : ℂ)).re ≤ (ratXiRoundedGridUpper k p B : ℝ) := by
  have hs : 0 < (xiGridArgument k : ℝ) := by exact_mod_cast xiGridArgument_pos k
  have hs1 : (xiGridArgument k : ℝ) ≠ 1 := by exact_mod_cast xiGridArgument_ne_one k hk
  have hG := ratGammaGridRounded_enclosure k p.gammaTerms p.zetaTerms p.logTerms p.scale p.expTerms B
    hc.scale_pos hc.expTerms_pos hc.grid_pos hc.gamma_lower hc.gamma_upper
  have hP := ratPiPowerRounded_enclosure (-xiGridArgument k / 2) p.logTerms p.scale p.expTerms B
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
  unfold ratXiRoundedGridLower ratXiRoundedGridUpper
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

theorem ratXiRoundedGrid_enclosure (k : ℕ) (p : XiEvalParams) (B : ℕ)
    (hc : k ≠ 40 → XiRoundedEvalChecks k p B) :
    (ratXiRoundedGridLower k p B : ℝ) ≤ (xi (xiGridArgument k : ℂ)).re ∧
    (xi (xiGridArgument k : ℂ)).re ≤ (ratXiRoundedGridUpper k p B : ℝ) := by
  by_cases hk : k = 40
  · subst k
    norm_num [ratXiRoundedGridLower, ratXiRoundedGridUpper, xiGridArgument, xi_one]
  · exact ratXiRoundedGrid_enclosure_of_ne k p B hk (hc hk)

def ratReciprocalRoundedGridLower (k : ℕ) (p : XiEvalParams) (B : ℕ) : ℚ :=
  ratRoundLower (max 0 (ratXiRoundedGridLower 0 p B) / ratXiRoundedGridUpper k p B) B
def ratReciprocalRoundedGridUpper (k : ℕ) (p : XiEvalParams) (B : ℕ) : ℚ :=
  ratRoundUpper (ratXiRoundedGridUpper 0 p B / ratXiRoundedGridLower k p B) B

theorem ratReciprocalRoundedGrid_enclosure (k : ℕ) (p : XiEvalParams) (B : ℕ)
    (h0 : XiRoundedEvalChecks 0 p B) (hk : k ≠ 40 → XiRoundedEvalChecks k p B)
    (hd : 0 < ratXiRoundedGridLower k p B) :
    (ratReciprocalRoundedGridLower k p B : ℝ) ≤ (reciprocalTransform ((k : ℝ)/40)).re ∧
    (reciprocalTransform ((k : ℝ)/40)).re ≤ (ratReciprocalRoundedGridUpper k p B : ℝ) := by
  have hN := ratXiRoundedGrid_enclosure 0 p B (fun _ => h0)
  have hD := ratXiRoundedGrid_enclosure k p B hk
  have hdR : 0 < (ratXiRoundedGridLower k p B : ℝ) := by exact_mod_cast hd
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

