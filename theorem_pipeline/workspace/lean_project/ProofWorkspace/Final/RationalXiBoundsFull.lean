import ProofWorkspace.Final.GammaGridBoundsFull
import ProofWorkspace.Final.PiPowerBoundsFull
import ProofWorkspace.Final.RationalEtaBoundsFull
import ProofWorkspace.Final.XiEtaFactorizationFull
import ProofWorkspace.Final.XiFourierRealFull

noncomputable section
namespace ReciprocalXi

def ratXiDenominatorLower (s : ℚ) (L m n : ℕ) : ℚ :=
  if s < 1 then ratPowerLower 2 (1-s) L m n - 1
  else 1 - ratPowerUpper 2 (1-s) L m n
def ratXiDenominatorUpper (s : ℚ) (L m n : ℕ) : ℚ :=
  if s < 1 then ratPowerUpper 2 (1-s) L m n - 1
  else 1 - ratPowerLower 2 (1-s) L m n
def ratXiBracketLower (s : ℚ) (L m n : ℕ) : ℚ :=
  |s-1| / ratXiDenominatorUpper s L m n
def ratXiBracketUpper (s : ℚ) (L m n : ℕ) : ℚ :=
  |s-1| / ratXiDenominatorLower s L m n

theorem ratXiDenominator_enclosure (s : ℚ) (L m n : ℕ) (hs1 : s ≠ 1)
    (hm : 0 < m) (hn : 0 < n)
    (hl : |ratPowerLogLower 2 (1-s) L / m| ≤ 1)
    (hu : |ratPowerLogUpper 2 (1-s) L / m| ≤ 1) :
    (ratXiDenominatorLower s L m n : ℝ) ≤ |1 - (2 : ℝ)^(1-(s : ℝ))| ∧
    |1 - (2 : ℝ)^(1-(s : ℝ))| ≤ (ratXiDenominatorUpper s L m n : ℝ) := by
  have hp := ratPower_enclosure 2 (1-s) L m n (by norm_num) hm hn hl hu
  push_cast at hp
  unfold ratXiDenominatorLower ratXiDenominatorUpper
  split_ifs with hs
  · have hsR : (s : ℝ) < 1 := by exact_mod_cast hs
    rw [abs_of_neg (xiEta_denominator_neg_of_lt_one _ hsR)]
    push_cast
    constructor <;> linarith [hp.1, hp.2]
  · have hsR : 1 < (s : ℝ) := by exact_mod_cast (lt_of_le_of_ne (not_lt.mp hs) (Ne.symm hs1))
    rw [abs_of_pos (xiEta_denominator_pos_of_one_lt _ hsR)]
    push_cast
    constructor <;> linarith [hp.1, hp.2]

theorem ratXiBracket_enclosure (s : ℚ) (L m n : ℕ) (hs1 : s ≠ 1)
    (hm : 0 < m) (hn : 0 < n)
    (hl : |ratPowerLogLower 2 (1-s) L / m| ≤ 1)
    (hu : |ratPowerLogUpper 2 (1-s) L / m| ≤ 1)
    (hd : 0 < ratXiDenominatorLower s L m n) :
    (ratXiBracketLower s L m n : ℝ) ≤ xiEtaBracket (s : ℝ) ∧
    xiEtaBracket (s : ℝ) ≤ (ratXiBracketUpper s L m n : ℝ) := by
  have h := ratXiDenominator_enclosure s L m n hs1 hm hn hl hu
  have hdR : 0 < (ratXiDenominatorLower s L m n : ℝ) := by exact_mod_cast hd
  have ha : 0 < |1 - (2 : ℝ)^(1-(s : ℝ))| := hdR.trans_le h.1
  rw [xiEtaBracket_eq_abs _ (by exact_mod_cast hs1)]
  unfold ratXiBracketLower ratXiBracketUpper
  push_cast
  exact ⟨div_le_div_of_nonneg_left (abs_nonneg _) ha h.2,
    div_le_div_of_nonneg_left (abs_nonneg _) hdR h.1⟩

structure XiEvalParams where
  etaTerms : ℕ
  gammaTerms : ℕ
  zetaTerms : ℕ
  logTerms : ℕ
  scale : ℕ
  expTerms : ℕ

def xiGridArgument (k : ℕ) : ℚ := (k + 40) / 80

def ratXiGridLower (k : ℕ) (p : XiEvalParams) : ℚ :=
  if k = 40 then 1 / 2 else (xiGridArgument k / 2) *
    (max 0 (ratGammaGridLower k p.gammaTerms p.zetaTerms p.logTerms p.scale p.expTerms) *
     max 0 (ratPiPowerLower (-xiGridArgument k / 2) p.logTerms p.scale p.expTerms) *
     max 0 (ratEtaNatLower p.etaTerms (xiGridArgument k) p.logTerms p.scale p.expTerms) *
     max 0 (ratXiBracketLower (xiGridArgument k) p.logTerms p.scale p.expTerms))

def ratXiGridUpper (k : ℕ) (p : XiEvalParams) : ℚ :=
  if k = 40 then 1 / 2 else (xiGridArgument k / 2) *
    (ratGammaGridUpper k p.gammaTerms p.zetaTerms p.logTerms p.scale p.expTerms *
     ratPiPowerUpper (-xiGridArgument k / 2) p.logTerms p.scale p.expTerms *
     ratEtaNatUpper p.etaTerms (xiGridArgument k) p.logTerms p.scale p.expTerms *
     ratXiBracketUpper (xiGridArgument k) p.logTerms p.scale p.expTerms)

/-- Every obligation is an inequality between explicitly computed rationals. -/
structure XiEvalChecks (k : ℕ) (p : XiEvalParams) : Prop where
  scale_pos : 0 < p.scale
  expTerms_pos : 0 < p.expTerms
  gamma_lower : |ratLogGammaLower (gammaGridOffset k) p.gammaTerms p.zetaTerms p.logTerms / p.scale| ≤ 1
  gamma_upper : |ratLogGammaUpper (gammaGridOffset k) p.gammaTerms p.zetaTerms p.logTerms / p.scale| ≤ 1
  pi_lower : |ratPiPowerLogLower (-xiGridArgument k / 2) p.logTerms / p.scale| ≤ 1
  pi_upper : |ratPiPowerLogUpper (-xiGridArgument k / 2) p.logTerms / p.scale| ≤ 1
  eta_lower : ∀ j ∈ Finset.range p.etaTerms,
    |ratPowerDyadicLogLower (ratPowerNatMantissa (j+1)) (-xiGridArgument k)
      (Nat.log2 (j+1)) p.logTerms / p.scale| ≤ 1
  eta_upper : ∀ j ∈ Finset.range p.etaTerms,
    |ratPowerDyadicLogUpper (ratPowerNatMantissa (j+1)) (-xiGridArgument k)
      (Nat.log2 (j+1)) p.logTerms / p.scale| ≤ 1
  two_lower : |ratPowerLogLower 2 (1-xiGridArgument k) p.logTerms / p.scale| ≤ 1
  two_upper : |ratPowerLogUpper 2 (1-xiGridArgument k) p.logTerms / p.scale| ≤ 1
  denominator_pos : 0 < ratXiDenominatorLower (xiGridArgument k) p.logTerms p.scale p.expTerms

theorem xiGridArgument_pos (k : ℕ) : 0 < xiGridArgument k := by
  unfold xiGridArgument
  positivity

theorem xiGridArgument_half (k : ℕ) : xiGridArgument k / 2 = gammaGridArgument k := by
  unfold xiGridArgument gammaGridArgument
  ring

theorem xiGridArgument_ne_one (k : ℕ) (hk : k ≠ 40) : xiGridArgument k ≠ 1 := by
  intro h
  unfold xiGridArgument at h
  have he : (k : ℚ) = 40 := by linarith
  have he' : k = 40 := by exact_mod_cast he
  exact hk he'

theorem ratXiGrid_enclosure_of_ne (k : ℕ) (p : XiEvalParams) (hk : k ≠ 40)
    (hc : XiEvalChecks k p) :
    (ratXiGridLower k p : ℝ) ≤ (xi (xiGridArgument k : ℂ)).re ∧
    (xi (xiGridArgument k : ℂ)).re ≤ (ratXiGridUpper k p : ℝ) := by
  have hs : 0 < (xiGridArgument k : ℝ) := by exact_mod_cast xiGridArgument_pos k
  have hs1 : (xiGridArgument k : ℝ) ≠ 1 := by exact_mod_cast xiGridArgument_ne_one k hk
  have hG := ratGammaGrid_enclosure k p.gammaTerms p.zetaTerms p.logTerms p.scale p.expTerms
    hc.scale_pos hc.expTerms_pos hc.gamma_lower hc.gamma_upper
  have hP := ratPiPower_enclosure (-xiGridArgument k / 2) p.logTerms p.scale p.expTerms
    hc.scale_pos hc.expTerms_pos hc.pi_lower hc.pi_upper
  have hE := ratEtaNatIntegral_enclosure p.etaTerms (xiGridArgument k) p.logTerms p.scale p.expTerms
    (xiGridArgument_pos k) hc.scale_pos hc.expTerms_pos hc.eta_lower hc.eta_upper
  have hB := ratXiBracket_enclosure (xiGridArgument k) p.logTerms p.scale p.expTerms
    (xiGridArgument_ne_one k hk) hc.scale_pos hc.expTerms_pos hc.two_lower hc.two_upper hc.denominator_pos
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
  have hB0 := (xiEtaBracket_pos (xiGridArgument k : ℝ) hs1).le
  have hlG := max_le hG0 hG.1
  have hlP := max_le hP0 hP.1
  have hlE := max_le hE0 hE.1
  have hlB := max_le hB0 hB.1
  have hlo := mul_le_mul
    (mul_le_mul (mul_le_mul hlG hlP (le_max_left 0 _) hG0) hlE (le_max_left 0 _)
      (mul_nonneg hG0 hP0)) hlB (le_max_left 0 _) (mul_nonneg (mul_nonneg hG0 hP0) hE0)
  have hup := mul_le_mul
    (mul_le_mul (mul_le_mul hG.2 hP.2 hP0 (hG0.trans hG.2)) hE.2 hE0
      (mul_nonneg (hG0.trans hG.2) (hP0.trans hP.2))) hB.2 hB0
    (mul_nonneg (mul_nonneg (hG0.trans hG.2) (hP0.trans hP.2)) (hE0.trans hE.2))
  have hs0 : 0 ≤ (xiGridArgument k : ℝ) / 2 := by positivity
  have hlo' := mul_le_mul_of_nonneg_left hlo hs0
  have hup' := mul_le_mul_of_nonneg_left hup hs0
  have hxi := xi_re_eq_etaIntegral (xiGridArgument k : ℝ) hs hs1
  push_cast at hxi
  unfold ratXiGridLower ratXiGridUpper
  rw [if_neg hk, if_neg hk]
  push_cast
  rw [hxi]
  change _ ≤ _ ∧ _ ≤ _
  unfold xiEtaBracket at hlo' hup'
  constructor
  · convert hlo' using 1; ring
  · convert hup' using 1; ring

/-- The removable node is evaluated exactly, so it needs no denominator check. -/
theorem ratXiGrid_enclosure (k : ℕ) (p : XiEvalParams)
    (hc : k ≠ 40 → XiEvalChecks k p) :
    (ratXiGridLower k p : ℝ) ≤ (xi (xiGridArgument k : ℂ)).re ∧
    (xi (xiGridArgument k : ℂ)).re ≤ (ratXiGridUpper k p : ℝ) := by
  by_cases hk : k = 40
  · subst k
    norm_num [ratXiGridLower, ratXiGridUpper, xiGridArgument, xi_one]
  · exact ratXiGrid_enclosure_of_ne k p hk (hc hk)

def ratReciprocalGridLower (k : ℕ) (p : XiEvalParams) : ℚ :=
  max 0 (ratXiGridLower 0 p) / ratXiGridUpper k p
def ratReciprocalGridUpper (k : ℕ) (p : XiEvalParams) : ℚ :=
  ratXiGridUpper 0 p / ratXiGridLower k p

theorem reciprocalTransform_grid_re (k : ℕ) :
    (reciprocalTransform ((k : ℝ) / 40)).re =
      (xi (xiGridArgument 0 : ℂ)).re / (xi (xiGridArgument k : ℂ)).re := by
  rw [reciprocalTransform_eq_real_ratio, Complex.ofReal_re]
  have he : (1 + (k : ℝ) / 40) / 2 = (xiGridArgument k : ℝ) := by
    unfold xiGridArgument
    push_cast
    ring
  rw [he]
  push_cast
  norm_num [xiGridArgument]

/-- The actual retained reciprocal-Xi value is enclosed, provided every
explicit rational evaluation and positive-denominator check succeeds. -/
theorem ratReciprocalGrid_enclosure (k : ℕ) (p : XiEvalParams)
    (h0 : XiEvalChecks 0 p) (hk : k ≠ 40 → XiEvalChecks k p)
    (hd : 0 < ratXiGridLower k p) :
    (ratReciprocalGridLower k p : ℝ) ≤ (reciprocalTransform ((k : ℝ) / 40)).re ∧
    (reciprocalTransform ((k : ℝ) / 40)).re ≤ (ratReciprocalGridUpper k p : ℝ) := by
  have hN := ratXiGrid_enclosure 0 p (fun _ => h0)
  have hD := ratXiGrid_enclosure k p hk
  have hdR : 0 < (ratXiGridLower k p : ℝ) := by exact_mod_cast hd
  have hden := hdR.trans_le hD.1
  have hupper := hden.trans_le hD.2
  have hnum : 0 ≤ (xi (xiGridArgument 0 : ℂ)).re := by
    have h := (xi_re_pos (xiGridArgument 0 : ℝ)).le
    push_cast at h
    exact h
  have hmax := max_le hnum hN.1
  unfold ratReciprocalGridLower ratReciprocalGridUpper
  push_cast
  rw [reciprocalTransform_grid_re]
  constructor
  · exact (div_le_div_of_nonneg_right hmax hupper.le).trans
      (div_le_div_of_nonneg_left hnum hden hD.2)
  · exact (div_le_div_of_nonneg_right hN.2 hden.le).trans
      (div_le_div_of_nonneg_left (hnum.trans hN.2) hdR hD.1)

end ReciprocalXi

