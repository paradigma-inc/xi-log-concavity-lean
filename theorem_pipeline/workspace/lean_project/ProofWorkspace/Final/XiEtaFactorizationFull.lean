import ProofWorkspace.Final.EtaContinuationFull

/-!
# Actual positive-real Xi factorization through eta

The previously proved actual Mellin continuation identifies Xi with a real
eta/Gamma/power expression. Denominator nonvanishing and its sign are proved
for all real arguments away from one; no numerical identity is assumed.
-/

set_option autoImplicit false

noncomputable section
namespace ReciprocalXi

def xiEtaBracket (s : ℝ) : ℝ := (s - 1) / (1 - (2 : ℝ) ^ (1 - s))

theorem xiEta_denominator_neg_of_lt_one (s : ℝ) (hs : s < 1) :
    1 - (2 : ℝ) ^ (1 - s) < 0 := by
  have hp := Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) (by linarith : 0 < 1 - s)
  linarith

theorem xiEta_denominator_pos_of_one_lt (s : ℝ) (hs : 1 < s) :
    0 < 1 - (2 : ℝ) ^ (1 - s) := by
  have hp := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2)
    (by linarith : 1 - s < 0)
  linarith

theorem xiEta_denominator_ne_zero (s : ℝ) (hs1 : s ≠ 1) :
    1 - (2 : ℝ) ^ (1 - s) ≠ 0 := by
  rcases lt_or_gt_of_ne hs1 with hs | hs
  · have hp := Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) (by linarith : 0 < 1 - s)
    linarith
  · have hp := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2)
      (by linarith : 1 - s < 0)
    linarith

theorem xiEtaBracket_pos (s : ℝ) (hs1 : s ≠ 1) : 0 < xiEtaBracket s := by
  unfold xiEtaBracket
  rcases lt_or_gt_of_ne hs1 with hs | hs
  · have hp := Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) (by linarith : 0 < 1 - s)
    exact div_pos_of_neg_of_neg (by linarith) (by linarith)
  · have hp := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2)
      (by linarith : 1 - s < 0)
    exact div_pos (by linarith) (by linarith)

theorem xiEtaBracket_eq_abs (s : ℝ) (hs1 : s ≠ 1) :
    xiEtaBracket s = |s - 1| / |1 - (2 : ℝ) ^ (1 - s)| := by
  calc
    xiEtaBracket s = |xiEtaBracket s| := (abs_of_pos (xiEtaBracket_pos s hs1)).symm
    _ = _ := abs_div _ _

theorem GammaReal_ofReal_eq (s : ℝ) :
    Complex.Gammaℝ (s : ℂ) =
      ((Real.pi ^ (-s / 2) * Real.Gamma (s / 2) : ℝ) : ℂ) := by
  rw [Complex.Gammaℝ_def]
  have hp : (Real.pi : ℂ) ^ (-(s : ℂ) / 2) = ((Real.pi ^ (-s / 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow Real.pi_pos.le]
    push_cast
    rfl
  rw [hp]
  have hG : Complex.Gamma ((s : ℂ) / 2) = (Real.Gamma (s / 2) : ℂ) := by
    rw [← Complex.ofReal_ofNat 2, ← Complex.ofReal_div, Complex.Gamma_ofReal]
  rw [hG, Complex.ofReal_mul]

/-- The actual entire Xi value equals a real eta/Gamma expression on the
positive real line away from the removable point. -/
theorem xi_eq_etaIntegral (s : ℝ) (hs : 0 < s) (hs1 : s ≠ 1) :
    xi (s : ℂ) =
      ((s * Real.Gamma (s / 2) * Real.pi ^ (-s / 2) * etaIntegral s *
        xiEtaBracket s / 2 : ℝ) : ℂ) := by
  have he := complexEtaIntegral_regularized (s : ℂ) (by simpa using hs)
  rw [complexEtaIntegral_ofReal, etaRegularizedXi, GammaReal_ofReal_eq] at he
  have hp : (2 : ℂ) ^ (1 - (s : ℂ)) = (((2 : ℝ) ^ (1 - s) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 2),
      Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_ofNat]
  rw [hp] at he
  have hG : Complex.Gammaℝ (s : ℂ) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by simpa using hs)
  rw [GammaReal_ofReal_eq] at hG
  have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hs)
  have hd : (1 : ℂ) - (((2 : ℝ) ^ (1 - s) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast xiEta_denominator_ne_zero s hs1
  have he' := (eq_div_iff (mul_ne_zero hs0 hG)).mp he
  unfold xiEtaBracket
  push_cast at he' ⊢
  field_simp [hd]
  simp only [neg_div] at he'
  linear_combination -he'

theorem xi_re_eq_etaIntegral (s : ℝ) (hs : 0 < s) (hs1 : s ≠ 1) :
    (xi (s : ℂ)).re =
      s * Real.Gamma (s / 2) * Real.pi ^ (-s / 2) * etaIntegral s *
        ((s - 1) / (1 - (2 : ℝ) ^ (1 - s))) / 2 := by
  rw [xi_eq_etaIntegral s hs hs1]
  rfl

end ReciprocalXi
