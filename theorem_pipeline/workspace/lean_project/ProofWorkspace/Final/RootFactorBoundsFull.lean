import ProofWorkspace.Final.RootPowerStreamFull
import ProofWorkspace.Final.SourcePiMidpointFull

set_option autoImplicit false
noncomputable section
namespace ReciprocalXi

theorem real_root160_enclosure (a l u : ℝ) (ha : 0 < a)
    (hl : 0 ≤ l) (hu : 0 ≤ u) (hlo : a*l^160 ≤ 1) (hup : 1 ≤ a*u^160) :
    l ≤ a^(-(1/160):ℝ) ∧ a^(-(1/160):ℝ) ≤ u := by
  have hx : 0 ≤ a^(-(1/160):ℝ) := (Real.rpow_pos_of_pos ha _).le
  have hx160 : (a^(-(1/160):ℝ))^160 = 1/a := by
    calc
      _ = a^((-(1/160):ℝ)*(160:ℝ)) := by
        rw [Real.rpow_mul ha.le]
        simpa only [Nat.cast_ofNat] using (Real.rpow_natCast (a^(-(1/160):ℝ)) 160).symm
      _ = a^(-1:ℝ) := by congr 1; norm_num
      _ = 1/a := by rw [Real.rpow_neg_one, one_div]
  have hl160 : l^160 ≤ 1/a := (le_div_iff₀ ha).mpr (by nlinarith only [hlo])
  have hu160 : 1/a ≤ u^160 := (div_le_iff₀ ha).mpr (by nlinarith only [hup])
  constructor
  · apply (pow_le_pow_iff_left₀ hl hx (by norm_num : (160:ℕ) ≠ 0)).mp
    simpa only [hx160] using hl160
  · apply (pow_le_pow_iff_left₀ hx hu (by norm_num : (160:ℕ) ≠ 0)).mp
    simpa only [hx160] using hu160

theorem sourcePi_root160_enclosure (l u : ℚ) (hl : 0 ≤ l) (hu : 0 ≤ u)
    (hlo : (sourcePiMidpoint+1/(10:ℚ)^150)*l^160 ≤ 1)
    (hup : 1 ≤ (sourcePiMidpoint-1/(10:ℚ)^150)*u^160) :
    (l:ℝ) ≤ Real.pi^(-(1/160):ℝ) ∧ Real.pi^(-(1/160):ℝ) ≤ (u:ℝ) := by
  have hp := abs_le.mp sourcePiMidpoint_error
  have hloR : ((sourcePiMidpoint:ℝ)+1/(10:ℝ)^150)*(l:ℝ)^160 ≤ 1 := by
    have h : (((sourcePiMidpoint+1/(10:ℚ)^150)*l^160:ℚ):ℝ) ≤ ((1:ℚ):ℝ) := Rat.cast_le.mpr hlo
    push_cast at h
    exact h
  have hupR : 1 ≤ ((sourcePiMidpoint:ℝ)-1/(10:ℝ)^150)*(u:ℝ)^160 := by
    have h : ((1:ℚ):ℝ) ≤ (((sourcePiMidpoint-1/(10:ℚ)^150)*u^160:ℚ):ℝ) := Rat.cast_le.mpr hup
    push_cast at h
    exact h
  apply real_root160_enclosure Real.pi l u Real.pi_pos
    (by exact_mod_cast hl) (by exact_mod_cast hu)
  · exact (mul_le_mul_of_nonneg_right (by linarith : Real.pi ≤
      (sourcePiMidpoint:ℝ)+1/(10:ℝ)^150) (by positivity)).trans hloR
  · exact hupR.trans (mul_le_mul_of_nonneg_right (by linarith :
      (sourcePiMidpoint:ℝ)-1/(10:ℝ)^150 ≤ Real.pi) (by positivity))

theorem rpow_root160_grid (a : ℝ) (ha : 0 < a) (k : ℕ) :
    (a^(-(1/160):ℝ))^(k+40) = a^(-(xiGridArgument k:ℝ)/2) := by
  calc
    _ = a^((-(1/160):ℝ)*(k+40)) := by
      rw [Real.rpow_mul ha.le]
      simpa only [Nat.cast_add, Nat.cast_ofNat] using
        (Real.rpow_natCast (a^(-(1/160):ℝ)) (k+40)).symm
    _ = _ := by congr 1; unfold xiGridArgument; push_cast; ring

theorem ratPiRootGrid_enclosure (l u : ℚ) (k B : ℕ) (hB : 0 < B)
    (hl : 0 ≤ l) (hu : 0 ≤ u)
    (hlo : (sourcePiMidpoint+1/(10:ℚ)^150)*l^160 ≤ 1)
    (hup : 1 ≤ (sourcePiMidpoint-1/(10:ℚ)^150)*u^160) :
    (ratPowRoundLower l B (k+40):ℝ) ≤ Real.pi^(-(xiGridArgument k:ℝ)/2) ∧
      Real.pi^(-(xiGridArgument k:ℝ)/2) ≤ (ratPowRoundUpper u B (k+40):ℝ) := by
  have h := sourcePi_root160_enclosure l u hl hu hlo hup
  have he := ratPowRound_enclosure l u (Real.pi^(-(1/160):ℝ)) B (k+40)
    hB hl h.1 h.2
  rw [rpow_root160_grid Real.pi Real.pi_pos k] at he
  exact he

def ratRootDenominatorLower (s l u : ℚ) : ℚ := if s < 1 then 2*l-1 else 1-2*u
def ratRootDenominatorUpper (s l u : ℚ) : ℚ := if s < 1 then 2*u-1 else 1-2*l
def ratRootBracketLower (s l u : ℚ) : ℚ := |s-1|/ratRootDenominatorUpper s l u
def ratRootBracketUpper (s l u : ℚ) : ℚ := |s-1|/ratRootDenominatorLower s l u

theorem root_two_power_identity (s : ℝ) : (2:ℝ)^(1-s) = 2*(2:ℝ)^(-s) := by
  rw [sub_eq_add_neg, Real.rpow_add (by norm_num)]
  simp

theorem ratRootDenominator_enclosure (s l u : ℚ) (hs1 : s ≠ 1)
    (hl : (l:ℝ) ≤ (2:ℝ)^(-(s:ℝ))) (hu : (2:ℝ)^(-(s:ℝ)) ≤ (u:ℝ)) :
    (ratRootDenominatorLower s l u:ℝ) ≤ |1-(2:ℝ)^(1-(s:ℝ))| ∧
      |1-(2:ℝ)^(1-(s:ℝ))| ≤ (ratRootDenominatorUpper s l u:ℝ) := by
  unfold ratRootDenominatorLower ratRootDenominatorUpper
  split_ifs with hs
  · have hsR : (s:ℝ) < 1 := by exact_mod_cast hs
    rw [abs_of_neg (xiEta_denominator_neg_of_lt_one _ hsR), root_two_power_identity]
    push_cast
    constructor <;> linarith
  · have hsR : 1 < (s:ℝ) := by
      exact_mod_cast (lt_of_le_of_ne (not_lt.mp hs) (Ne.symm hs1))
    rw [abs_of_pos (xiEta_denominator_pos_of_one_lt _ hsR), root_two_power_identity]
    push_cast
    constructor <;> linarith

theorem ratRootBracket_enclosure (s l u : ℚ) (hs1 : s ≠ 1)
    (hl : (l:ℝ) ≤ (2:ℝ)^(-(s:ℝ))) (hu : (2:ℝ)^(-(s:ℝ)) ≤ (u:ℝ))
    (hd : 0 < ratRootDenominatorLower s l u) :
    (ratRootBracketLower s l u:ℝ) ≤ xiEtaBracket (s:ℝ) ∧
      xiEtaBracket (s:ℝ) ≤ (ratRootBracketUpper s l u:ℝ) := by
  have h := ratRootDenominator_enclosure s l u hs1 hl hu
  have hdR : 0 < (ratRootDenominatorLower s l u:ℝ) := by exact_mod_cast hd
  have ha : 0 < |1-(2:ℝ)^(1-(s:ℝ))| := hdR.trans_le h.1
  rw [xiEtaBracket_eq_abs _ (by exact_mod_cast hs1)]
  unfold ratRootBracketLower ratRootBracketUpper
  push_cast
  exact ⟨div_le_div_of_nonneg_left (abs_nonneg _) ha h.2,
    div_le_div_of_nonneg_left (abs_nonneg _) hdR h.1⟩

def ratFactorXiLower (s g p e b : ℚ) (B : ℕ) : ℚ :=
  ratRoundLower ((s/2)*(max 0 g * max 0 p * max 0 e * max 0 b)) B

def ratFactorXiUpper (s g p e b : ℚ) (B : ℕ) : ℚ :=
  ratRoundUpper ((s/2)*(g*p*e*b)) B

theorem ratFactorXi_enclosure (s gL gU pL pU eL eU bL bU : ℚ) (B : ℕ)
    (hs : 0 < s) (hs1 : s ≠ 1) (hB : 0 < B)
    (hG : (gL:ℝ) ≤ Real.Gamma ((s:ℝ)/2) ∧ Real.Gamma ((s:ℝ)/2) ≤ (gU:ℝ))
    (hP : (pL:ℝ) ≤ Real.pi^(-(s:ℝ)/2) ∧ Real.pi^(-(s:ℝ)/2) ≤ (pU:ℝ))
    (hE : (eL:ℝ) ≤ etaIntegral (s:ℝ) ∧ etaIntegral (s:ℝ) ≤ (eU:ℝ))
    (hF : (bL:ℝ) ≤ xiEtaBracket (s:ℝ) ∧ xiEtaBracket (s:ℝ) ≤ (bU:ℝ)) :
    (ratFactorXiLower s gL pL eL bL B:ℝ) ≤ (xi (s:ℂ)).re ∧
      (xi (s:ℂ)).re ≤ (ratFactorXiUpper s gU pU eU bU B:ℝ) := by
  have hsR : 0 < (s:ℝ) := by exact_mod_cast hs
  have hs1R : (s:ℝ) ≠ 1 := by exact_mod_cast hs1
  have hG0 := (Real.Gamma_pos_of_pos (show 0 < (s:ℝ)/2 by positivity)).le
  have hP0 := Real.rpow_nonneg Real.pi_pos.le (-(s:ℝ)/2)
  have hE0 : 0 ≤ etaIntegral (s:ℝ) := by
    simpa [etaEulerApprox] using (etaIntegral_euler_error_bounds 0 (s:ℝ) hsR).1
  have hF0 := (xiEtaBracket_pos (s:ℝ) hs1R).le
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
  have hlo' := mul_le_mul_of_nonneg_left hlo (show 0 ≤ (s:ℝ)/2 by positivity)
  have hup' := mul_le_mul_of_nonneg_left hup (show 0 ≤ (s:ℝ)/2 by positivity)
  have hxi := xi_re_eq_etaIntegral (s:ℝ) hsR hs1R
  push_cast at hxi
  unfold ratFactorXiLower ratFactorXiUpper
  apply ratRound_interval_enclosure _ _ _ B hB
  · push_cast
    rw [hxi]
    unfold xiEtaBracket at hlo'
    convert hlo' using 1; ring
  · push_cast
    rw [hxi]
    unfold xiEtaBracket at hup'
    convert hup' using 1; ring

end ReciprocalXi

