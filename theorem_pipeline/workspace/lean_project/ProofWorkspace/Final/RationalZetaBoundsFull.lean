import ProofWorkspace.Final.EtaAccelerationFull

/-!
# Exact rational integer-zeta evaluator

Finite binomial eta sums give directed rational enclosures for actual zeta at
every integer k>=2. At 480 terms the interval width is below 10^-140. The
proof uses actual eta acceleration and no assumed numerical zeta table.
-/

noncomputable section
open scoped BigOperators
namespace ReciprocalXi

def ratEtaEulerWeight (M j : ℕ) : ℚ :=
  (∑ n ∈ (Finset.range (M + 1)).filter (fun n => j < n), (M.choose n : ℚ)) / 2 ^ M

def ratEtaNatSum (M k : ℕ) : ℚ :=
  ∑ j ∈ Finset.range M, (-1 : ℚ) ^ j * ratEtaEulerWeight M j / ((j : ℚ) + 1) ^ k

def ratZetaNatFactor (k : ℕ) : ℚ := (2 : ℚ) ^ k / (2 ^ k - 2)
def ratZetaNatLower (M k : ℕ) : ℚ := ratZetaNatFactor k * ratEtaNatSum M k
def ratZetaNatUpper (M k : ℕ) : ℚ := ratZetaNatLower M k + 2 / (2 : ℚ) ^ M

theorem ratEtaEulerWeight_cast (M j : ℕ) : (ratEtaEulerWeight M j : ℝ) = etaEulerWeight M j := by
  unfold ratEtaEulerWeight etaEulerWeight
  push_cast
  rfl

theorem ratEtaNatSum_cast (M k : ℕ) : (ratEtaNatSum M k : ℝ) = etaEulerApprox M (k : ℝ) := by
  unfold ratEtaNatSum etaEulerApprox
  push_cast
  simp_rw [ratEtaEulerWeight_cast, Real.rpow_natCast]

theorem ratZetaNatFactor_pos (k : ℕ) (hk : 2 ≤ k) : 0 < ratZetaNatFactor k := by
  have hpow : (4 : ℚ) ≤ 2 ^ k := by
    simpa using pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) hk
  unfold ratZetaNatFactor
  exact div_pos (by positivity) (by linarith)

theorem ratZetaNatFactor_le_two (k : ℕ) (hk : 2 ≤ k) : ratZetaNatFactor k ≤ 2 := by
  have hpow : (4 : ℚ) ≤ 2 ^ k := by
    simpa using pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) hk
  unfold ratZetaNatFactor
  apply (div_le_iff₀ (by linarith : (0 : ℚ) < 2 ^ k - 2)).mpr
  linarith

theorem ratZetaNatFactor_cancel (k : ℕ) (hk : 2 ≤ k) :
    (ratZetaNatFactor k : ℝ) * (1 - (2 : ℝ) ^ (1 - (k : ℝ))) = 1 := by
  have hpow : (4 : ℝ) ≤ 2 ^ k := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk
    norm_num at h
    exact h
  unfold ratZetaNatFactor
  push_cast
  rw [Real.rpow_sub (by norm_num), Real.rpow_one, Real.rpow_natCast]
  have hden : (2 : ℝ) ^ k - 2 ≠ 0 := by linarith
  field_simp

theorem ratZetaNat_enclosure (M k : ℕ) (hk : 2 ≤ k) :
    (ratZetaNatLower M k : ℝ) ≤ (riemannZeta (k : ℂ)).re ∧
      (riemannZeta (k : ℂ)).re ≤ (ratZetaNatUpper M k : ℝ) := by
  have hks : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  have he := riemannZeta_euler_error_bounds M (k : ℝ) hks
  have hc := ratZetaNatFactor_cancel k hk
  have hf : (0 : ℝ) ≤ ratZetaNatFactor k := by exact_mod_cast (ratZetaNatFactor_pos k hk).le
  have hf2 : (ratZetaNatFactor k : ℝ) ≤ 2 := by exact_mod_cast ratZetaNatFactor_le_two k hk
  have hlo := mul_nonneg hf he.1
  have hup := mul_le_mul_of_nonneg_left he.2 hf
  rw [mul_sub, ← mul_assoc, hc, one_mul] at hlo hup
  have herr : (ratZetaNatFactor k : ℝ) * (1 / (2 : ℝ) ^ M) ≤ 2 / (2 : ℝ) ^ M := by
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_right hf2 (by positivity : (0 : ℝ) ≤ 1 / 2 ^ M)
  rw [← ratEtaNatSum_cast M k] at hlo hup
  unfold ratZetaNatUpper ratZetaNatLower
  push_cast
  push_cast at hlo hup
  constructor <;> linarith

theorem ratZetaNat_width (M k : ℕ) :
    ratZetaNatUpper M k - ratZetaNatLower M k = 2 / (2 : ℚ) ^ M := by
  unfold ratZetaNatUpper
  ring

set_option exponentiation.threshold 512 in
theorem ratZetaNat_480_width_lt (k : ℕ) :
    ratZetaNatUpper 480 k - ratZetaNatLower 480 k < 1 / (10 : ℚ) ^ 140 := by
  rw [ratZetaNat_width]
  norm_num

end ReciprocalXi
