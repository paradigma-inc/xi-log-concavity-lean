import ProofWorkspace.Final.RoundedLogBoundsFull
import ProofWorkspace.Final.RoundedSpecialFunctionBoundsFull

/-! Actual Gamma and pi-power intervals using rounded logarithmic constants,
rounded integer-zeta coefficient sums, and fully rounded exponentials. -/

set_option autoImplicit false

namespace ReciprocalXi

private theorem fastSignedRoundedProduct_enclosure (c a b : ℚ) (x : ℝ) (B : ℕ)
    (hB : 0 < B) (hl : (a : ℝ) ≤ x) (hu : x ≤ (b : ℝ)) :
    (ratRoundLower (min (c * a) (c * b)) B : ℝ) ≤ (c : ℝ) * x ∧
      (c : ℝ) * x ≤ (ratRoundUpper (max (c * a) (c * b)) B : ℝ) := by
  have h : ((min (c * a) (c * b) : ℚ) : ℝ) ≤ (c : ℝ) * x ∧
      (c : ℝ) * x ≤ ((max (c * a) (c * b) : ℚ) : ℝ) := by
    push_cast
    rcases le_total (0 : ℝ) (c : ℝ) with hc | hc
    · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_left hl hc),
        (mul_le_mul_of_nonneg_left hu hc).trans (le_max_right _ _)⟩
    · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left hu hc),
        (mul_le_mul_of_nonpos_left hl hc).trans (le_max_left _ _)⟩
  exact ratRound_interval_enclosure _ _ _ B hB h.1 h.2


def ratPiPowerLogFastLower (q : ℚ) (L B : ℕ) : ℚ :=
  ratRoundLower (min (q * ratPiLogFullyRoundedLower L B)
    (q * ratPiLogFullyRoundedUpper L B)) B

def ratPiPowerLogFastUpper (q : ℚ) (L B : ℕ) : ℚ :=
  ratRoundUpper (max (q * ratPiLogFullyRoundedLower L B)
    (q * ratPiLogFullyRoundedUpper L B)) B

theorem ratPiPowerLogFast_enclosure (q : ℚ) (L B : ℕ) (hB : 0 < B) :
    (ratPiPowerLogFastLower q L B : ℝ) ≤ (q : ℝ) * Real.log Real.pi ∧
      (q : ℝ) * Real.log Real.pi ≤ (ratPiPowerLogFastUpper q L B : ℝ) := by
  have h := ratPiLogFullyRounded_enclosure L B hB
  exact fastSignedRoundedProduct_enclosure q _ _ _ B hB h.1 h.2

def ratGammaConstantFastLower (z : ℚ) (L B : ℕ) : ℚ :=
  ratPiPowerLogFastLower z L B +
    ratRoundLower (min
      ((-2 * z) * ratLogFullyRoundedLower 2 (1/3) L B)
      ((-2 * z) * ratLogFullyRoundedUpper 2 (1/3) L B)) B

def ratGammaConstantFastUpper (z : ℚ) (L B : ℕ) : ℚ :=
  ratPiPowerLogFastUpper z L B +
    ratRoundUpper (max
      ((-2 * z) * ratLogFullyRoundedLower 2 (1/3) L B)
      ((-2 * z) * ratLogFullyRoundedUpper 2 (1/3) L B)) B

theorem ratGammaConstantFast_enclosure (z : ℚ) (L B : ℕ) (hB : 0 < B) :
    (ratGammaConstantFastLower z L B : ℝ) ≤
        (z : ℝ) * Real.log Real.pi - 2 * (z : ℝ) * Real.log 2 ∧
      (z : ℝ) * Real.log Real.pi - 2 * (z : ℝ) * Real.log 2 ≤
        (ratGammaConstantFastUpper z L B : ℝ) := by
  have hp := ratPiPowerLogFast_enclosure z L B hB
  have ht := ratLogFullyRounded_enclosure 2 (1/3) L B
    (by norm_num) hB (by norm_num [ratLogArgument]) (by norm_num)
  have htR := fastSignedRoundedProduct_enclosure (-2*z) _ _ _ B hB ht.1 ht.2
  unfold ratGammaConstantFastLower ratGammaConstantFastUpper
  push_cast only [Rat.cast_add]
  have he : (z : ℝ) * Real.log Real.pi - 2 * (z : ℝ) * Real.log 2 =
      (z : ℝ) * Real.log Real.pi + ((-2*z : ℚ) : ℝ) * Real.log (2 : ℚ) := by
    push_cast
    ring
  rw [he]
  exact ⟨add_le_add hp.1 htR.1, add_le_add hp.2 htR.2⟩

def ratLogGammaFastLower (z : ℚ) (N M L B : ℕ) : ℚ :=
  ratRoundLower (ratGammaConstantFastLower z L B +
    (∑ k ∈ Finset.range N, ratGammaCoefficientRoundedLower z k M B) -
    8 * (1 / 2 : ℚ) ^ (N + 2)) B

def ratLogGammaFastUpper (z : ℚ) (N M L B : ℕ) : ℚ :=
  ratRoundUpper (ratGammaConstantFastUpper z L B +
    (∑ k ∈ Finset.range N, ratGammaCoefficientRoundedUpper z k M B) +
    8 * (1 / 2 : ℚ) ^ (N + 2)) B

/-- An actual log-Gamma enclosure with outward-rounded integer-zeta sums
and outward-rounded signed Gamma coefficient terms. -/
theorem ratLogGammaFast_enclosure (z : ℚ) (N M L B : ℕ)
    (hz : |z| ≤ 1 / 2) (hB : 0 < B) :
    (ratLogGammaFastLower z N M L B : ℝ) ≤ Real.log (Real.Gamma (1 + (z : ℝ))) ∧
      Real.log (Real.Gamma (1 + (z : ℝ))) ≤ (ratLogGammaFastUpper z N M L B : ℝ) := by
  have hzR : |(z : ℝ)| ≤ 1 / 2 := by
    have hc : ((|z| : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := Rat.cast_le.mpr hz
    simpa only [Rat.cast_abs, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hc
  have he := abs_le.mp (logGamma_approx_error_bound (z : ℝ) N hzR)
  have hc := ratGammaConstantFast_enclosure z L B hB
  have hlo : ((∑ k ∈ Finset.range N, ratGammaCoefficientRoundedLower z k M B : ℚ) : ℝ) ≤
      gammaLogSeriesApprox (z : ℝ) N := by
    unfold gammaLogSeriesApprox
    push_cast
    apply Finset.sum_le_sum
    intro k hk
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      (ratGammaCoefficientRounded_enclosure z k M B hB).1
  have hup : gammaLogSeriesApprox (z : ℝ) N ≤
      ((∑ k ∈ Finset.range N, ratGammaCoefficientRoundedUpper z k M B : ℚ) : ℝ) := by
    unfold gammaLogSeriesApprox
    push_cast
    apply Finset.sum_le_sum
    intro k hk
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      (ratGammaCoefficientRounded_enclosure z k M B hB).2
  unfold logGammaApprox at he
  unfold ratLogGammaFastLower ratLogGammaFastUpper
  apply ratRound_interval_enclosure _ _ _ B hB
  · push_cast at hlo hup ⊢
    linarith [he.1, he.2, hc.1, hc.2]
  · push_cast at hlo hup ⊢
    linarith [he.1, he.2, hc.1, hc.2]

def ratGammaFastLower (z : ℚ) (N M L m n B : ℕ) : ℚ :=
  ratExpFullyRoundedLower (ratLogGammaFastLower z N M L B) m n B

def ratGammaFastUpper (z : ℚ) (N M L m n B : ℕ) : ℚ :=
  ratExpFullyRoundedUpper (ratLogGammaFastUpper z N M L B) m n B

theorem ratGammaFast_enclosure (z : ℚ) (N M L m n B : ℕ) (hz : |z| ≤ 1 / 2)
    (hm : 0 < m) (hn : 0 < n) (hB : 0 < B)
    (hl : |ratLogGammaFastLower z N M L B / m| ≤ 1)
    (hu : |ratLogGammaFastUpper z N M L B / m| ≤ 1) :
    (ratGammaFastLower z N M L m n B : ℝ) ≤ Real.Gamma (1 + (z : ℝ)) ∧
      Real.Gamma (1 + (z : ℝ)) ≤ (ratGammaFastUpper z N M L m n B : ℝ) := by
  have h := ratLogGammaFast_enclosure z N M L B hz hB
  have hlo := ratExpFullyRounded_enclosure (ratLogGammaFastLower z N M L B) m n B hm hn hB hl
  have hup := ratExpFullyRounded_enclosure (ratLogGammaFastUpper z N M L B) m n B hm hn hB hu
  have hzR : |(z : ℝ)| ≤ 1 / 2 := by
    have hc : ((|z| : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := Rat.cast_le.mpr hz
    simpa only [Rat.cast_abs, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hc
  have hg : 0 < Real.Gamma (1 + (z : ℝ)) :=
    Real.Gamma_pos_of_pos (by linarith [(abs_le.mp hzR).1])
  have he := Real.exp_log hg
  exact ⟨hlo.1.trans ((Real.exp_le_exp.mpr h.1).trans_eq he),
    (he.symm.trans_le (Real.exp_le_exp.mpr h.2)).trans hup.2⟩

def ratGammaGridFastLower (k N M L m n B : ℕ) : ℚ :=
  ratRoundLower (gammaGridMultiplier k *
    ratGammaFastLower (gammaGridOffset k) N M L m n B) B

def ratGammaGridFastUpper (k N M L m n B : ℕ) : ℚ :=
  ratRoundUpper (gammaGridMultiplier k *
    ratGammaFastUpper (gammaGridOffset k) N M L m n B) B

theorem ratGammaGridFast_enclosure (k N M L m n B : ℕ)
    (hm : 0 < m) (hn : 0 < n) (hB : 0 < B)
    (hl : |ratLogGammaFastLower (gammaGridOffset k) N M L B / m| ≤ 1)
    (hu : |ratLogGammaFastUpper (gammaGridOffset k) N M L B / m| ≤ 1) :
    (ratGammaGridFastLower k N M L m n B : ℝ) ≤ Real.Gamma (gammaGridArgument k : ℝ) ∧
      Real.Gamma (gammaGridArgument k : ℝ) ≤ (ratGammaGridFastUpper k N M L m n B : ℝ) := by
  have h := ratGammaFast_enclosure (gammaGridOffset k) N M L m n B
    (gammaGridOffset_bounds k) hm hn hB hl hu
  have hp : 0 ≤ (gammaGridMultiplier k : ℝ) := by
    exact_mod_cast (gammaGridMultiplier_pos k).le
  have hlow : ((gammaGridMultiplier k *
      ratGammaFastLower (gammaGridOffset k) N M L m n B : ℚ) : ℝ) ≤
      Real.Gamma (gammaGridArgument k : ℝ) := by
    push_cast
    rw [gammaGrid_recurrence]
    exact mul_le_mul_of_nonneg_left h.1 hp
  have hupp : Real.Gamma (gammaGridArgument k : ℝ) ≤
      ((gammaGridMultiplier k * ratGammaFastUpper (gammaGridOffset k) N M L m n B : ℚ) : ℝ) := by
    push_cast
    rw [gammaGrid_recurrence]
    exact mul_le_mul_of_nonneg_left h.2 hp
  exact ratRound_interval_enclosure _ _ _ B hB hlow hupp

def ratPiPowerFastLower (r : ℚ) (L m n B : ℕ) : ℚ :=
  ratExpFullyRoundedLower (ratPiPowerLogFastLower r L B) m n B

def ratPiPowerFastUpper (r : ℚ) (L m n B : ℕ) : ℚ :=
  ratExpFullyRoundedUpper (ratPiPowerLogFastUpper r L B) m n B

theorem ratPiPowerFast_enclosure (r : ℚ) (L m n B : ℕ)
    (hm : 0 < m) (hn : 0 < n) (hB : 0 < B)
    (hl : |ratPiPowerLogFastLower r L B / m| ≤ 1)
    (hu : |ratPiPowerLogFastUpper r L B / m| ≤ 1) :
    (ratPiPowerFastLower r L m n B : ℝ) ≤ Real.pi ^ (r : ℝ) ∧
      Real.pi ^ (r : ℝ) ≤ (ratPiPowerFastUpper r L m n B : ℝ) := by
  have h := ratPiPowerLogFast_enclosure r L B hB
  have hlo := ratExpFullyRounded_enclosure (ratPiPowerLogFastLower r L B) m n B hm hn hB hl
  have hup := ratExpFullyRounded_enclosure (ratPiPowerLogFastUpper r L B) m n B hm hn hB hu
  rw [Real.rpow_def_of_pos Real.pi_pos, mul_comm (Real.log Real.pi)]
  exact ⟨hlo.1.trans (Real.exp_le_exp.mpr h.1),
    (Real.exp_le_exp.mpr h.2).trans hup.2⟩


end ReciprocalXi

