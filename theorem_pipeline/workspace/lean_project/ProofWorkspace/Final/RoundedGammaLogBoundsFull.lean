import ProofWorkspace.Final.RationalGammaBoundsFull
import ProofWorkspace.Final.RationalRoundingBoundsFull
import ProofWorkspace.Final.PiPowerBoundsFull

/-!
# Rounded actual integer-zeta and log-Gamma enclosures

Each finite eta summand and each signed Gamma coefficient term is rounded
outward before addition. The actual analytic eta/Gamma remainders remain
in the bounds, and final endpoints are returned to the fixed rational grid.
-/

set_option autoImplicit false

namespace ReciprocalXi

def ratEtaIntegerTerm (M k j : ℕ) : ℚ :=
  (-1 : ℚ) ^ j * ratEtaEulerWeight M j / ((j : ℚ) + 1) ^ k

def ratEtaIntegerRoundedLower (M k B : ℕ) : ℚ :=
  ∑ j ∈ Finset.range M, ratRoundLower (ratEtaIntegerTerm M k j) B

def ratEtaIntegerRoundedUpper (M k B : ℕ) : ℚ :=
  ∑ j ∈ Finset.range M, ratRoundUpper (ratEtaIntegerTerm M k j) B

theorem ratEtaIntegerRounded_enclosure (M k B : ℕ) (hB : 0 < B) :
    ratEtaIntegerRoundedLower M k B ≤ ratEtaNatSum M k ∧
      ratEtaNatSum M k ≤ ratEtaIntegerRoundedUpper M k B := by
  unfold ratEtaIntegerRoundedLower ratEtaIntegerRoundedUpper ratEtaNatSum
  constructor <;> apply Finset.sum_le_sum <;> intro j hj
  · exact (ratRound_enclosure (ratEtaIntegerTerm M k j) B hB).1
  · exact (ratRound_enclosure (ratEtaIntegerTerm M k j) B hB).2

def ratZetaNatRoundedLower (M k B : ℕ) : ℚ :=
  ratRoundLower (ratZetaNatFactor k * ratEtaIntegerRoundedLower M k B) B

def ratZetaNatRoundedUpper (M k B : ℕ) : ℚ :=
  ratRoundUpper (ratZetaNatFactor k * ratEtaIntegerRoundedUpper M k B + 2 / (2 : ℚ) ^ M) B

/-- Per-term rounding keeps the finite integer-zeta computation on a fixed
grid without replacing or assuming the actual analytic eta remainder. -/
theorem ratZetaNatRounded_enclosure (M k B : ℕ) (hk : 2 ≤ k) (hB : 0 < B) :
    (ratZetaNatRoundedLower M k B : ℝ) ≤ (riemannZeta (k : ℂ)).re ∧
      (riemannZeta (k : ℂ)).re ≤ (ratZetaNatRoundedUpper M k B : ℝ) := by
  have hs := ratEtaIntegerRounded_enclosure M k B hB
  have hf := (ratZetaNatFactor_pos k hk).le
  have hz := ratZetaNat_enclosure M k hk
  have hlq : ratZetaNatFactor k * ratEtaIntegerRoundedLower M k B ≤ ratZetaNatLower M k :=
    mul_le_mul_of_nonneg_left hs.1 hf
  have huq : ratZetaNatUpper M k ≤
      ratZetaNatFactor k * ratEtaIntegerRoundedUpper M k B + 2 / (2 : ℚ) ^ M := by
    change ratZetaNatFactor k * ratEtaNatSum M k + 2 / (2 : ℚ) ^ M ≤ _
    exact add_le_add (mul_le_mul_of_nonneg_left hs.2 hf) le_rfl
  have hl : ((ratZetaNatFactor k * ratEtaIntegerRoundedLower M k B : ℚ) : ℝ) ≤
      (riemannZeta (k : ℂ)).re := ((Rat.cast_le (K := ℝ)).mpr hlq).trans hz.1
  have hu : (riemannZeta (k : ℂ)).re ≤
      ((ratZetaNatFactor k * ratEtaIntegerRoundedUpper M k B + 2 / (2 : ℚ) ^ M : ℚ) : ℝ) :=
    hz.2.trans ((Rat.cast_le (K := ℝ)).mpr huq)
  exact ratRound_interval_enclosure _ _ _ B hB hl hu

private theorem signedRoundedProduct_enclosure (c a b : ℚ) (x : ℝ) (B : ℕ)
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

def ratGammaCoefficientRoundedLower (z : ℚ) (k M B : ℕ) : ℚ :=
  ratRoundLower (min
    (ratGammaLogCoefficient z k * ratZetaNatRoundedLower M (k + 2) B)
    (ratGammaLogCoefficient z k * ratZetaNatRoundedUpper M (k + 2) B)) B

def ratGammaCoefficientRoundedUpper (z : ℚ) (k M B : ℕ) : ℚ :=
  ratRoundUpper (max
    (ratGammaLogCoefficient z k * ratZetaNatRoundedLower M (k + 2) B)
    (ratGammaLogCoefficient z k * ratZetaNatRoundedUpper M (k + 2) B)) B

theorem ratGammaCoefficientRounded_enclosure (z : ℚ) (k M B : ℕ) (hB : 0 < B) :
    (ratGammaCoefficientRoundedLower z k M B : ℝ) ≤
        gammaLogTaylorCoefficient (z : ℝ) k * (riemannZeta ((k + 2 : ℕ) : ℂ)).re ∧
      gammaLogTaylorCoefficient (z : ℝ) k * (riemannZeta ((k + 2 : ℕ) : ℂ)).re ≤
        (ratGammaCoefficientRoundedUpper z k M B : ℝ) := by
  have hz := ratZetaNatRounded_enclosure M (k + 2) B (by omega) hB
  have h := signedRoundedProduct_enclosure (ratGammaLogCoefficient z k) _ _ _ B hB hz.1 hz.2
  rw [ratGammaLogCoefficient_cast] at h
  exact h

def ratGammaConstantRoundedLower (z : ℚ) (L B : ℕ) : ℚ :=
  ratRoundLower (ratPiPowerLogLower z L) B +
    ratRoundLower (min
      ((-2 * z) * (ratLogTaylor 2 L - ratLogError 2 L))
      ((-2 * z) * (ratLogTaylor 2 L + ratLogError 2 L))) B

def ratGammaConstantRoundedUpper (z : ℚ) (L B : ℕ) : ℚ :=
  ratRoundUpper (ratPiPowerLogUpper z L) B +
    ratRoundUpper (max
      ((-2 * z) * (ratLogTaylor 2 L - ratLogError 2 L))
      ((-2 * z) * (ratLogTaylor 2 L + ratLogError 2 L))) B

theorem ratGammaConstantRounded_enclosure (z : ℚ) (L B : ℕ) (hB : 0 < B) :
    (ratGammaConstantRoundedLower z L B : ℝ) ≤
        (z : ℝ) * Real.log Real.pi - 2 * (z : ℝ) * Real.log 2 ∧
      (z : ℝ) * Real.log Real.pi - 2 * (z : ℝ) * Real.log 2 ≤
        (ratGammaConstantRoundedUpper z L B : ℝ) := by
  have hp := ratPiPower_log_enclosure z L
  have hpR := ratRound_interval_enclosure _ _ _ B hB hp.1 hp.2
  have ht := ratLog_enclosure 2 L (by norm_num)
  have htR := signedRoundedProduct_enclosure (-2 * z) _ _ _ B hB ht.1 ht.2
  unfold ratGammaConstantRoundedLower ratGammaConstantRoundedUpper
  push_cast only [Rat.cast_add]
  have he : (z : ℝ) * Real.log Real.pi - 2 * (z : ℝ) * Real.log 2 =
      (z : ℝ) * Real.log Real.pi + ((-2 * z : ℚ) : ℝ) * Real.log (2 : ℚ) := by
    push_cast
    ring
  rw [he]
  exact ⟨add_le_add hpR.1 htR.1, add_le_add hpR.2 htR.2⟩

def ratLogGammaRoundedLower (z : ℚ) (N M L B : ℕ) : ℚ :=
  ratRoundLower (ratGammaConstantRoundedLower z L B +
    (∑ k ∈ Finset.range N, ratGammaCoefficientRoundedLower z k M B) -
    8 * (1 / 2 : ℚ) ^ (N + 2)) B

def ratLogGammaRoundedUpper (z : ℚ) (N M L B : ℕ) : ℚ :=
  ratRoundUpper (ratGammaConstantRoundedUpper z L B +
    (∑ k ∈ Finset.range N, ratGammaCoefficientRoundedUpper z k M B) +
    8 * (1 / 2 : ℚ) ^ (N + 2)) B

/-- An actual log-Gamma enclosure with outward-rounded integer-zeta sums
and outward-rounded signed Gamma coefficient terms. -/
theorem ratLogGammaRounded_enclosure (z : ℚ) (N M L B : ℕ)
    (hz : |z| ≤ 1 / 2) (hB : 0 < B) :
    (ratLogGammaRoundedLower z N M L B : ℝ) ≤ Real.log (Real.Gamma (1 + (z : ℝ))) ∧
      Real.log (Real.Gamma (1 + (z : ℝ))) ≤ (ratLogGammaRoundedUpper z N M L B : ℝ) := by
  have hzR : |(z : ℝ)| ≤ 1 / 2 := by
    have hc : ((|z| : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := Rat.cast_le.mpr hz
    simpa only [Rat.cast_abs, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hc
  have he := abs_le.mp (logGamma_approx_error_bound (z : ℝ) N hzR)
  have hc := ratGammaConstantRounded_enclosure z L B hB
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
  unfold ratLogGammaRoundedLower ratLogGammaRoundedUpper
  apply ratRound_interval_enclosure _ _ _ B hB
  · push_cast at hlo hup ⊢
    linarith [he.1, he.2, hc.1, hc.2]
  · push_cast at hlo hup ⊢
    linarith [he.1, he.2, hc.1, hc.2]

end ReciprocalXi
