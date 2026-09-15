import ProofWorkspace.Final.RoundedTaylorBoundsFull
import ProofWorkspace.Final.RoundedGammaLogBoundsFull
import ProofWorkspace.Final.GammaGridBoundsFull
import ProofWorkspace.Final.PiPowerBoundsFull
import ProofWorkspace.Final.RationalPowerDyadicBoundsFull

/-! Actual Gamma and real-power intervals using rounded log-Gamma sums and
fully rounded Taylor exponentials. All interval hypotheses are rational checks;
no special-function approximation is assumed. -/

set_option autoImplicit false

namespace ReciprocalXi

def ratGammaRoundedLower (z : ℚ) (N M L m n B : ℕ) : ℚ :=
  ratExpFullyRoundedLower (ratLogGammaRoundedLower z N M L B) m n B

def ratGammaRoundedUpper (z : ℚ) (N M L m n B : ℕ) : ℚ :=
  ratExpFullyRoundedUpper (ratLogGammaRoundedUpper z N M L B) m n B

theorem ratGammaRounded_enclosure (z : ℚ) (N M L m n B : ℕ) (hz : |z| ≤ 1 / 2)
    (hm : 0 < m) (hn : 0 < n) (hB : 0 < B)
    (hl : |ratLogGammaRoundedLower z N M L B / m| ≤ 1)
    (hu : |ratLogGammaRoundedUpper z N M L B / m| ≤ 1) :
    (ratGammaRoundedLower z N M L m n B : ℝ) ≤ Real.Gamma (1 + (z : ℝ)) ∧
      Real.Gamma (1 + (z : ℝ)) ≤ (ratGammaRoundedUpper z N M L m n B : ℝ) := by
  have h := ratLogGammaRounded_enclosure z N M L B hz hB
  have hlo := ratExpFullyRounded_enclosure (ratLogGammaRoundedLower z N M L B) m n B hm hn hB hl
  have hup := ratExpFullyRounded_enclosure (ratLogGammaRoundedUpper z N M L B) m n B hm hn hB hu
  have hzR : |(z : ℝ)| ≤ 1 / 2 := by
    have hc : ((|z| : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := Rat.cast_le.mpr hz
    simpa only [Rat.cast_abs, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hc
  have hg : 0 < Real.Gamma (1 + (z : ℝ)) :=
    Real.Gamma_pos_of_pos (by linarith [(abs_le.mp hzR).1])
  have he := Real.exp_log hg
  exact ⟨hlo.1.trans ((Real.exp_le_exp.mpr h.1).trans_eq he),
    (he.symm.trans_le (Real.exp_le_exp.mpr h.2)).trans hup.2⟩

def ratGammaGridRoundedLower (k N M L m n B : ℕ) : ℚ :=
  ratRoundLower (gammaGridMultiplier k *
    ratGammaRoundedLower (gammaGridOffset k) N M L m n B) B

def ratGammaGridRoundedUpper (k N M L m n B : ℕ) : ℚ :=
  ratRoundUpper (gammaGridMultiplier k *
    ratGammaRoundedUpper (gammaGridOffset k) N M L m n B) B

theorem ratGammaGridRounded_enclosure (k N M L m n B : ℕ)
    (hm : 0 < m) (hn : 0 < n) (hB : 0 < B)
    (hl : |ratLogGammaRoundedLower (gammaGridOffset k) N M L B / m| ≤ 1)
    (hu : |ratLogGammaRoundedUpper (gammaGridOffset k) N M L B / m| ≤ 1) :
    (ratGammaGridRoundedLower k N M L m n B : ℝ) ≤ Real.Gamma (gammaGridArgument k : ℝ) ∧
      Real.Gamma (gammaGridArgument k : ℝ) ≤ (ratGammaGridRoundedUpper k N M L m n B : ℝ) := by
  have h := ratGammaRounded_enclosure (gammaGridOffset k) N M L m n B
    (gammaGridOffset_bounds k) hm hn hB hl hu
  have hp : 0 ≤ (gammaGridMultiplier k : ℝ) := by
    exact_mod_cast (gammaGridMultiplier_pos k).le
  have hlow : ((gammaGridMultiplier k *
      ratGammaRoundedLower (gammaGridOffset k) N M L m n B : ℚ) : ℝ) ≤
      Real.Gamma (gammaGridArgument k : ℝ) := by
    push_cast
    rw [gammaGrid_recurrence]
    exact mul_le_mul_of_nonneg_left h.1 hp
  have hupp : Real.Gamma (gammaGridArgument k : ℝ) ≤
      ((gammaGridMultiplier k * ratGammaRoundedUpper (gammaGridOffset k) N M L m n B : ℚ) : ℝ) := by
    push_cast
    rw [gammaGrid_recurrence]
    exact mul_le_mul_of_nonneg_left h.2 hp
  exact ratRound_interval_enclosure _ _ _ B hB hlow hupp

def ratPiPowerRoundedLower (r : ℚ) (L m n B : ℕ) : ℚ :=
  ratExpFullyRoundedLower (ratPiPowerLogLower r L) m n B

def ratPiPowerRoundedUpper (r : ℚ) (L m n B : ℕ) : ℚ :=
  ratExpFullyRoundedUpper (ratPiPowerLogUpper r L) m n B

theorem ratPiPowerRounded_enclosure (r : ℚ) (L m n B : ℕ)
    (hm : 0 < m) (hn : 0 < n) (hB : 0 < B)
    (hl : |ratPiPowerLogLower r L / m| ≤ 1)
    (hu : |ratPiPowerLogUpper r L / m| ≤ 1) :
    (ratPiPowerRoundedLower r L m n B : ℝ) ≤ Real.pi ^ (r : ℝ) ∧
      Real.pi ^ (r : ℝ) ≤ (ratPiPowerRoundedUpper r L m n B : ℝ) := by
  have h := ratPiPower_log_enclosure r L
  have hlo := ratExpFullyRounded_enclosure (ratPiPowerLogLower r L) m n B hm hn hB hl
  have hup := ratExpFullyRounded_enclosure (ratPiPowerLogUpper r L) m n B hm hn hB hu
  rw [Real.rpow_def_of_pos Real.pi_pos, mul_comm (Real.log Real.pi)]
  exact ⟨hlo.1.trans (Real.exp_le_exp.mpr h.1),
    (Real.exp_le_exp.mpr h.2).trans hup.2⟩

def ratPowerDyadicRoundedLower (r q : ℚ) (d nLog m nExp B : ℕ) : ℚ :=
  ratExpFullyRoundedLower (ratPowerDyadicLogLower r q d nLog) m nExp B

def ratPowerDyadicRoundedUpper (r q : ℚ) (d nLog m nExp B : ℕ) : ℚ :=
  ratExpFullyRoundedUpper (ratPowerDyadicLogUpper r q d nLog) m nExp B

theorem ratPowerDyadicRounded_enclosure (r q : ℚ) (d nLog m nExp B : ℕ)
    (hr : 0 < r) (hm : 0 < m) (hn : 0 < nExp) (hB : 0 < B)
    (hl : |ratPowerDyadicLogLower r q d nLog / m| ≤ 1)
    (hu : |ratPowerDyadicLogUpper r q d nLog / m| ≤ 1) :
    (ratPowerDyadicRoundedLower r q d nLog m nExp B : ℝ) ≤
        (((2 : ℚ) ^ d * r : ℚ) : ℝ) ^ (q : ℝ) ∧
      (((2 : ℚ) ^ d * r : ℚ) : ℝ) ^ (q : ℝ) ≤
        (ratPowerDyadicRoundedUpper r q d nLog m nExp B : ℝ) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have ha : (0 : ℝ) < (((2 : ℚ) ^ d * r : ℚ) : ℝ) := by
    push_cast
    positivity
  have hp := ratPowerDyadic_log_enclosure r q d nLog hr
  have hlo := ratExpFullyRounded_enclosure (ratPowerDyadicLogLower r q d nLog) m nExp B hm hn hB hl
  have hup := ratExpFullyRounded_enclosure (ratPowerDyadicLogUpper r q d nLog) m nExp B hm hn hB hu
  rw [Real.rpow_def_of_pos ha, mul_comm (Real.log _)]
  exact ⟨hlo.1.trans (Real.exp_le_exp.mpr hp.1),
    (Real.exp_le_exp.mpr hp.2).trans hup.2⟩

def ratPowerNatRoundedLower (a : ℕ) (q : ℚ) (nLog m nExp B : ℕ) : ℚ :=
  ratPowerDyadicRoundedLower (ratPowerNatMantissa a) q (Nat.log2 a) nLog m nExp B

def ratPowerNatRoundedUpper (a : ℕ) (q : ℚ) (nLog m nExp B : ℕ) : ℚ :=
  ratPowerDyadicRoundedUpper (ratPowerNatMantissa a) q (Nat.log2 a) nLog m nExp B

theorem ratPowerNatRounded_enclosure (a : ℕ) (q : ℚ) (nLog m nExp B : ℕ)
    (ha : 0 < a) (hm : 0 < m) (hn : 0 < nExp) (hB : 0 < B)
    (hl : |ratPowerDyadicLogLower (ratPowerNatMantissa a) q (Nat.log2 a) nLog / m| ≤ 1)
    (hu : |ratPowerDyadicLogUpper (ratPowerNatMantissa a) q (Nat.log2 a) nLog / m| ≤ 1) :
    (ratPowerNatRoundedLower a q nLog m nExp B : ℝ) ≤ (a : ℝ) ^ (q : ℝ) ∧
      (a : ℝ) ^ (q : ℝ) ≤ (ratPowerNatRoundedUpper a q nLog m nExp B : ℝ) := by
  have h := ratPowerDyadicRounded_enclosure (ratPowerNatMantissa a) q (Nat.log2 a) nLog m nExp B
    (ratPowerNatMantissa_pos a ha) hm hn hB hl hu
  rw [ratPowerNat_decomposition] at h
  simpa only [Rat.cast_natCast] using h

end ReciprocalXi

