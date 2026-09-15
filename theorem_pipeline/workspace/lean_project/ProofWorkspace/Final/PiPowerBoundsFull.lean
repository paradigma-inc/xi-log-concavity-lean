import ProofWorkspace.Final.RationalGammaBoundsFull
import ProofWorkspace.Final.RationalPowerBoundsFull

namespace ReciprocalXi

def ratPiPowerLogLower (r : ℚ) (L : ℕ) : ℚ :=
  min (r * ratGammaPiLogLower L) (r * ratGammaPiLogUpper L)
def ratPiPowerLogUpper (r : ℚ) (L : ℕ) : ℚ :=
  max (r * ratGammaPiLogLower L) (r * ratGammaPiLogUpper L)
def ratPiPowerLower (r : ℚ) (L m n : ℕ) : ℚ :=
  ratExpScaledLower (ratPiPowerLogLower r L) m n
def ratPiPowerUpper (r : ℚ) (L m n : ℕ) : ℚ :=
  ratExpScaledUpper (ratPiPowerLogUpper r L) m n

theorem ratPiPower_log_enclosure (r : ℚ) (L : ℕ) :
    (ratPiPowerLogLower r L : ℝ) ≤ (r : ℝ) * Real.log Real.pi ∧
    (r : ℝ) * Real.log Real.pi ≤ (ratPiPowerLogUpper r L : ℝ) := by
  have h := ratLog_interval_enclosure machinPiLower machinPiUpper Real.pi L
    machinPiLower_pos machinPi_enclosure.1 machinPi_enclosure.2
  change (ratGammaPiLogLower L : ℝ) ≤ Real.log Real.pi ∧
    Real.log Real.pi ≤ (ratGammaPiLogUpper L : ℝ) at h
  unfold ratPiPowerLogLower ratPiPowerLogUpper
  push_cast
  rcases le_total (0 : ℝ) (r : ℝ) with hr | hr
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_left h.1 hr),
      (mul_le_mul_of_nonneg_left h.2 hr).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left h.2 hr),
      (mul_le_mul_of_nonpos_left h.1 hr).trans (le_max_left _ _)⟩

theorem ratPiPower_enclosure (r : ℚ) (L m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hl : |ratPiPowerLogLower r L / m| ≤ 1)
    (hu : |ratPiPowerLogUpper r L / m| ≤ 1) :
    (ratPiPowerLower r L m n : ℝ) ≤ Real.pi ^ (r : ℝ) ∧
    Real.pi ^ (r : ℝ) ≤ (ratPiPowerUpper r L m n : ℝ) := by
  have h := ratPiPower_log_enclosure r L
  have hlo := ratExp_scaled_enclosure (ratPiPowerLogLower r L) m n hm hn hl
  have hup := ratExp_scaled_enclosure (ratPiPowerLogUpper r L) m n hm hn hu
  rw [Real.rpow_def_of_pos Real.pi_pos, mul_comm (Real.log Real.pi)]
  exact ⟨hlo.1.trans (Real.exp_le_exp.mpr h.1),
    (Real.exp_le_exp.mpr h.2).trans hup.2⟩

end ReciprocalXi

