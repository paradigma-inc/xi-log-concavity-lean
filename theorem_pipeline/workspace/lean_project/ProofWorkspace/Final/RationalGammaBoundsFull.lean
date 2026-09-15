import ProofWorkspace.Final.GammaLogSeriesFull
import ProofWorkspace.Final.RationalZetaBoundsFull
import ProofWorkspace.Final.RationalLogBoundsFull
import ProofWorkspace.Final.PiBoundsFull
import ProofWorkspace.Final.RationalExpBoundsFull

noncomputable section
open scoped BigOperators
namespace ReciprocalXi

def ratGammaLogCoefficient (z : ℚ) (k : ℕ) : ℚ :=
  (-1 : ℚ) ^ k * (z ^ (k + 2) - 2 * z * (1 / 2 : ℚ) ^ (k + 2)) / (k + 2)

def ratGammaLogSeries (z : ℚ) (N M : ℕ) : ℚ :=
  ∑ k ∈ Finset.range N, ratGammaLogCoefficient z k * ratZetaNatLower M (k + 2)

def ratGammaLogSeriesError (z : ℚ) (N M : ℕ) : ℚ :=
  (2 / (2 : ℚ) ^ M) * ∑ k ∈ Finset.range N, |ratGammaLogCoefficient z k|

theorem ratGammaLogCoefficient_cast (z : ℚ) (k : ℕ) :
    (ratGammaLogCoefficient z k : ℝ) = gammaLogTaylorCoefficient (z : ℝ) k := by
  unfold ratGammaLogCoefficient gammaLogTaylorCoefficient
  push_cast
  rfl

theorem ratGammaLogSeries_error (z : ℚ) (N M : ℕ) :
    |gammaLogSeriesApprox (z : ℝ) N - (ratGammaLogSeries z N M : ℝ)| ≤
      (ratGammaLogSeriesError z N M : ℝ) := by
  have hz (k : ℕ) : |(riemannZeta ((k : ℂ) + 2)).re -
      (ratZetaNatLower M (k + 2) : ℝ)| ≤ (2 : ℝ) / 2 ^ M := by
    have h := ratZetaNat_enclosure M (k + 2) (by omega)
    unfold ratZetaNatUpper at h
    push_cast at h
    rw [abs_of_nonneg (sub_nonneg.mpr h.1)]
    linarith
  unfold gammaLogSeriesApprox ratGammaLogSeries ratGammaLogSeriesError
  push_cast
  simp_rw [ratGammaLogCoefficient_cast]
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro k hk
  rw [← mul_sub, abs_mul]
  exact (mul_le_mul_of_nonneg_left (hz k) (abs_nonneg _)).trans_eq (mul_comm _ _)

def ratGammaPiLogLower (L : ℕ) : ℚ :=
  ratLogTaylor machinPiLower L - ratLogError machinPiLower L
def ratGammaPiLogUpper (L : ℕ) : ℚ :=
  ratLogTaylor machinPiUpper L + ratLogError machinPiUpper L
def ratGammaPiLogCenter (L : ℕ) : ℚ := (ratGammaPiLogLower L + ratGammaPiLogUpper L) / 2
def ratGammaPiLogRadius (L : ℕ) : ℚ := (ratGammaPiLogUpper L - ratGammaPiLogLower L) / 2

theorem ratGammaPiLog_error (L : ℕ) :
    |Real.log Real.pi - (ratGammaPiLogCenter L : ℝ)| ≤ (ratGammaPiLogRadius L : ℝ) := by
  have h := ratLog_interval_enclosure machinPiLower machinPiUpper Real.pi L
    machinPiLower_pos machinPi_enclosure.1 machinPi_enclosure.2
  change (ratGammaPiLogLower L : ℝ) ≤ Real.log Real.pi ∧
    Real.log Real.pi ≤ (ratGammaPiLogUpper L : ℝ) at h
  unfold ratGammaPiLogCenter ratGammaPiLogRadius
  push_cast
  rw [abs_le]
  constructor <;> linarith

def ratLogGammaCenter (z : ℚ) (N M L : ℕ) : ℚ :=
  z * ratGammaPiLogCenter L - 2 * z * ratLogTaylor 2 L + ratGammaLogSeries z N M

def ratLogGammaRadius (z : ℚ) (N M L : ℕ) : ℚ :=
  8 * (1 / 2 : ℚ) ^ (N + 2) + |z| * ratGammaPiLogRadius L +
    2 * |z| * ratLogError 2 L + ratGammaLogSeriesError z N M

theorem ratLogGamma_error (z : ℚ) (N M L : ℕ) (hz : |z| ≤ 1 / 2) :
    |Real.log (Real.Gamma (1 + (z : ℝ))) - (ratLogGammaCenter z N M L : ℝ)| ≤
      (ratLogGammaRadius z N M L : ℝ) := by
  have hzR : |(z : ℝ)| ≤ 1 / 2 := by
    rw [← Rat.cast_abs]
    have hc : ((|z| : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := Rat.cast_le.mpr hz
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hc
    exact hc
  have hG := logGamma_approx_error_bound (z : ℝ) N hzR
  have hpi := ratGammaPiLog_error L
  have htwo := ratLogTaylor_error 2 L (by norm_num)
  have hzeta := ratGammaLogSeries_error z N M
  have hpi' := mul_le_mul_of_nonneg_left hpi (abs_nonneg (z : ℝ))
  have htwo' := mul_le_mul_of_nonneg_left htwo (by positivity : 0 ≤ 2 * |(z : ℝ)|)
  have hdiff : logGammaApprox (z : ℝ) N - (ratLogGammaCenter z N M L : ℝ) =
      (z : ℝ) * (Real.log Real.pi - (ratGammaPiLogCenter L : ℝ)) -
      2 * (z : ℝ) * (Real.log 2 - (ratLogTaylor 2 L : ℝ)) +
      (gammaLogSeriesApprox (z : ℝ) N - (ratGammaLogSeries z N M : ℝ)) := by
    unfold logGammaApprox ratLogGammaCenter
    push_cast
    ring
  have hmid : |logGammaApprox (z : ℝ) N - (ratLogGammaCenter z N M L : ℝ)| ≤
      |(z : ℝ)| * (ratGammaPiLogRadius L : ℝ) +
      2 * |(z : ℝ)| * (ratLogError 2 L : ℝ) + (ratGammaLogSeriesError z N M : ℝ) := by
    rw [hdiff]
    apply (abs_add_le _ _).trans
    apply add_le_add _ hzeta
    rw [sub_eq_add_neg]
    apply (abs_add_le _ _).trans
    rw [abs_neg, abs_mul, abs_mul, abs_mul]
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    convert add_le_add hpi' htwo' using 1
  have htriangle := norm_sub_le_norm_sub_add_norm_sub
    (Real.log (Real.Gamma (1 + (z : ℝ)))) (logGammaApprox (z : ℝ) N)
    (ratLogGammaCenter z N M L : ℝ)
  simp only [Real.norm_eq_abs] at htriangle
  apply htriangle.trans
  apply (add_le_add hG hmid).trans_eq
  unfold ratLogGammaRadius
  push_cast
  ring

def ratLogGammaLower (z : ℚ) (N M L : ℕ) : ℚ :=
  ratLogGammaCenter z N M L - ratLogGammaRadius z N M L
def ratLogGammaUpper (z : ℚ) (N M L : ℕ) : ℚ :=
  ratLogGammaCenter z N M L + ratLogGammaRadius z N M L

theorem ratLogGamma_enclosure (z : ℚ) (N M L : ℕ) (hz : |z| ≤ 1 / 2) :
    (ratLogGammaLower z N M L : ℝ) ≤ Real.log (Real.Gamma (1 + (z : ℝ))) ∧
    Real.log (Real.Gamma (1 + (z : ℝ))) ≤ (ratLogGammaUpper z N M L : ℝ) := by
  have h := abs_le.mp (ratLogGamma_error z N M L hz)
  unfold ratLogGammaLower ratLogGammaUpper
  push_cast
  constructor <;> linarith

def ratGammaLower (z : ℚ) (N M L m n : ℕ) : ℚ :=
  ratExpScaledLower (ratLogGammaLower z N M L) m n
def ratGammaUpper (z : ℚ) (N M L m n : ℕ) : ℚ :=
  ratExpScaledUpper (ratLogGammaUpper z N M L) m n

/-- An all-rational enclosure of the actual Gamma function on [1/2,3/2]. -/
theorem ratGamma_enclosure (z : ℚ) (N M L m n : ℕ) (hz : |z| ≤ 1 / 2)
    (hm : 0 < m) (hn : 0 < n)
    (hl : |ratLogGammaLower z N M L / m| ≤ 1)
    (hu : |ratLogGammaUpper z N M L / m| ≤ 1) :
    (ratGammaLower z N M L m n : ℝ) ≤ Real.Gamma (1 + (z : ℝ)) ∧
    Real.Gamma (1 + (z : ℝ)) ≤ (ratGammaUpper z N M L m n : ℝ) := by
  have h := ratLogGamma_enclosure z N M L hz
  have hlo := ratExp_scaled_enclosure (ratLogGammaLower z N M L) m n hm hn hl
  have hup := ratExp_scaled_enclosure (ratLogGammaUpper z N M L) m n hm hn hu
  have hzR : |(z : ℝ)| ≤ 1 / 2 := by
    have hc : ((|z| : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := Rat.cast_le.mpr hz
    simpa only [Rat.cast_abs, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hc
  have hg : 0 < Real.Gamma (1 + (z : ℝ)) :=
    Real.Gamma_pos_of_pos (by linarith [(abs_le.mp hzR).1])
  have he := Real.exp_log hg
  constructor
  · exact hlo.1.trans ((Real.exp_le_exp.mpr h.1).trans_eq he)
  · exact (he.symm.trans_le (Real.exp_le_exp.mpr h.2)).trans hup.2

end ReciprocalXi

