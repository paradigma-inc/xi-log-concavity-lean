import ProofWorkspace.Final.EtaEulerFull
import ProofWorkspace.Final.EtaIntegralFull
import ProofWorkspace.Final.EtaContinuationFull

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace ReciprocalXi

def etaEulerApprox (N : ℕ) (s : ℝ) : ℝ :=
  ∑ j ∈ Finset.range N, (-1 : ℝ) ^ j * etaEulerWeight N j / ((j : ℝ) + 1) ^ s

theorem integral_etaEulerIntegrand (N : ℕ) (s : ℝ) (hs : 0 < s) :
    (∫ t : ℝ in Ioi 0, etaEulerIntegrand N s t) / Real.Gamma s = etaEulerApprox N s := by
  have he (t : ℝ) : etaEulerIntegrand N s t =
      ∑ j ∈ Finset.range N, ((-1 : ℝ) ^ j * etaEulerWeight N j) *
        (t ^ (s - 1) * Real.exp (-(((j : ℝ) + 1) * t))) := by
    unfold etaEulerIntegrand etaEulerPolynomial
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← Real.exp_nat_mul]
    push_cast
    have hx : ((j : ℝ) + 1) * -t = -(((j : ℝ) + 1) * t) := by ring
    rw [hx]
    ring
  simp_rw [he]
  rw [integral_finset_sum _ (by
    intro j hj
    exact (integrableOn_etaLaplace s ((j : ℝ) + 1) hs (by positivity)).const_mul _)]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_const_mul, div_eq_mul_inv, mul_assoc, ← div_eq_mul_inv,
    etaLaplaceIntegral_nat s hs j]
  ring

theorem etaIntegral_euler_error_bounds (N : ℕ) (s : ℝ) (hs : 0 < s) :
    0 ≤ etaIntegral s - etaEulerApprox N s ∧
    etaIntegral s - etaEulerApprox N s ≤ 1 / 2 ^ N := by
  have he := integrableOn_etaIntegrand s hs
  have hp := integrableOn_etaEulerIntegrand N s hs
  have hg := Real.GammaIntegral_convergent hs
  have hG : 0 < Real.Gamma s := Real.Gamma_pos_of_pos hs
  have hd : etaIntegral s - etaEulerApprox N s =
      (∫ t : ℝ in Ioi 0, etaIntegrand s t - etaEulerIntegrand N s t) / Real.Gamma s := by
    rw [integral_sub he hp, ← div_sub_div_same]
    unfold etaIntegral
    rw [integral_etaEulerIntegrand N s hs]
  rw [hd]
  constructor
  · apply div_nonneg _ hG.le
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (etaEulerIntegrand_remainder_bounds N s t ht).1
  · have hi : (∫ t : ℝ in Ioi 0, etaIntegrand s t - etaEulerIntegrand N s t) ≤
        Real.Gamma s / 2 ^ N := by
      rw [Real.Gamma_eq_integral hs, ← integral_div]
      apply integral_mono_ae (he.sub hp) (hg.div_const _)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact (etaEulerIntegrand_remainder_bounds N s t ht).2
    exact (div_le_div_of_nonneg_right hi hG.le).trans_eq (by field_simp)

theorem etaIntegral_euler_400_error (s : ℝ) (hs : 0 < s) :
    0 ≤ etaIntegral s - etaEulerApprox 400 s ∧
    etaIntegral s - etaEulerApprox 400 s < 1 / 10 ^ 120 :=
  ⟨(etaIntegral_euler_error_bounds 400 s hs).1,
    (etaIntegral_euler_error_bounds 400 s hs).2.trans_lt eta_euler_400_error_lt⟩

theorem etaIntegral_euler_400_enclosure (s : ℝ) (hs : 0 < s) :
    etaEulerApprox 400 s ≤ etaIntegral s ∧
    etaIntegral s < etaEulerApprox 400 s + 1 / 10 ^ 120 := by
  have h := etaIntegral_euler_400_error s hs
  constructor <;> linarith

theorem riemannZeta_euler_error_bounds (N : ℕ) (s : ℝ) (hs : 1 < s) :
    0 ≤ (1 - (2 : ℝ) ^ (1 - s)) * (riemannZeta (s : ℂ)).re - etaEulerApprox N s ∧
    (1 - (2 : ℝ) ^ (1 - s)) * (riemannZeta (s : ℂ)).re - etaEulerApprox N s ≤
      1 / 2 ^ N := by
  rw [← etaIntegral_eq_riemannZeta s hs]
  exact etaIntegral_euler_error_bounds N s (by linarith)

theorem riemannZeta_euler_error_bounds_of_pos (N : ℕ) (s : ℝ) (hs : 0 < s) (hs1 : s ≠ 1) :
    0 ≤ (1 - (2 : ℝ) ^ (1 - s)) * (riemannZeta (s : ℂ)).re - etaEulerApprox N s ∧
    (1 - (2 : ℝ) ^ (1 - s)) * (riemannZeta (s : ℂ)).re - etaEulerApprox N s ≤
      1 / 2 ^ N := by
  rw [← etaIntegral_eq_riemannZeta_of_pos s hs hs1]
  exact etaIntegral_euler_error_bounds N s hs

end ReciprocalXi
