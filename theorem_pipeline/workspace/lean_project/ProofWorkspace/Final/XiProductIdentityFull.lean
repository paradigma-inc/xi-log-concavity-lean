import ProofWorkspace.Final.XiQuotientGrowthFull
import ProofWorkspace.Final.EntireRealAverageFull

set_option autoImplicit false
noncomputable section
namespace ReciprocalXi

theorem F_quotientLog_eq_zero (w : ℂ) : F_quotientLog w=0 :=
  entire_eq_zero_of_subquadratic_positive_average differentiable_F_quotientLog
    F_quotientLog_zero F_quotientLog_deriv_zero F_quotientLogPositiveAverage_div_sq_tendsto w

theorem F_pairQuotient_eq_const (w : ℂ) : F_pairQuotient w=F 0 := by
  rw [F_pairQuotient_eq_exp, F_quotientLog_eq_zero, Complex.exp_zero, mul_one]

/-- Actual Xi equals the canonical product over its actual positive-half-plane zero
occurrences. No zero-list, RH, product identity or growth hypothesis is assumed. -/
theorem F_eq_pairedProduct (w : ℂ) : F w=F 0*F_pairedProduct w := by
  rw [F_pairedProduct_exp_factor, F_quotientLog_eq_zero, Complex.exp_zero, mul_one]

theorem F_div_zero_eq_pairedProduct (w : ℂ) : F w/F 0=F_pairedProduct w := by
  rw [F_eq_pairedProduct]
  exact mul_div_cancel_left₀ _ F_zero_ne_zero

end ReciprocalXi
