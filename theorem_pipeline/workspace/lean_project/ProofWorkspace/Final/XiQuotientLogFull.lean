import ProofWorkspace.Final.XiPairedQuotientFull
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
noncomputable section
open Set Metric Filter Topology
namespace ReciprocalXi

theorem entire_wedgeIntegral_hasDerivAt {f : ℂ → ℂ} (hf : Differentiable ℂ f) (w : ℂ) :
    HasDerivAt (fun z ↦ Complex.wedgeIntegral 0 z f) (f w) w := by
  have hd : DifferentiableOn ℂ f (ball 0 (‖w‖+1)) := hf.differentiableOn
  exact hd.isConservativeOn.hasDerivAt_wedgeIntegral hd.continuousOn
    (by simp [mem_ball_iff_norm])

def F_quotientLogDeriv (w : ℂ) : ℂ := deriv F_pairQuotient w/F_pairQuotient w

theorem differentiable_F_quotientLogDeriv : Differentiable ℂ F_quotientLogDeriv := by
  have hd : Differentiable ℂ (deriv F_pairQuotient) :=
    differentiableOn_univ.mp (differentiable_F_pairQuotient.differentiableOn.deriv isOpen_univ)
  exact hd.div differentiable_F_pairQuotient F_pairQuotient_ne_zero

def F_quotientLog (w : ℂ) : ℂ := Complex.wedgeIntegral 0 w F_quotientLogDeriv

theorem F_quotientLog_hasDerivAt (w : ℂ) :
    HasDerivAt F_quotientLog (F_quotientLogDeriv w) w :=
  entire_wedgeIntegral_hasDerivAt differentiable_F_quotientLogDeriv w

theorem differentiable_F_quotientLog : Differentiable ℂ F_quotientLog :=
  fun w ↦ (F_quotientLog_hasDerivAt w).differentiableAt

theorem F_quotientLog_zero : F_quotientLog 0 = 0 := by
  simp [F_quotientLog, Complex.wedgeIntegral]

theorem F_pairQuotient_eq_exp (w : ℂ) :
    F_pairQuotient w = F 0 * Complex.exp (F_quotientLog w) := by
  let h (z : ℂ) := F_pairQuotient z*Complex.exp (-F_quotientLog z)
  have hh : ∀ z, HasDerivAt h 0 z := by
    intro z
    have hd : HasDerivAt h
        (deriv F_pairQuotient z*Complex.exp (-F_quotientLog z)+
          F_pairQuotient z*(Complex.exp (-F_quotientLog z)*(-F_quotientLogDeriv z))) z :=
      (differentiable_F_pairQuotient z).hasDerivAt.mul ((F_quotientLog_hasDerivAt z).neg.cexp)
    convert hd using 1
    unfold F_quotientLogDeriv
    field_simp [F_pairQuotient_ne_zero z]
    ring
  have he := is_const_of_deriv_eq_zero (fun z ↦ (hh z).differentiableAt)
    (fun z ↦ (hh z).deriv) w 0
  simp only [h, F_quotientLog_zero, neg_zero, Complex.exp_zero, mul_one, F_pairQuotient_zero] at he
  have hm := congrArg (fun z ↦ z*Complex.exp (F_quotientLog w)) he
  simpa only [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one] using hm

theorem F_pairedProduct_exp_factor (w : ℂ) :
    F w = F 0 * Complex.exp (F_quotientLog w) * F_pairedProduct w := by
  rw [← F_pairQuotient_eq_exp, F_pairQuotient_mul_product]

theorem F_pairQuotient_deriv_zero : deriv F_pairQuotient 0 = 0 := by
  have hd : HasDerivAt (fun z : ℂ ↦ F_pairQuotient (-z)) (-deriv F_pairQuotient 0) 0 := by
    convert (differentiable_F_pairQuotient (-(0:ℂ))).hasDerivAt.comp 0
      ((hasDerivAt_id (0:ℂ)).neg) using 1 <;> simp
  have he : (fun z : ℂ ↦ F_pairQuotient (-z)) = F_pairQuotient := funext F_pairQuotient_even
  rw [he] at hd
  have hh := hd.unique (differentiable_F_pairQuotient (0:ℂ)).hasDerivAt
  linear_combination -1/2*hh

theorem F_quotientLog_deriv_zero : deriv F_quotientLog 0 = 0 := by
  rw [(F_quotientLog_hasDerivAt 0).deriv, F_quotientLogDeriv, F_pairQuotient_deriv_zero, zero_div]

end ReciprocalXi

