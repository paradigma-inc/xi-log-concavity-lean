import ProofWorkspace.Final.XiProductIdentityFull
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn

set_option autoImplicit false
noncomputable section
open Set Metric Filter Topology Complex
namespace ReciprocalXi

theorem F_pairFactor_ne_zero (z : FPositiveZeroOccurrence) (w : ℂ) (hw : F w ≠ 0) :
    1+F_pairTerm z w ≠ 0 := by
  intro h
  rcases (F_pairFactor_zero_iff z w).mp h with h | h
  · exact hw (h ▸ F_pairRoot_is_zero z)
  · rw [h, F_even] at hw
    exact hw (F_pairRoot_is_zero z)

theorem F_pairFactor_hasDerivAt (z : FPositiveZeroOccurrence) (w : ℂ) :
    HasDerivAt (fun w ↦ 1+F_pairTerm z w) (-2*w/(F_pairRoot z)^2) w := by
  have h := (((hasDerivAt_id w).div_const (F_pairRoot z)).pow 2).neg.const_add 1
  convert h using 1 <;> simp only [F_pairTerm, id_eq, Nat.cast_ofNat, pow_one]
  field_simp
  <;> ring

theorem F_pairFactor_logDeriv (z : FPositiveZeroOccurrence) (w : ℂ) :
    logDeriv (fun w ↦ 1+F_pairTerm z w) w = 2*w/(w^2-(F_pairRoot z)^2) := by
  rw [logDeriv_apply, (F_pairFactor_hasDerivAt z w).deriv, F_pairTerm]
  field_simp [F_pairRoot_ne_zero z]
  ring_nf
  rw [show -w^2+(F_pairRoot z)^2 = -(w^2-(F_pairRoot z)^2) by ring, inv_neg]
  ring

theorem summable_norm_F_pairFactor_logDeriv (w : ℂ) :
    Summable (fun z : FPositiveZeroOccurrence ↦
      ‖logDeriv (fun w ↦ 1+F_pairTerm z w) w‖) := by
  apply (summable_F_pairRoot_inv_norm_sq.mul_left (4*‖w‖)).of_norm_bounded_eventually
  filter_upwards [(summable_norm_F_pairTerm w).tendsto_cofinite_zero.eventually_le_const
    (show (0:ℝ)<1/2 by norm_num)] with z hz
  have hden : 1/2 ≤ ‖1+F_pairTerm z w‖ := by
    have h := norm_sub_norm_le (1:ℂ) (-F_pairTerm z w)
    simp only [norm_one, norm_neg, sub_neg_eq_add] at h
    linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), logDeriv_apply,
    (F_pairFactor_hasDerivAt z w).deriv, norm_div, norm_div, norm_mul, norm_pow]
  norm_num only [norm_neg, Complex.norm_ofNat]
  calc
    (2*‖w‖/‖F_pairRoot z‖^2)/‖1+F_pairTerm z w‖ ≤
        (2*‖w‖/‖F_pairRoot z‖^2)/(1/2) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hden
    _ = 4*‖w‖*(‖F_pairRoot z‖^2)⁻¹ := by ring

theorem summable_F_pairFactor_logDeriv (w : ℂ) :
    Summable (fun z : FPositiveZeroOccurrence ↦
      logDeriv (fun w ↦ 1+F_pairTerm z w) w) :=
  (summable_norm_F_pairFactor_logDeriv w).of_norm

theorem F_logDeriv_eq_paired_sum (w : ℂ) (hw : F w ≠ 0) :
    logDeriv F w = ∑' z : FPositiveZeroOccurrence, 2*w/(w^2-(F_pairRoot z)^2) := by
  have hf : F = fun w ↦ F 0*F_pairedProduct w := funext F_eq_pairedProduct
  calc
    logDeriv F w = logDeriv F_pairedProduct w := by
      conv_lhs => rw [hf]
      exact logDeriv_const_mul w (F 0) F_zero_ne_zero
    _ = ∑' z : FPositiveZeroOccurrence, logDeriv (fun w ↦ 1+F_pairTerm z w) w := by
      apply logDeriv_tprod_eq_tsum isOpen_univ (mem_univ w)
      · exact fun z ↦ F_pairFactor_ne_zero z w hw
      · intro z
        exact Differentiable.differentiableOn (fun w ↦
          (F_pairFactor_hasDerivAt z w).differentiableAt)
      · exact summable_F_pairFactor_logDeriv w
      · exact ⟨_, F_pairedProduct_hasProdLocallyUniformlyOn⟩
      · exact F_pairedProduct_ne_zero_of_F_ne_zero w hw
    _ = _ := tsum_congr (fun z ↦ F_pairFactor_logDeriv z w)

end ReciprocalXi

