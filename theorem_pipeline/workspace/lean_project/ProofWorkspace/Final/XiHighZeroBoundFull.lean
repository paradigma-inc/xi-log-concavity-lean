import ProofWorkspace.Final.XiZeroBudgetFull
import ProofWorkspace.Final.XiHeatTraceFull

set_option autoImplicit false
noncomputable section
open Set Filter Topology Complex
namespace ReciprocalXi

theorem exponential_dominates_high_zero_weight {A : ℝ} (hA : 100 ≤ A) :
    1000*(A^2+1) ≤ Real.exp (A/2) := by
  have hA0 : 0 ≤ A := by linarith
  have h4 : (100:ℝ)^4 ≤ A^4 := pow_le_pow_left₀ (by norm_num) hA 4
  have h2 : (100:ℝ)^2 ≤ A^2 := pow_le_pow_left₀ (by norm_num) hA 2
  have h6 := mul_le_mul_of_nonneg_right h4 (sq_nonneg A)
  rw [← pow_add] at h6
  norm_num at h4 h2 h6
  calc
    1000*(A^2+1) ≤ 2000*A^2 := by nlinarith
    _ ≤ A^6/46080 := by nlinarith [h6]
    _ = (A/2)^6/((6:ℕ).factorial:ℝ) := by norm_num; ring
    _ ≤ Real.exp (A/2) := Real.pow_div_factorial_le_exp (A/2) (by linarith) 6

theorem F_highZero_exp_le (z : FPositiveZeroOccurrence)
    (hz : 100 ≤ (F_pairRoot z).re) :
    Real.exp (-(F_pairRoot z).re/2) ≤ (‖F_pairRoot z‖^2)⁻¹/1000 := by
  have hi : (F_pairRoot z).im^2 ≤ 1 :=
    ((sq_lt_one_iff_abs_lt_one _).mpr (F_zero_im_bound _ (F_pairRoot_is_zero z))).le
  have hn : ‖F_pairRoot z‖^2 ≤ (F_pairRoot z).re^2+1 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith
  have he : 1000*‖F_pairRoot z‖^2 ≤ Real.exp ((F_pairRoot z).re/2) :=
    (mul_le_mul_of_nonneg_left hn (by norm_num)).trans
      (exponential_dominates_high_zero_weight hz)
  have hp : 0 < 1000*‖F_pairRoot z‖^2 := by
    positivity [norm_pos_iff.mpr (F_pairRoot_ne_zero z)]
  rw [neg_div, Real.exp_neg]
  calc
    (Real.exp ((F_pairRoot z).re/2))⁻¹ ≤ (1000*‖F_pairRoot z‖^2)⁻¹ := inv_anti₀ hp he
    _ = _ := by rw [mul_inv_rev, div_eq_mul_inv]

abbrev FHighZeroOccurrence (T : ℝ) := {z : FPositiveZeroOccurrence // T ≤ (F_pairRoot z).re}

theorem summable_F_highZero_exp {T : ℝ} (hT : 100 ≤ T) :
    Summable (fun z : FHighZeroOccurrence T ↦ Real.exp (-(F_pairRoot z.val).re/2)) := by
  exact ((summable_F_pairRoot_inv_norm_sq.subtype _).div_const 1000).of_nonneg_of_le
    (fun _ ↦ (Real.exp_pos _).le) (fun z ↦ F_highZero_exp_le z.val (hT.trans z.property))

theorem F_highZero_exp_tsum_le {T : ℝ} (hT : 100 ≤ T) :
    (∑' z : FHighZeroOccurrence T, Real.exp (-(F_pairRoot z.val).re/2)) ≤ 7/100 := by
  have hb : (∑' z : FHighZeroOccurrence T, (‖F_pairRoot z.val‖^2)⁻¹) ≤ 70 := by
    apply le_trans _ F_pairRoot_inv_norm_sq_tsum_le_seventy
    exact Summable.tsum_le_tsum_of_inj Subtype.val Subtype.val_injective
      (fun _ _ ↦ by positivity) (fun _ ↦ le_rfl)
      (summable_F_pairRoot_inv_norm_sq.subtype _) summable_F_pairRoot_inv_norm_sq
  calc
    _ ≤ ∑' z : FHighZeroOccurrence T, (‖F_pairRoot z.val‖^2)⁻¹/1000 :=
      (summable_F_highZero_exp hT).tsum_le_tsum (fun z ↦ F_highZero_exp_le z.val (hT.trans z.property))
        ((summable_F_pairRoot_inv_norm_sq.subtype _).div_const 1000)
    _ = (∑' z : FHighZeroOccurrence T, (‖F_pairRoot z.val‖^2)⁻¹)/1000 := tsum_div_const
    _ ≤ 70/1000 := div_le_div_of_nonneg_right hb (by norm_num)
    _ = 7/100 := by norm_num

end ReciprocalXi

