import ProofWorkspace.Final.XiMomentGeometryFull
import ProofWorkspace.Final.XiMomentExpansionFull
import ProofWorkspace.Final.XiMomentSamplesFull

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 6000000
noncomputable section
namespace ReciprocalXi

theorem F_pairRoot_re_gt_seven (z : FPositiveZeroOccurrence) :
    7<(F_pairRoot z).re := by
  have hp : 0<(F_pairRoot z).re := z.property
  simpa only [abs_of_pos hp] using
    F_zero_abs_re_gt_seven (F_pairRoot z) (F_pairRoot_is_zero z)

theorem F_pairMoment_one_bound : F_pairMoment 1<(1:ℝ)/160 := by
  have he := F_momentTaylor_error_of_mass_bound 1 (1/40) 7 70 (by norm_num)
    (fun z ↦ (F_pairRoot_re_gt_seven z).le) (by norm_num)
    F_pairRoot_inv_norm_sq_tsum_le_seventy
  have he' : |F_momentLog (1/40)-F_pairMoment 1/1600|≤
      ((70*(1/1600)^2/(2*49*(1-(1/1600)/49)):ℚ):ℝ) := by
    convert he using 1 <;> norm_num [F_momentTaylor,Finset.sum_range_succ] <;> ring
  have hg : |F_momentLog (1/40)-(momentLogSample 1:ℝ)|≤1/(10:ℝ)^118 := by
    simpa [F_momentLog] using momentLogSample_actual 1
  have hbound : F_pairMoment 1≤(momentOneUpper:ℝ) := by
    unfold momentOneUpper
    push_cast
    have ht := (abs_le.mp he').1
    have hl := (abs_le.mp hg).2
    norm_num at ht ⊢
    linarith
  have hrat : (momentOneUpper:ℝ)<1/160 := by
    have h := (Rat.cast_lt (K:=ℝ)).mpr momentOneUpper_bound
    norm_num only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at h
    exact h
  exact hbound.trans_lt hrat

theorem F_pairMoment_one_mass_lower :
    (47/49:ℝ)*(∑' z : FPositiveZeroOccurrence, (‖F_pairRoot z‖^2)⁻¹)≤F_pairMoment 1 := by
  have hp (z : FPositiveZeroOccurrence) :
      (47/49:ℝ)*(‖F_pairRoot z‖^2)⁻¹≤(((F_pairRoot z)⁻¹)^2).re := by
    have ha := F_pairRoot_re_gt_seven z
    have hb := complex_inverse_power_re_lower (F_pairRoot z) z.property
      (F_zero_im_bound _ (F_pairRoot_is_zero z)).le 2
    have hsq : (49:ℝ)≤(F_pairRoot z).re^2 := by nlinarith
    have hfac : (47/49:ℝ)≤1-(2:ℝ)^2/(2*(F_pairRoot z).re^2) := by
      have hh : (2:ℝ)^2/(2*(F_pairRoot z).re^2)≤2/49 := by
        calc
          _≤(2:ℝ)^2/(2*49) := by gcongr
          _=_ := by norm_num
      linarith
    apply le_trans _ hb
    rw [←div_eq_mul_inv]
    exact div_le_div_of_nonneg_right hfac (sq_nonneg _)
  have hh := Summable.tsum_le_tsum hp
    (summable_F_pairRoot_inv_norm_sq.mul_left (47/49))
    (summable_F_pairMoment_terms 1 (by norm_num))
  simpa only [tsum_mul_left,F_pairMoment,Nat.mul_one] using hh

theorem F_pairRoot_inv_norm_sq_tsum_lt_one_fifty :
    (∑' z : FPositiveZeroOccurrence, (‖F_pairRoot z‖^2)⁻¹)<(1:ℝ)/150 := by
  have h1 := F_pairMoment_one_bound
  have h2 := F_pairMoment_one_mass_lower
  linarith

theorem F_pairMoment_two_bound : F_pairMoment 2<(1:ℝ)/400000 := by
  have he1 := F_momentTaylor_error_of_mass_bound 2 (1/40) 7 (1/150) (by norm_num)
    (fun z ↦ (F_pairRoot_re_gt_seven z).le) (by norm_num)
    F_pairRoot_inv_norm_sq_tsum_lt_one_fifty.le
  have he2 := F_momentTaylor_error_of_mass_bound 2 (1/20) 7 (1/150) (by norm_num)
    (fun z ↦ (F_pairRoot_re_gt_seven z).le) (by norm_num)
    F_pairRoot_inv_norm_sq_tsum_lt_one_fifty.le
  have hg1 : |F_momentLog (1/40)-(momentLogSample 1:ℝ)|≤1/(10:ℝ)^118 := by
    simpa [F_momentLog] using momentLogSample_actual 1
  have hg2 : |F_momentLog (1/20)-(momentLogSample 2:ℝ)|≤1/(10:ℝ)^118 := by
    convert momentLogSample_actual 2 using 1 <;> norm_num [F_momentLog]
  norm_num [F_momentTaylor,Finset.sum_range_succ] at he1 he2
  have hbound : F_pairMoment 2≤(momentTwoUpper:ℝ) := by
    unfold momentTwoUpper
    push_cast
    norm_num
    have a := (abs_le.mp he1).1
    have b := (abs_le.mp he2).2
    have c := (abs_le.mp hg1).2
    have d := (abs_le.mp hg2).1
    linarith
  have hrat : (momentTwoUpper:ℝ)<1/400000 := by
    have h := (Rat.cast_lt (K:=ℝ)).mpr momentTwoUpper_bound
    norm_num only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at h
    exact h
  exact hbound.trans_lt hrat

theorem F_pairMoment_two_terms_nonneg (z : FPositiveZeroOccurrence) :
    0≤(((F_pairRoot z)⁻¹)^4).re := by
  have ha := F_pairRoot_re_gt_seven z
  have hsq : (49:ℝ)≤(F_pairRoot z).re^2 := by nlinarith
  have hfac : 0≤1-(4:ℝ)^2/(2*(F_pairRoot z).re^2) := by
    have hp : (0:ℝ)<2*(F_pairRoot z).re^2 := by positivity
    have hh : (4:ℝ)^2/(2*(F_pairRoot z).re^2)≤1 :=
      (div_le_one hp).mpr (by nlinarith)
    linarith
  exact (div_nonneg hfac (pow_nonneg (norm_nonneg _) 4)).trans
    (complex_inverse_power_re_lower (F_pairRoot z) z.property
      (F_zero_im_bound _ (F_pairRoot_is_zero z)).le 4)

theorem F_pairRoot_re_gt_twentyFour (z : FPositiveZeroOccurrence) :
    24<(F_pairRoot z).re := by
  by_contra hn
  have ha := F_pairRoot_re_gt_seven z
  have hb : (F_pairRoot z).re≤24 := le_of_not_gt hn
  have hi := (F_zero_im_bound _ (F_pairRoot_is_zero z)).le
  have hsq : (49:ℝ)≤(F_pairRoot z).re^2 := by nlinarith
  have him : (F_pairRoot z).im^2≤1 := (sq_le_one_iff_abs_le_one _).mpr hi
  have hr : ‖F_pairRoot z‖^2≤577 := by
    rw [Complex.sq_norm,Complex.normSq_apply]
    nlinarith
  have hr4 : ‖F_pairRoot z‖^4≤577^2 := by
    have hh := pow_le_pow_left₀ (sq_nonneg ‖F_pairRoot z‖) hr 2
    simpa only [←pow_mul] using hh
  have hfac : (41/49:ℝ)≤1-(4:ℝ)^2/(2*(F_pairRoot z).re^2) := by
    have hh : (4:ℝ)^2/(2*(F_pairRoot z).re^2)≤8/49 := by
      calc
        _≤(4:ℝ)^2/(2*49) := by gcongr
        _=_ := by norm_num
    linarith
  have hterm : (41/49:ℝ)/577^2≤(((F_pairRoot z)⁻¹)^4).re := by
    apply le_trans _ (complex_inverse_power_re_lower (F_pairRoot z) z.property hi 4)
    apply le_trans _ (div_le_div_of_nonneg_right hfac (pow_nonneg (norm_nonneg _) 4))
    exact div_le_div_of_nonneg_left (by norm_num)
      (pow_pos (lt_trans zero_lt_one (F_zero_norm_gt_one _ (F_pairRoot_is_zero z))) 4) hr4
  have ht : (((F_pairRoot z)⁻¹)^4).re≤F_pairMoment 2 := by
    apply (summable_F_pairMoment_terms 2 (by norm_num)).le_tsum z
    intro w hw
    exact F_pairMoment_two_terms_nonneg w
  have hm := F_pairMoment_two_bound
  have hconst : (1:ℝ)/400000<(41/49:ℝ)/577^2 := by norm_num
  exact (hconst.trans_le (hterm.trans ht)).not_ge hm.le

end ReciprocalXi
