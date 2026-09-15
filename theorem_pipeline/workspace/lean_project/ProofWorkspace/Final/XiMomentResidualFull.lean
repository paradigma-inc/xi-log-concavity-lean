import ProofWorkspace.Final.XiMomentExtractionFull
import ProofWorkspace.Final.XiPairedProductOrderFull

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 6000000
noncomputable section
namespace ReciprocalXi

theorem F_pairMoment_sixteen_term_large_below_sixty
    (z : FPositiveZeroOccurrence) (hz : (F_pairRoot z).re≤60) :
    (7/10:ℝ)<60^32*(((F_pairRoot z)⁻¹)^32).re := by
  have ha := F_pairRoot_re_gt_twentyFour z
  have hi := (F_zero_im_bound _ (F_pairRoot_is_zero z)).le
  have him : (F_pairRoot z).im^2≤1 := (sq_le_one_iff_abs_le_one _).mpr hi
  have hnorm : 0<‖F_pairRoot z‖ := norm_pos_iff.mpr (F_pairRoot_ne_zero z)
  have hang := complex_inverse_power_re_lower (F_pairRoot z) z.property hi 32
  by_cases hlow : (F_pairRoot z).re≤55
  · have hs : (576:ℝ)≤(F_pairRoot z).re^2 := by nlinarith
    have hn : ‖F_pairRoot z‖^2≤3026 := by
      rw [Complex.sq_norm,Complex.normSq_apply]
      nlinarith
    have hp : ‖F_pairRoot z‖^32≤3026^16 := by
      have h := pow_le_pow_left₀ (sq_nonneg ‖F_pairRoot z‖) hn 16
      simpa only [←pow_mul] using h
    have hf : (1/9:ℝ)≤1-(32:ℝ)^2/(2*(F_pairRoot z).re^2) := by
      have hq : (32:ℝ)^2/(2*(F_pairRoot z).re^2)≤8/9 := by
        calc
          _≤(32:ℝ)^2/(2*576) := by gcongr
          _=_ := by norm_num
      linarith
    have ht : (1/9:ℝ)/3026^16≤(((F_pairRoot z)⁻¹)^32).re := by
      apply le_trans _ hang
      apply le_trans _ (div_le_div_of_nonneg_right hf (pow_nonneg hnorm.le 32))
      exact div_le_div_of_nonneg_left (by norm_num) (pow_pos hnorm 32) hp
    have hc : (7/10:ℝ)<60^32*((1/9:ℝ)/3026^16) := by norm_num
    exact hc.trans_le (mul_le_mul_of_nonneg_left ht (by norm_num))
  · have hs : (3025:ℝ)≤(F_pairRoot z).re^2 := by
      have := lt_of_not_ge hlow
      nlinarith
    have hn : ‖F_pairRoot z‖^2≤3601 := by
      rw [Complex.sq_norm,Complex.normSq_apply]
      nlinarith
    have hp : ‖F_pairRoot z‖^32≤3601^16 := by
      have h := pow_le_pow_left₀ (sq_nonneg ‖F_pairRoot z‖) hn 16
      simpa only [←pow_mul] using h
    have hf : (1-512/3025:ℝ)≤1-(32:ℝ)^2/(2*(F_pairRoot z).re^2) := by
      have hq : (32:ℝ)^2/(2*(F_pairRoot z).re^2)≤512/3025 := by
        calc
          _≤(32:ℝ)^2/(2*3025) := by gcongr
          _=_ := by norm_num
      linarith
    have ht : (1-512/3025:ℝ)/3601^16≤(((F_pairRoot z)⁻¹)^32).re := by
      apply le_trans _ hang
      apply le_trans _ (div_le_div_of_nonneg_right hf (pow_nonneg hnorm.le 32))
      exact div_le_div_of_nonneg_left (by norm_num) (pow_pos hnorm 32) hp
    have hc : (7/10:ℝ)<60^32*((1-512/3025:ℝ)/3601^16) := by norm_num
    exact hc.trans_le (mul_le_mul_of_nonneg_left ht (by norm_num))

theorem F_pairMoment_sixteen_real_root_lower
    (z : FPositiveZeroOccurrence) (x U : ℝ)
    (he : F_pairRoot z=(x:ℂ)) (hx : 0<x) (hU : x≤U) :
    1/U^32≤(((F_pairRoot z)⁻¹)^32).re := by
  rw [he,←Complex.ofReal_inv,←Complex.ofReal_pow,Complex.ofReal_re]
  rw [inv_pow,←one_div]
  exact one_div_le_one_div_of_le (pow_pos hx 32) (pow_le_pow_left₀ hx.le hU 32)

theorem F_pairMoment_sixteen_sum_four_le
    (a b c z : FPositiveZeroOccurrence)
    (hab : a≠b) (hac : a≠c) (hbc : b≠c)
    (hza : z≠a) (hzb : z≠b) (hzc : z≠c) :
    (((F_pairRoot a)⁻¹)^32).re+(((F_pairRoot b)⁻¹)^32).re+
      (((F_pairRoot c)⁻¹)^32).re+(((F_pairRoot z)⁻¹)^32).re≤F_pairMoment 16 := by
  classical
  have hh := (summable_F_pairMoment_terms 16 (by norm_num)).sum_le_tsum
    ({a,b,c,z}:Finset FPositiveZeroOccurrence)
    (fun w _ ↦ F_pairMoment_sixteen_terms_nonneg w)
  simpa [F_pairMoment,Finset.sum_insert,hab,hac,hbc,hza.symm,hzb.symm,hzc.symm,
    add_assoc] using hh

theorem F_three_real_occurrences_exhaust_below_sixty
    (a b c : FPositiveZeroOccurrence) (x y w : ℝ)
    (ha : F_pairRoot a=(x:ℂ)) (hb : F_pairRoot b=(y:ℂ)) (hc : F_pairRoot c=(w:ℂ))
    (hx : 0<x) (hy : 0<y) (hw : 0<w)
    (hxu : x≤(momentRootUpperEndpoints.getD 0 0:ℝ))
    (hyu : y≤(momentRootUpperEndpoints.getD 1 0:ℝ))
    (hwu : w≤(momentRootUpperEndpoints.getD 2 0:ℝ))
    (hab : a≠b) (hac : a≠c) (hbc : b≠c)
    (z : FPositiveZeroOccurrence) (hza : z≠a) (hzb : z≠b) (hzc : z≠c) :
    60<(F_pairRoot z).re := by
  by_contra hn
  have hz := F_pairMoment_sixteen_term_large_below_sixty z (le_of_not_gt hn)
  have hsum := F_pairMoment_sixteen_sum_four_le a b c z hab hac hbc hza hzb hzc
  have h1 := F_pairMoment_sixteen_real_root_lower a x _ ha hx hxu
  have h2 := F_pairMoment_sixteen_real_root_lower b y _ hb hy hyu
  have h3 := F_pairMoment_sixteen_real_root_lower c w _ hc hw hwu
  have hm := F_pairMoment_sixteen_bound
  have hrat : (momentScaledResidualUpper:ℝ)<7/10 := by
    have h := (Rat.cast_lt (K:=ℝ)).mpr momentScaledResidualUpper_bound
    norm_num only [Rat.cast_div,Rat.cast_ofNat] at h
    exact h
  unfold momentScaledResidualUpper at hrat
  push_cast at hrat
  rw [Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_succ] at hrat
  norm_num only [Fin.val_zero,Fin.val_succ,Fin.sum_univ_zero,add_zero] at hrat
  nlinarith

theorem F_pairRoot_simple_of_unique_occurrence (a : FPositiveZeroOccurrence)
    (hunique : ∀ z : FPositiveZeroOccurrence, F_pairRoot z=F_pairRoot a → z=a) :
    analyticOrderNatAt F (F_pairRoot a)=1 := by
  let e := F_pairRootFiberEquiv ⟨F_pairRoot a,F_pairRoot_is_zero a⟩ a.property
  have hinj : Function.Injective
      (fun _ : Fin (analyticOrderNatAt F (F_pairRoot a)) ↦ ()) := by
    intro i j hij
    apply e.symm.injective
    apply Subtype.ext
    exact (hunique _ (e.symm i).property).trans (hunique _ (e.symm j).property).symm
  have hcard := Fintype.card_le_of_injective _ hinj
  simp only [Fintype.card_fin,Fintype.card_unit] at hcard
  have hpos := F_zero_order_pos (F_pairRoot a) (F_pairRoot_is_zero a)
  omega

end ReciprocalXi
