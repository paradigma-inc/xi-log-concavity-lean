import ProofWorkspace.Final.XiMomentBootstrapFull

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 6000000
noncomputable section
namespace ReciprocalXi

theorem momentSampleNode_cast_power (j : Fin 33) (m : ℕ) :
    ((j:ℝ)/40)^(2*m)=(momentSampleNode j:ℝ)^m := by
  rw [pow_mul]
  congr 1
  unfold momentSampleNode
  push_cast
  ring

theorem momentCoefficientWeights_real (m : ℕ) (hm : m<33) :
    (∑ j : Fin 33, (momentCoefficientWeight j:ℝ)*(momentSampleNode j:ℝ)^m)=
      if m=16 then 1 else 0 := by
  have h := momentCoefficientWeights_exact ⟨m,hm⟩
  have hc := congrArg (fun r : ℚ ↦ (r:ℝ)) h
  push_cast at hc
  by_cases h16 : m=16
  · simpa only [Fin.val_mk,h16,if_true,Rat.cast_one] using hc
  · simpa only [Fin.val_mk,h16,if_false,Rat.cast_zero] using hc

theorem F_momentTaylor_weighted_extraction :
    (∑ j : Fin 33, (momentCoefficientWeight j:ℝ)*F_momentTaylor 32 ((j:ℝ)/40))=
      -F_pairMoment 16/16 := by
  unfold F_momentTaylor
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hterm (m : ℕ) (hm : m∈Finset.range 33) :
      (∑ j : Fin 33, (momentCoefficientWeight j:ℝ)*
        ((-1:ℝ)^(m+1)*((j:ℝ)/40)^(2*m)/(m:ℝ)*F_pairMoment m))=
      if m=16 then -F_pairMoment 16/16 else 0 := by
    simp_rw [momentSampleNode_cast_power]
    calc
      _=((-1:ℝ)^(m+1)/(m:ℝ)*F_pairMoment m)*
          (∑ j : Fin 33, (momentCoefficientWeight j:ℝ)*(momentSampleNode j:ℝ)^m) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _=_ := by
        rw [momentCoefficientWeights_real m (Finset.mem_range.mp hm)]
        split_ifs with h
        · subst m
          norm_num
          ring
        · simp
  rw [Finset.sum_congr rfl hterm]
  simp

theorem F_momentTaylor_thirtyTwo_uniform (j : Fin 33) :
    |F_momentLog ((j:ℝ)/40)-F_momentTaylor 32 ((j:ℝ)/40)|≤
      (momentThirtyTwoRemainder:ℝ) := by
  have hj : (j:ℝ)≤32 := by exact_mod_cast (show (j:ℕ)≤32 by omega)
  have hsq : ((j:ℝ)/40)^2≤16/25 := by
    have h := pow_le_pow_left₀ (Nat.cast_nonneg (j:ℕ)) hj 2
    nlinarith
  have he := F_momentTaylor_error_of_mass_bound 32 ((j:ℝ)/40) 24 (1/150)
    (by norm_num) (fun z ↦ (F_pairRoot_re_gt_twentyFour z).le)
    (by nlinarith) F_pairRoot_inv_norm_sq_tsum_lt_one_fifty.le
  apply he.trans
  calc
    _≤(1/150:ℝ)*(16/25)*((16/25)/24^2)^32/(33*(1-(16/25)/24^2)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) _
      · gcongr
      · norm_num
        nlinarith
    _=(momentThirtyTwoRemainder:ℝ) := by
      norm_num [momentThirtyTwoRemainder]

theorem F_pairMoment_sixteen_bound : F_pairMoment 16≤(momentSixteenUpper:ℝ) := by
  let e : ℝ := (momentThirtyTwoRemainder:ℝ)+1/(10:ℝ)^118
  have he (j : Fin 33) :
      |(momentLogSample j:ℝ)-F_momentTaylor 32 ((j:ℝ)/40)|≤e := by
    have hlog : |F_momentLog ((j:ℝ)/40)-(momentLogSample j:ℝ)|≤1/(10:ℝ)^118 :=
      momentLogSample_actual j
    have ht := F_momentTaylor_thirtyTwo_uniform j
    calc
      _≤|(momentLogSample j:ℝ)-F_momentLog ((j:ℝ)/40)|+
          |F_momentLog ((j:ℝ)/40)-F_momentTaylor 32 ((j:ℝ)/40)| := abs_sub_le _ _ _
      _≤e := by rw [abs_sub_comm (momentLogSample j:ℝ)]; dsimp [e]; linarith
  have hs :
      |(∑ j : Fin 33, (momentCoefficientWeight j:ℝ)*
        ((momentLogSample j:ℝ)-F_momentTaylor 32 ((j:ℝ)/40)))|≤
        (momentCoefficientWeightMass:ℝ)*e := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _≤∑ j : Fin 33, |(momentCoefficientWeight j:ℝ)| * e := by
        apply Finset.sum_le_sum
        intro j hj
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (he j) (abs_nonneg _)
      _=(momentCoefficientWeightMass:ℝ)*e := by
        rw [←Finset.sum_mul]
        unfold momentCoefficientWeightMass
        push_cast
        rfl
  simp_rw [mul_sub,Finset.sum_sub_distrib] at hs
  rw [F_momentTaylor_weighted_extraction] at hs
  have hb := (abs_le.mp hs).2
  unfold momentSixteenUpper
  push_cast
  dsimp [e] at hb
  linarith

theorem F_pairMoment_sixteen_terms_nonneg (z : FPositiveZeroOccurrence) :
    0≤(((F_pairRoot z)⁻¹)^32).re := by
  have ha := F_pairRoot_re_gt_twentyFour z
  have hs : (576:ℝ)≤(F_pairRoot z).re^2 := by nlinarith
  have hp : (0:ℝ)<2*(F_pairRoot z).re^2 := by positivity
  have hq : (32:ℝ)^2/(2*(F_pairRoot z).re^2)≤1 :=
    (div_le_one hp).mpr (by nlinarith)
  exact (div_nonneg (by linarith) (pow_nonneg (norm_nonneg _) 32)).trans
    (complex_inverse_power_re_lower (F_pairRoot z) z.property
      (F_zero_im_bound _ (F_pairRoot_is_zero z)).le 32)

end ReciprocalXi
