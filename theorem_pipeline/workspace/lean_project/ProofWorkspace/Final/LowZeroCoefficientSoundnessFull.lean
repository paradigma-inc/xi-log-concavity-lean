import ProofWorkspace.Final.LowZeroCoefficientChecksFull

set_option autoImplicit false
noncomputable section
namespace ReciprocalXi

theorem ratLowZeroCoefficientsValid_error (x c h : ℚ) (k : ℕ) (w : ℕ → ℚ × ℚ) (r : ℕ → ℚ)
    (hv : ratLowZeroCoefficientsValid x c h sourcePiMidpoint k w r)
    (hseed : ‖ratComplexValue (w 0)-complexPowerExpAtom (complexThetaExponent x)
      (Real.pi*(k:ℝ)^2) (c:ℂ)‖≤(lowZeroSeedRadius (w 0):ℝ)) :
    ∀ n, n<80 →
      ‖ratComplexValue (w n)-scaledPowerExpCoefficient (complexThetaExponent x)
        (c:ℂ) (Real.pi*(k:ℝ)^2) h n‖≤(lowZeroCoefficientRadius r n:ℝ) := by
  obtain ⟨hk,hc,hh0,hh1,hunit,hseedRadius,huniform,hfirst,hstep,hE1,hE⟩ := hv
  have hcR : (1:ℝ)≤c := by exact_mod_cast hc
  have hh0R : (0:ℝ)≤h := by exact_mod_cast hh0
  have hh1R : (h:ℝ)≤1 := by exact_mod_cast hh1
  have hc0R : (c:ℝ)≠0 := by linarith
  have hl := lowZeroLambda_midpoint_error k hk
  let delta : ℝ := (thetaCoefficientTransitionDelta:ℝ)
  let rho : ℝ := (lowZeroCoefficientRoundRadius:ℝ)
  have hdelta : delta=1/(10:ℝ)^140 := by
    simp [delta,thetaCoefficientTransitionDelta]
  let W : ℕ → ℂ := fun n ↦ ratComplexValue (w n)
  let a : ℕ → ℂ := scaledPowerExpCoefficient (complexThetaExponent x)
    (c:ℂ) (Real.pi*(k:ℝ)^2) h
  let D : ℂ := powerExpScaledFirst (complexThetaExponent x) c h (Real.pi*(k:ℝ)^2)
  let A : ℕ → ℂ := powerExpScaledA (complexThetaExponent x) c h (Real.pi*(k:ℝ)^2)
  let B : ℕ → ℂ := powerExpScaledB c h (Real.pi*(k:ℝ)^2)
  have hd0 : 0≤delta := by dsimp [delta,thetaCoefficientTransitionDelta]; positivity
  have hw : ∀ n, n<80 → ‖W n‖≤1 := by
    intro n hn
    exact (ratComplexValue_norm_le_L1 (w n)).trans (by
      simpa only [Rat.cast_one] using (Rat.cast_le (K:=ℝ)).mpr (hunit ⟨n,hn⟩))
  have hD : ‖D-ratComplexValue (ratLowZeroFirst x c h sourcePiMidpoint k)‖≤delta := by
    rw [ratLowZeroFirst_value,hdelta]
    exact powerExpScaledFirst_perturbation _ _ _ _ _ _ hc0R hh0R hh1R hl
  have hA : ∀ n, ‖A n-ratComplexValue (ratLowZeroA x c h sourcePiMidpoint k n)‖≤delta := by
    intro n
    rw [ratLowZeroA_value,hdelta]
    exact powerExpScaledA_perturbation _ _ _ _ _ _ _ hc0R hh0R hh1R hl
  have hB : ∀ n, ‖B n-ratComplexValue (ratThetaB c h sourcePiMidpoint k n)‖≤delta := by
    intro n
    rw [ratThetaB_value,hdelta]
    exact powerExpScaledB_perturbation _ _ _ _ _ _ hcR hh0R hh1R hl
  have hDn := complex_norm_le_rat_approx D _ delta hD
  have ha0 : ‖W 0-a 0‖≤(lowZeroCoefficientRadius r 0:ℝ) := by
    have hr : (lowZeroSeedRadius (w 0):ℝ)≤(lowZeroCoefficientRadius r 0:ℝ) :=
      (Rat.cast_le (K:=ℝ)).mpr hseedRadius
    simpa [a,W,scaledPowerExpCoefficient_zero] using hseed.trans hr
  have hr0 : ‖W 1-D*W 0‖≤rho+delta := by
    have ht := ratComplexValue_norm_le_L1
      (ratComplexSub (w 1) (ratComplexMul (ratLowZeroFirst x c h sourcePiMidpoint k) (w 0)))
    rw [ratComplexValue_sub,ratComplexValue_mul] at ht
    have ht0 : ‖W 1-ratComplexValue (ratLowZeroFirst x c h sourcePiMidpoint k)*W 0‖≤rho :=
      ht.trans ((Rat.cast_le (K:=ℝ)).mpr hfirst)
    have he : ratComplexValue (ratLowZeroFirst x c h sourcePiMidpoint k)*W 0-D*W 0=
        (ratComplexValue (ratLowZeroFirst x c h sourcePiMidpoint k)-D)*W 0 := by ring
    have ht1 := norm_sub_le_norm_sub_add_norm_sub (W 1)
      (ratComplexValue (ratLowZeroFirst x c h sourcePiMidpoint k)*W 0) (D*W 0)
    rw [he,norm_mul] at ht1
    have hDrev : ‖ratComplexValue (ratLowZeroFirst x c h sourcePiMidpoint k)-D‖≤delta := by
      rw [norm_sub_rev]
      exact hD
    have hm := mul_le_mul hDrev (hw 0 (by norm_num)) (norm_nonneg _) hd0
    linarith
  have ha1 : ‖W 1-a 1‖≤(lowZeroCoefficientRadius r 1:ℝ) := by
    have he : a 1=D*a 0 := scaledPowerExpCoefficient_one_eq _ _ _ _ (by linarith)
    rw [he]
    have ht := complex_recurrence_step_error D 0 (a 0) 0 (W 0) 0 (W 1) (rho+delta)
      (by simpa using hr0)
    simp only [zero_mul,sub_zero,norm_zero,mul_zero,add_zero] at ht
    have hpos : 0≤(ratComplexL1 (ratLowZeroFirst x c h sourcePiMidpoint k):ℝ)+delta :=
      (norm_nonneg D).trans hDn
    have hm := mul_le_mul hDn ha0 (norm_nonneg _) hpos
    have heR : rho+delta+
        ((ratComplexL1 (ratLowZeroFirst x c h sourcePiMidpoint k):ℝ)+delta)*
          (lowZeroCoefficientRadius r 0:ℝ)≤(lowZeroCoefficientRadius r 1:ℝ) := by
      have hcast := (Rat.cast_le (K:=ℝ)).mpr hE1
      push_cast at hcast
      exact hcast
    linarith
  apply complex_second_order_error a W A B
    (fun n ↦ (ratComplexL1 (ratLowZeroA x c h sourcePiMidpoint k n):ℝ)+delta)
    (fun n ↦ (ratComplexL1 (ratThetaB c h sourcePiMidpoint k n):ℝ)+delta)
    (fun n ↦ (lowZeroCoefficientRadius r n:ℝ)) (fun _ ↦ rho+2*delta) 80 ha0 ha1
  · intro n
    exact_mod_cast lowZeroCoefficientRadius_nonneg r n
  · intro n hn
    exact scaledPowerExpCoefficient_recurrence_eq _ _ _ _ _ (by linarith)
  · intro n hn
    have hn78 : n<78 := by omega
    have ht := ratComplexValue_norm_le_L1
      (ratComplexSub (w (n+2))
        (ratComplexSub (ratComplexMul (ratLowZeroA x c h sourcePiMidpoint k n) (w (n+1)))
          (ratComplexMul (ratThetaB c h sourcePiMidpoint k n) (w n))))
    rw [ratComplexValue_sub,ratComplexValue_sub,ratComplexValue_mul,ratComplexValue_mul] at ht
    have ht0 : ‖W (n+2)-(ratComplexValue (ratLowZeroA x c h sourcePiMidpoint k n)*W (n+1)-
        ratComplexValue (ratThetaB c h sourcePiMidpoint k n)*W n)‖≤rho :=
      ht.trans ((Rat.cast_le (K:=ℝ)).mpr (hstep ⟨n,hn78⟩))
    have hp := complex_linear_pair_perturbation
      (ratComplexValue (ratLowZeroA x c h sourcePiMidpoint k n))
      (ratComplexValue (ratThetaB c h sourcePiMidpoint k n))
      (A n) (B n) (W (n+1)) (W n) delta delta
      (by rw [norm_sub_rev]; exact hA n) (by rw [norm_sub_rev]; exact hB n)
    have ht1 := norm_sub_le_norm_sub_add_norm_sub (W (n+2))
      (ratComplexValue (ratLowZeroA x c h sourcePiMidpoint k n)*W (n+1)-
        ratComplexValue (ratThetaB c h sourcePiMidpoint k n)*W n)
      (A n*W (n+1)-B n*W n)
    have hm1 := mul_le_mul_of_nonneg_left (hw (n+1) (by omega)) hd0
    have hm0 := mul_le_mul_of_nonneg_left (hw n (by omega)) hd0
    linarith
  · intro n hn
    exact complex_norm_le_rat_approx _ _ _ (hA n)
  · intro n hn
    exact complex_norm_le_rat_approx _ _ _ (hB n)
  · intro n hn
    have hcast := (Rat.cast_le (K:=ℝ)).mpr (hE ⟨n,by omega⟩)
    push_cast at hcast
    exact hcast

theorem ratLowZeroCoefficientsValid_uniform_error (x c h : ℚ) (k : ℕ)
    (w : ℕ → ℚ × ℚ) (r : ℕ → ℚ)
    (hv : ratLowZeroCoefficientsValid x c h sourcePiMidpoint k w r)
    (hseed : ‖ratComplexValue (w 0)-complexPowerExpAtom (complexThetaExponent x)
      (Real.pi*(k:ℝ)^2) (c:ℂ)‖≤(lowZeroSeedRadius (w 0):ℝ)) :
    ∀ n, n<80 →
      ‖ratComplexValue (w n)-scaledPowerExpCoefficient (complexThetaExponent x)
        (c:ℂ) (Real.pi*(k:ℝ)^2) h n‖≤1/(10:ℝ)^50 := by
  have he := ratLowZeroCoefficientsValid_error x c h k w r hv hseed
  obtain ⟨hk,hc,hh0,hh1,hunit,hseedRadius,huniform,hfirst,hstep,hE1,hE⟩ := hv
  intro n hn
  apply (he n hn).trans
  simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat] using
    (Rat.cast_le (K:=ℝ)).mpr (huniform ⟨n,hn⟩)

end ReciprocalXi


