import ProofWorkspace.Final.XiThetaBoundsFull

/-!
# Actual theta/Mellin representation on the central strip

This module derives the theta integral identity from mathlib's actual
completed-zeta definition. No representation or central norm bound is assumed.
-/

noncomputable section
open MeasureTheory Set
namespace ReciprocalXi

def upperThetaKernel (t : ℝ) : ℂ :=
  (Ioi 1).indicator (fun u : ℝ => ((HurwitzZeta.cosKernel 0 u - 1 : ℝ) : ℂ)) t

theorem mellin_upperThetaKernel (s : ℂ) :
    mellin upperThetaKernel s = ∫ t : ℝ in Ioi 1, thetaMellinIntegrand s t := by
  unfold mellin upperThetaKernel
  simp_rw [← indicator_smul]
  rw [setIntegral_indicator measurableSet_Ioi]
  have hi : Ioi (0 : ℝ) ∩ Ioi 1 = Ioi 1 := by
    ext t
    simp only [mem_inter_iff, mem_Ioi]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨lt_trans zero_lt_one h, h⟩
  rw [hi]
  rfl

theorem mellinConvergent_upperThetaKernel (s : ℂ) (hs : s.re ≤ 1) :
    MellinConvergent upperThetaKernel s := by
  unfold MellinConvergent upperThetaKernel
  simp_rw [← indicator_smul]
  rw [IntegrableOn, integrable_indicator_iff measurableSet_Ioi,
    IntegrableOn, Measure.restrict_restrict measurableSet_Ioi]
  have hi : Ioi (1 : ℝ) ∩ Ioi 0 = Ioi 1 := by
    ext t
    simp only [mem_inter_iff, mem_Ioi]
    constructor
    · exact fun h => h.1
    · exact fun h => ⟨h, lt_trans zero_lt_one h⟩
  rw [hi]
  exact integrableOn_thetaMellinIntegrand s hs

theorem hurwitzZero_f_modif_eq (t : ℝ) (ht : 0 < t) :
    (HurwitzZeta.hurwitzEvenFEPair 0).f_modif t =
      upperThetaKernel t + (t : ℂ) ^ (-(1 / 2 : ℂ)) * upperThetaKernel t⁻¹ := by
  have hp : (t : ℂ) ^ (-(1 / 2 : ℂ)) = ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
    simpa using (Complex.ofReal_cpow ht.le (-(1 / 2 : ℝ))).symm
  have hf := HurwitzZeta.evenKernel_functional_equation 0 t
  rw [HurwitzZeta.evenKernel_eq_cosKernel_of_zero] at hf
  have hf' : HurwitzZeta.cosKernel 0 t =
      t ^ (-(1 / 2 : ℝ)) * HurwitzZeta.cosKernel 0 t⁻¹ := by
    simpa only [Real.rpow_neg ht.le, one_div] using hf
  rw [hp]
  unfold WeakFEPair.f_modif HurwitzZeta.hurwitzEvenFEPair upperThetaKernel
  simp only [Pi.add_apply, Function.comp_apply, if_true, one_mul, smul_eq_mul, mul_one]
  rw [HurwitzZeta.evenKernel_eq_cosKernel_of_zero]
  rcases lt_trichotomy t 1 with hlt | heq | hgt
  · have hinv : 1 < t⁻¹ := (one_lt_inv₀ ht).mpr hlt
    simp only [indicator_of_notMem (notMem_Ioi.mpr hlt.le),
      indicator_of_mem (show t ∈ Ioo (0 : ℝ) 1 from ⟨ht, hlt⟩),
      indicator_of_mem (show t⁻¹ ∈ Ioi (1 : ℝ) from hinv), zero_add]
    rw [hf']
    push_cast
    ring
  · subst t
    simp
  · have hinv : t⁻¹ < 1 := (inv_lt_one₀ ht).mpr hgt
    simp only [indicator_of_mem (show t ∈ Ioi (1 : ℝ) from hgt),
      indicator_of_notMem (show t ∉ Ioo (0 : ℝ) 1 from fun h => (not_lt.mpr hgt.le) h.2),
      indicator_of_notMem (notMem_Ioi.mpr hinv.le), mul_zero, add_zero]
    push_cast
    rfl

theorem mellinConvergent_upperThetaKernel_inv (s : ℂ) (hs : (-s).re ≤ 1) :
    MellinConvergent (fun t : ℝ => upperThetaKernel t⁻¹) s := by
  have h := (MellinConvergent.comp_rpow (f := upperThetaKernel) (s := s)
    (a := (-1 : ℝ)) (by norm_num)).mpr
    (show MellinConvergent upperThetaKernel (s / ((-1 : ℝ) : ℂ)) from by
      convert mellinConvergent_upperThetaKernel (-s) hs using 1
      push_cast
      ring)
  simpa only [Real.rpow_neg_one] using h

theorem mellin_hurwitzZero_f_modif (s : ℂ)
    (hs : s.re ≤ 1) (hs' : ((1 / 2 : ℂ) - s).re ≤ 1) :
    mellin (HurwitzZeta.hurwitzEvenFEPair 0).f_modif s =
      mellin upperThetaKernel s + mellin upperThetaKernel ((1 / 2 : ℂ) - s) := by
  have hinv : MellinConvergent (fun t : ℝ => upperThetaKernel t⁻¹)
      (s + (-(1 / 2 : ℂ))) := by
    apply mellinConvergent_upperThetaKernel_inv
    convert hs' using 1
    ring_nf
  have hleft : MellinConvergent
      (fun t : ℝ => (t : ℂ) ^ (-(1 / 2 : ℂ)) • upperThetaKernel t⁻¹) s :=
    MellinConvergent.cpow_smul.mpr hinv
  have hsplit := (hasMellin_add (mellinConvergent_upperThetaKernel s hs) hleft).2
  have hcongr : mellin (HurwitzZeta.hurwitzEvenFEPair 0).f_modif s =
      mellin (fun t : ℝ => upperThetaKernel t +
        (t : ℂ) ^ (-(1 / 2 : ℂ)) • upperThetaKernel t⁻¹) s := by
    unfold mellin
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [hurwitzZero_f_modif_eq t ht]
    rfl
  rw [hcongr, hsplit, mellin_cpow_smul, mellin_comp_inv]
  congr 2
  ring

/-- The actual pole-removed completed zeta equals two upper theta integrals.
The identity is derived from the library definition and the theta functional
equation, including the lower-interval inversion substitution. -/
theorem completedRiemannZeta₀_eq_thetaMellin (s : ℂ)
    (hs0 : 0 ≤ s.re) (hs1 : s.re ≤ 1) :
    completedRiemannZeta₀ s =
      ((∫ t : ℝ in Ioi 1, thetaMellinIntegrand (s / 2) t) +
        ∫ t : ℝ in Ioi 1, thetaMellinIntegrand ((1 - s) / 2) t) / 2 := by
  have hσ : (s / 2).re ≤ 1 := by simp only [Complex.div_ofNat_re]; linarith
  have hσ' : ((1 / 2 : ℂ) - s / 2).re ≤ 1 := by
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
    linarith
  unfold completedRiemannZeta₀ HurwitzZeta.completedHurwitzZetaEven₀ WeakFEPair.Λ₀
  rw [mellin_hurwitzZero_f_modif (s / 2) hσ hσ', mellin_upperThetaKernel,
    mellin_upperThetaKernel]
  rw [show (1 / 2 : ℂ) - s / 2 = (1 - s) / 2 by ring]

/-- A proved norm bound throughout the central complex strip. -/
theorem completedRiemannZeta₀_norm_lt_two (s : ℂ)
    (hs0 : 0 ≤ s.re) (hs1 : s.re ≤ 1) :
    ‖completedRiemannZeta₀ s‖ < 2 := by
  have hσ : (s / 2).re ≤ 1 := by simp only [Complex.div_ofNat_re]; linarith
  have hσ' : ((1 - s) / 2).re ≤ 1 := by
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
    linarith
  have h₁ := thetaMellinIntegral_norm_lt_two (s / 2) hσ
  have h₂ := thetaMellinIntegral_norm_lt_two ((1 - s) / 2) hσ'
  have hsum := norm_add_le
    (∫ t : ℝ in Ioi 1, thetaMellinIntegrand (s / 2) t)
    (∫ t : ℝ in Ioi 1, thetaMellinIntegrand ((1 - s) / 2) t)
  rw [completedRiemannZeta₀_eq_thetaMellin s hs0 hs1, norm_div]
  norm_num only [Complex.norm_ofNat]
  linarith

/-- Positivity of the real part of the actual normalized Xi on [0,1].
Its entire completed-zeta factor is controlled by the proved theta bound. -/
theorem xi_re_pos_of_mem_Icc (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    0 < (xi (s : ℂ)).re := by
  have hnorm := completedRiemannZeta₀_norm_lt_two (s : ℂ) hs.1 hs.2
  have hq : (completedRiemannZeta₀ (s : ℂ)).re ≤ 2 :=
    (Complex.re_le_norm _).trans hnorm.le
  have ht : 0 ≤ s * (1 - s) := mul_nonneg hs.1 (sub_nonneg.mpr hs.2)
  have htmax : s * (1 - s) ≤ 1 / 4 := by nlinarith [sq_nonneg (s - 1 / 2)]
  have hprod := mul_le_mul_of_nonneg_left hq ht
  have hform : (xi (s : ℂ)).re =
      (1 - s * (1 - s) * (completedRiemannZeta₀ (s : ℂ)).re) / 2 := by
    simp only [xi, Complex.div_ofNat_re, Complex.add_re, Complex.mul_re, Complex.mul_im,
      Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_re, Complex.one_im, mul_zero, zero_mul, sub_zero, zero_add]
    ring
  rw [hform]
  nlinarith

/-- The explicit Gaussian majorant also bounds the actual entire completed
factor, not merely either of its constituent integrals. -/
theorem completedRiemannZeta₀_norm_le_thetaBound (s : ℂ)
    (hs0 : 0 ≤ s.re) (hs1 : s.re ≤ 1) :
    ‖completedRiemannZeta₀ s‖ ≤ 4 * Real.exp (-Real.pi) / Real.pi := by
  have hσ : (s / 2).re ≤ 1 := by simp only [Complex.div_ofNat_re]; linarith
  have hσ' : ((1 - s) / 2).re ≤ 1 := by
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
    linarith
  have h₁ := thetaMellinIntegral_norm_le (s / 2) hσ
  have h₂ := thetaMellinIntegral_norm_le ((1 - s) / 2) hσ'
  have hsum := norm_add_le
    (∫ t : ℝ in Ioi 1, thetaMellinIntegrand (s / 2) t)
    (∫ t : ℝ in Ioi 1, thetaMellinIntegrand ((1 - s) / 2) t)
  rw [completedRiemannZeta₀_eq_thetaMellin s hs0 hs1, norm_div]
  norm_num only [Complex.norm_ofNat]
  linarith

theorem completedRiemannZeta₀_norm_lt_one (s : ℂ)
    (hs0 : 0 ≤ s.re) (hs1 : s.re ≤ 1) :
    ‖completedRiemannZeta₀ s‖ < 1 := by
  apply lt_of_le_of_lt (completedRiemannZeta₀_norm_le_thetaBound s hs0 hs1)
  have he : 2 < Real.exp Real.pi := by linarith [Real.add_one_le_exp Real.pi, Real.two_le_pi]
  have hinv : Real.exp (-Real.pi) < 1 / 2 := by
    rw [Real.exp_neg, ← one_div]
    apply (div_lt_iff₀ (Real.exp_pos Real.pi)).mpr
    linarith
  apply (div_lt_iff₀ Real.pi_pos).mpr
  linarith [Real.two_le_pi]

/-- A small complex zero-free rectangle, from the same explicit theta bound.
The product bound used here is ≤1, not the false ≤1/2 bound at height 1/2. -/
theorem xi_ne_zero_of_central_rectangle (s : ℂ)
    (hs0 : 0 ≤ s.re) (hs1 : s.re ≤ 1) (hsim : |s.im| ≤ 1 / 2) :
    xi s ≠ 0 := by
  have h₁ : ‖s‖ ≤ s.re + |s.im| := by
    simpa only [abs_of_nonneg hs0] using Complex.norm_le_abs_re_add_abs_im s
  have h₂ : ‖s - 1‖ ≤ 1 - s.re + |s.im| := by
    have h := Complex.norm_le_abs_re_add_abs_im (s - 1)
    simpa only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
      sub_zero, abs_of_nonpos (sub_nonpos.mpr hs1), neg_sub] using h
  have hp₁ : ‖s‖ * ‖s - 1‖ ≤ (s.re + |s.im|) * (1 - s.re + |s.im|) :=
    mul_le_mul h₁ h₂ (norm_nonneg _) (by positivity)
  have hm : s.re * (1 - s.re) ≤ 1 / 4 := by
    nlinarith [sq_nonneg (s.re - 1 / 2)]
  have hd : |s.im| ^ 2 ≤ 1 / 4 := by nlinarith [abs_nonneg s.im]
  have hp : ‖s‖ * ‖s - 1‖ ≤ 1 := by nlinarith
  have hnorm := completedRiemannZeta₀_norm_lt_one s hs0 hs1
  have hsmall : ‖s * (s - 1) * completedRiemannZeta₀ s‖ < 1 := by
    rw [norm_mul, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hp).trans_lt hnorm
  intro hz
  have hn : s * (s - 1) * completedRiemannZeta₀ s + 1 = 0 := by
    have h := congrArg (fun z : ℂ => z * 2) hz
    simpa only [xi, div_mul_cancel₀ _ (by norm_num : (2 : ℂ) ≠ 0), zero_mul] using h
  have heq : s * (s - 1) * completedRiemannZeta₀ s = -1 := by
    linear_combination hn
  rw [heq, norm_neg, norm_one] at hsmall
  exact (lt_irrefl (1 : ℝ)) hsmall

end ReciprocalXi

end
