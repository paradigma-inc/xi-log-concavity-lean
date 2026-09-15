import ProofWorkspace.Final.XiSelectedHeatIntegralFull

set_option autoImplicit false
noncomputable section
open Set Filter Topology Complex MeasureTheory
namespace ReciprocalXi

def F_momentHeatKernel (x t : ℝ) : ℂ := (((Real.exp (x*t)-1)/t:ℝ):ℂ)

theorem norm_F_momentHeatKernel_le {x t : ℝ} (hx : 0≤x) (ht : 0<t) :
    ‖F_momentHeatKernel x t‖ ≤ x*Real.exp (x*t) := by
  have he : 1≤Real.exp (x*t) := Real.one_le_exp_iff.mpr (mul_nonneg hx ht.le)
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-x*t)) (Real.exp_pos (x*t)).le
  rw [← Real.exp_add, show -x*t+x*t=0 by ring, Real.exp_zero] at h
  rw [F_momentHeatKernel, Complex.norm_real, Real.norm_eq_abs, abs_div,
    abs_of_nonneg (sub_nonneg.mpr he), abs_of_pos ht]
  apply (div_le_iff₀ ht).mpr
  nlinarith

def F_selectedMomentIntegrand (S : Set FPositiveZeroOccurrence) (x t : ℝ) : ℂ :=
  F_momentHeatKernel x t*F_selectedHeatTrace S t

def F_selectedMomentExponent (S : Set FPositiveZeroOccurrence) (x : ℝ) : ℂ :=
  ∫ t : ℝ in Ioi 0, F_selectedMomentIntegrand S x t

theorem integrableOn_F_selectedMomentIntegrand (S : Set FPositiveZeroOccurrence)
    {x : ℝ} (hx : 0≤x) (hgap : ∀ z∈S, x<((F_pairRoot z)^2).re) :
    IntegrableOn (F_selectedMomentIntegrand S x) (Ioi 0) := by
  have hw := integrableOn_F_selectedHeatTrace_weight S x hgap
  apply (hw.norm.const_mul x).mono'
  · apply AEStronglyMeasurable.mul _ (integrableOn_F_selectedHeatTrace S).1
    exact (show Measurable (F_momentHeatKernel x) by unfold F_momentHeatKernel; fun_prop).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp only [F_selectedMomentIntegrand, norm_mul]
    have he : ‖Complex.exp ((x:ℂ)*(t:ℂ))‖=Real.exp (x*t) := by
      simp [Complex.norm_exp, Complex.mul_re]
    rw [he]
    calc
      _ ≤ (x*Real.exp (x*t))*‖F_selectedHeatTrace S t‖ :=
        mul_le_mul_of_nonneg_right (norm_F_momentHeatKernel_le hx ht) (norm_nonneg _)
      _ = _ := by ring

theorem F_selectedMomentExponent_im (S : Set FPositiveZeroOccurrence)
    (hS : ∀ z∈S, F_pairConj z∈S) {x : ℝ} (hx : 0≤x)
    (hgap : ∀ z∈S, x<((F_pairRoot z)^2).re) :
    (F_selectedMomentExponent S x).im=0 := by
  have hi : (∫ t : ℝ in Ioi 0, (F_selectedMomentIntegrand S x t).im)=
      (F_selectedMomentExponent S x).im :=
    Complex.imCLM.integral_comp_comm (integrableOn_F_selectedMomentIntegrand S hx hgap)
  rw [← hi]
  simp only [F_selectedMomentIntegrand, F_momentHeatKernel, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, F_selectedHeatTrace_im S hS,
    mul_zero, zero_mul, add_zero, integral_zero]

theorem F_selectedMomentExponent_re_nonneg (S : Set FPositiveZeroOccurrence)
    (hpos : ∀ t>0, 0≤(F_selectedHeatTrace S t).re) {x : ℝ} (hx : 0≤x)
    (hgap : ∀ z∈S, x<((F_pairRoot z)^2).re) :
    0≤(F_selectedMomentExponent S x).re := by
  have hi : (∫ t : ℝ in Ioi 0, (F_selectedMomentIntegrand S x t).re)=
      (F_selectedMomentExponent S x).re :=
    Complex.reCLM.integral_comp_comm (integrableOn_F_selectedMomentIntegrand S hx hgap)
  rw [← hi]
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simp only [F_selectedMomentIntegrand, F_momentHeatKernel, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_nonneg (div_nonneg (sub_nonneg.mpr (Real.one_le_exp_iff.mpr
    (mul_nonneg hx ht.le))) ht.le) (hpos t ht)

end ReciprocalXi
