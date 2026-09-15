import ProofWorkspace.Final.XiMomentDensityBridgeFull
import Mathlib.Analysis.Convolution

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 6000000
noncomputable section
open MeasureTheory ProbabilityTheory
namespace ReciprocalXi

theorem integral_twoLaplace_normalized_kernel {a b : ℝ} (ha : 0<a) (hab : a<b) :
    (∫ x : ℝ, twoLaplaceJet (a*b/(2*(b^2-a^2))) a b 0 x) = 1 := by
  have h := integral_twoLaplace_normalized_character ha hab 0
  have ha0 : (a:ℂ)≠0 := by exact_mod_cast ha.ne'
  have hb0 : (b:ℂ)≠0 := by exact_mod_cast (ha.trans hab).ne'
  apply Complex.ofReal_injective
  simpa [ha0,hb0,integral_complex_ofReal] using h

theorem integrable_laplaceConvolution_kernel (μ : Measure ℝ) [IsFiniteMeasure μ]
    (C : ℝ) {a b : ℝ} (ha : 0<a) (hb : 0<b) :
    Integrable (laplaceConvolutionJet μ C a b 0) := by
  have h : Integrable (fun p : ℝ×ℝ ↦ twoLaplaceJet C a b 0 (p.1-p.2))
      (volume.prod μ) := by
    simpa only [ContinuousLinearMap.mul_apply',one_mul] using
      (integrable_const (1:ℝ) (μ:=μ)).convolution_integrand
        (ContinuousLinearMap.mul ℝ ℝ) (integrable_twoLaplace_kernel C ha hb)
  exact h.integral_prod_left

theorem integral_laplaceConvolution_normalized_kernel
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {a b : ℝ} (ha : 0<a) (hab : a<b) :
    (∫ x : ℝ, laplaceConvolutionJet μ (a*b/(2*(b^2-a^2))) a b 0 x) = 1 := by
  have h := integral_convolution (ContinuousLinearMap.mul ℝ ℝ)
    (integrable_const (1:ℝ) (μ:=μ))
    (integrable_twoLaplace_kernel (a*b/(2*(b^2-a^2))) ha (ha.trans hab))
  simpa [convolution_def,laplaceConvolutionJet,
    integral_twoLaplace_normalized_kernel ha hab] using h

theorem density_probability_of_threeLowZeroCertificate (C : ThreeLowZeroCertificate) :
    Integrable density ∧ (∫ x : ℝ, density x) = 1 := by
  classical
  letI := F_selectedResidualLaw_isProbability C.residualSet C.residual_heat_nonneg
  have he : density = laplaceConvolutionJet (F_selectedResidualLaw C.residualSet)
      (C.value 0*C.value 1/(2*(C.value 1^2-C.value 0^2))) (C.value 0) (C.value 1) 0 := by
    funext x
    exact density_eq_twoLaplace_convolution (C.occurrence 0) (C.occurrence 1)
      (C.value_pos 0) (C.value_strictMono (by decide)) (C.root_eq 0) (C.root_eq 1)
      (F_pairConj_compl_two_real _ _ (C.root_eq 0) (C.root_eq 1))
      C.residual_heat_nonneg x
  constructor
  · rw [he]
    exact integrable_laplaceConvolution_kernel _ _ (C.value_pos 0) (C.value_pos 1)
  · rw [he]
    exact integral_laplaceConvolution_normalized_kernel _
      (C.value_pos 0) (C.value_strictMono (by decide))

theorem density_probability_of_original_signs
    (hs : ∀ j : Fin 3, (F (originalLowRootLower j:ℂ)).re*
      (F (originalLowRootUpper j:ℂ)).re<0) :
    Integrable density ∧ (∫ x : ℝ, density x) = 1 := by
  obtain ⟨C⟩ := threeLowZeroCertificate_of_signs hs
  exact density_probability_of_threeLowZeroCertificate C

end ReciprocalXi
