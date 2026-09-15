import ProofWorkspace.Final.XiSelectedResidualLawFull
import ProofWorkspace.Final.XiMomentExponentFull
import ProofWorkspace.Final.HeatExponentialFull
import ProofWorkspace.Final.GaussianMixtureAbsoluteFull

set_option autoImplicit false
noncomputable section
open Set Filter Topology Complex MeasureTheory ProbabilityTheory Measure
open scoped ENNReal NNReal
namespace ReciprocalXi

theorem integrableOn_F_selectedMoment_real (S : Set FPositiveZeroOccurrence)
    {x : ℝ} (hx : 0≤x) (hgap : ∀ z∈S, x<((F_pairRoot z)^2).re) :
    IntegrableOn (fun t : ℝ ↦ ((Real.exp (x*t)-1)/t)*(F_selectedHeatTrace S t).re)
      (Ioi 0) := by
  have hh := Complex.reCLM.integrable_comp (integrableOn_F_selectedMomentIntegrand S hx hgap)
  simpa only [F_selectedMomentIntegrand, F_momentHeatKernel, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.reCLM_apply] using hh

theorem F_selectedMomentExponent_re_eq (S : Set FPositiveZeroOccurrence)
    {x : ℝ} (hx : 0≤x) (hgap : ∀ z∈S, x<((F_pairRoot z)^2).re) :
    (F_selectedMomentExponent S x).re=
      ∫ t : ℝ in Ioi 0, ((Real.exp (x*t)-1)/t)*(F_selectedHeatTrace S t).re := by
  have hh := Complex.reCLM.integral_comp_comm (integrableOn_F_selectedMomentIntegrand S hx hgap)
  simpa only [F_selectedMomentExponent, F_selectedMomentIntegrand, F_momentHeatKernel,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.reCLM_apply] using hh.symm

theorem F_selectedResidualLaw_exponentialMoment (S : Set FPositiveZeroOccurrence)
    (hpos : ∀ t : ℝ, 0<t → 0≤(F_selectedHeatTrace S t).re) (q : ℝ)
    (hgap : ∀ z∈S, q^2<((F_pairRoot z)^2).re) :
    Integrable (fun y : ℝ ↦ Real.exp (q*y)) (F_selectedResidualLaw S) ∧
      exponentialMoment (F_selectedResidualLaw S) q=
        Real.exp (F_selectedMomentExponent S (q^2)).re := by
  have hn : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0), 0≤(F_selectedHeatTrace S t).re := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hpos t ht
  have hi := integrableOn_F_selectedHeatTrace_re S
  letI := heatSubordinatorLaw_isProbability hi hn
  have hm := heatSubordinatorLaw_exponentialMoment hi hn (sq_nonneg q)
    (integrableOn_F_selectedMoment_real S (sq_nonneg q) hgap)
  have hs := ae_nonneg_heatSubordinatorLaw hi hn
  refine ⟨integrable_exp_gaussianVarianceMixture _ hs q hm.1, ?_⟩
  rw [F_selectedResidualLaw, exponentialMoment_gaussianVarianceMixture _ hs q hm.1, hm.2,
    F_selectedMomentExponent_re_eq S (sq_nonneg q) hgap]

theorem F_selectedResidualLaw_absoluteMoment (S : Set FPositiveZeroOccurrence)
    (hpos : ∀ t : ℝ, 0<t → 0≤(F_selectedHeatTrace S t).re) (q : ℝ)
    (hgap : ∀ z∈S, q^2<((F_pairRoot z)^2).re) :
    Integrable (fun y : ℝ ↦ Real.exp (q*|y|)) (F_selectedResidualLaw S) ∧
      (∫ y : ℝ, Real.exp (q*|y|) ∂F_selectedResidualLaw S)≤
        2*Real.exp (F_selectedMomentExponent S (q^2)).re := by
  have hp := F_selectedResidualLaw_exponentialMoment S hpos q hgap
  have hgap' : ∀ z∈S, (-q)^2<((F_pairRoot z)^2).re := by simpa only [neg_sq] using hgap
  have hm := F_selectedResidualLaw_exponentialMoment S hpos (-q) hgap'
  refine ⟨integrable_exp_abs_of_two_sided _ q hp.1 hm.1, ?_⟩
  have hh := integral_exp_abs_le_two_sided _ q hp.1 hm.1
  rw [hp.2, hm.2, neg_sq] at hh
  linarith

theorem F_selectedResidualLaw_even (S : Set FPositiveZeroOccurrence)
    (hpos : ∀ t : ℝ, 0<t → 0≤(F_selectedHeatTrace S t).re) :
    MeasurePreserving (fun y : ℝ ↦ -y) (F_selectedResidualLaw S) (F_selectedResidualLaw S) := by
  have hn : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0), 0≤(F_selectedHeatTrace S t).re := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hpos t ht
  have hi := integrableOn_F_selectedHeatTrace_re S
  letI := heatSubordinatorLaw_isProbability hi hn
  exact gaussianVarianceMixture_even _ (ae_nonneg_heatSubordinatorLaw hi hn)

end ReciprocalXi
