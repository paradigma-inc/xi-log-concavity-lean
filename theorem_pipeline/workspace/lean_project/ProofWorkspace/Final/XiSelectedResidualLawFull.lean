import ProofWorkspace.Final.HeatSubordinatorFull
import ProofWorkspace.Final.GaussianVarianceMixtureFull
import ProofWorkspace.Final.XiHeatDeletionFull

set_option autoImplicit false
noncomputable section
open Set Filter Topology Complex MeasureTheory ProbabilityTheory Measure
open scoped ENNReal NNReal
namespace ReciprocalXi

theorem integrableOn_F_selectedHeatTrace_re (S : Set FPositiveZeroOccurrence) :
    IntegrableOn (fun t ↦ (F_selectedHeatTrace S t).re) (Ioi 0) :=
  Complex.reCLM.integrable_comp (integrableOn_F_selectedHeatTrace S)

theorem F_selectedHeatExponent_eq_ofReal (S : Set FPositiveZeroOccurrence)
    (hS : ∀ z∈S, F_pairConj z∈S) (u : ℝ) :
    heatExponentOf (F_selectedHeatTrace S) u=
      Complex.ofReal (∫ t : ℝ in Ioi 0, ((Real.exp (-u^2*t)-1)/t)*(F_selectedHeatTrace S t).re) := by
  rw [heatExponentOf, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards with t
  change (((Real.exp (-u^2*t)-1)/t:ℝ):ℂ)*F_selectedHeatTrace S t=_
  rw [Complex.ofReal_mul]
  congr 1
  apply Complex.ext
  · simp
  · simp [F_selectedHeatTrace_im S hS t]

def F_selectedResidualLaw (S : Set FPositiveZeroOccurrence) : Measure ℝ :=
  gaussianVarianceMixture (heatSubordinatorLaw (fun t ↦ (F_selectedHeatTrace S t).re))

theorem F_selectedResidualLaw_isProbability (S : Set FPositiveZeroOccurrence)
    (hpos : ∀ t : ℝ, 0<t → 0≤(F_selectedHeatTrace S t).re) :
    IsProbabilityMeasure (F_selectedResidualLaw S) := by
  have hn : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0), 0≤(F_selectedHeatTrace S t).re := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hpos t ht
  letI := heatSubordinatorLaw_isProbability (integrableOn_F_selectedHeatTrace_re S) hn
  exact gaussianVarianceMixture_isProbability _

theorem charFun_F_selectedResidualLaw (S : Set FPositiveZeroOccurrence)
    (hS : ∀ z∈S, F_pairConj z∈S)
    (hpos : ∀ t : ℝ, 0<t → 0≤(F_selectedHeatTrace S t).re) (u : ℝ) :
    charFun (F_selectedResidualLaw S) u=Complex.exp (heatExponentOf (F_selectedHeatTrace S) u) := by
  have hn : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0), 0≤(F_selectedHeatTrace S t).re := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hpos t ht
  letI := heatSubordinatorLaw_isProbability (integrableOn_F_selectedHeatTrace_re S) hn
  rw [F_selectedResidualLaw, charFun_gaussianVarianceMixture _
    (ae_nonneg_heatSubordinatorLaw (integrableOn_F_selectedHeatTrace_re S) hn),
    nonnegativeLaplace_heatSubordinatorLaw (integrableOn_F_selectedHeatTrace_re S) hn (sq_nonneg u),
    F_selectedHeatExponent_eq_ofReal S hS, Complex.ofReal_exp]

theorem F_selectedResidualLaw_finite_certificate (S : Set FPositiveZeroOccurrence)
    (hS : ∀ z∈S, F_pairConj z∈S) (a : S) {T : ℝ} (hT : 100≤T)
    (hca : 2*(F_pairRoot a.val).re≤T)
    (hreal : ∀ z∈S, (F_pairRoot z).re<T → (F_pairRoot z).im=0) :
    IsProbabilityMeasure (F_selectedResidualLaw S) ∧
      ∀ u : ℝ, charFun (F_selectedResidualLaw S) u=
        Complex.exp (heatExponentOf (F_selectedHeatTrace S) u) := by
  have hp (t : ℝ) (ht : 0<t) : 0≤(F_selectedHeatTrace S t).re := by
    exact (show 0≤(93/100)*Real.exp (-(F_pairRoot a.val).re^2*t) by positivity).trans
      (F_selectedHeatTrace_lower_of_finite_zero_certificate S a hT hca hreal ht)
  exact ⟨F_selectedResidualLaw_isProbability S hp, charFun_F_selectedResidualLaw S hS hp⟩

theorem reciprocalTransform_eq_residual_charFun (s : Finset FPositiveZeroOccurrence)
    (hS : ∀ z∈((s:Set FPositiveZeroOccurrence)ᶜ), F_pairConj z∈((s:Set FPositiveZeroOccurrence)ᶜ))
    (a : ↥((s:Set FPositiveZeroOccurrence)ᶜ)) {T : ℝ} (hT : 100≤T)
    (hca : 2*(F_pairRoot a.val).re≤T)
    (hreal : ∀ z∈((s:Set FPositiveZeroOccurrence)ᶜ),
      (F_pairRoot z).re<T → (F_pairRoot z).im=0) (u : ℝ) :
    reciprocalTransform u*(∏ z∈s, (1+(u:ℂ)^2/(F_pairRoot z)^2))=
      charFun (F_selectedResidualLaw ((s:Set FPositiveZeroOccurrence)ᶜ)) u := by
  rw [reciprocalTransform_delete_finite_heat]
  exact ((F_selectedResidualLaw_finite_certificate _ hS a hT hca hreal).2 u).symm

end ReciprocalXi

