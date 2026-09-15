import ProofWorkspace.Final.XiResidualQuotientFull
import ProofWorkspace.Final.TwoLaplaceInversionFull
import ProofWorkspace.Final.AngularConvolutionFull
import ProofWorkspace.Final.XiFourierRealFull
import ProofWorkspace.Final.XiRealDeletionFull

set_option autoImplicit false
noncomputable section
open Set Filter Topology Complex MeasureTheory ProbabilityTheory Measure
namespace ReciprocalXi

theorem reciprocalTransform_twoLaplace_residual
    (z₁ z₂ : FPositiveZeroOccurrence) {a b : ℝ} (ha : 0<a) (hab : a<b)
    (hz₁ : F_pairRoot z₁=(a:ℂ)) (hz₂ : F_pairRoot z₂=(b:ℂ))
    (hS : ∀ z∈(({z₁,z₂}:Finset FPositiveZeroOccurrence):Set FPositiveZeroOccurrence)ᶜ,
      F_pairConj z∈(({z₁,z₂}:Finset FPositiveZeroOccurrence):Set FPositiveZeroOccurrence)ᶜ)
    (hpos : ∀ t : ℝ, 0<t → 0≤(F_selectedHeatTrace
      ((({z₁,z₂}:Finset FPositiveZeroOccurrence):Set FPositiveZeroOccurrence)ᶜ) t).re) (u : ℝ) :
    twoLaplaceMultiplier a b u*charFun (F_selectedResidualLaw
      ((({z₁,z₂}:Finset FPositiveZeroOccurrence):Set FPositiveZeroOccurrence)ᶜ)) u=
        reciprocalTransform u := by
  classical
  have hne : z₁≠z₂ := by
    intro h
    have hh : (a:ℂ)=(b:ℂ) := hz₁.symm.trans ((congrArg F_pairRoot h).trans hz₂)
    exact hab.ne (Complex.ofReal_injective hh)
  rw [charFun_F_selectedResidualLaw _ hS hpos, ← reciprocalTransform_delete_finite_heat]
  have hnot : z₁∉({z₂}:Finset FPositiveZeroOccurrence) := by simpa using hne
  rw [Finset.prod_insert hnot, Finset.prod_singleton, hz₁, hz₂]
  have hcancel : twoLaplaceMultiplier a b u*
      ((1+(u:ℂ)^2/(a:ℂ)^2)*(1+(u:ℂ)^2/(b:ℂ)^2))=1 := by
    have ha0 : (a:ℂ)≠0 := by exact_mod_cast ha.ne'
    have hb0 : (b:ℂ)≠0 := by exact_mod_cast (ha.trans hab).ne'
    have had : (a:ℂ)^2+(u:ℂ)^2≠0 := by
      exact_mod_cast (show (a^2+u^2:ℝ)≠0 by nlinarith [sq_nonneg u])
    have hbd : (b:ℂ)^2+(u:ℂ)^2≠0 := by
      exact_mod_cast (show (b^2+u^2:ℝ)≠0 by nlinarith [sq_nonneg u])
    unfold twoLaplaceMultiplier
    field_simp
  calc
    _ = reciprocalTransform u*(twoLaplaceMultiplier a b u*
        ((1+(u:ℂ)^2/(a:ℂ)^2)*(1+(u:ℂ)^2/(b:ℂ)^2))) := by ring
    _ = _ := by rw [hcancel, mul_one]

theorem density_eq_twoLaplace_convolution
    (z₁ z₂ : FPositiveZeroOccurrence) {a b : ℝ} (ha : 0<a) (hab : a<b)
    (hz₁ : F_pairRoot z₁=(a:ℂ)) (hz₂ : F_pairRoot z₂=(b:ℂ))
    (hS : ∀ z∈(({z₁,z₂}:Finset FPositiveZeroOccurrence):Set FPositiveZeroOccurrence)ᶜ,
      F_pairConj z∈(({z₁,z₂}:Finset FPositiveZeroOccurrence):Set FPositiveZeroOccurrence)ᶜ)
    (hpos : ∀ t : ℝ, 0<t → 0≤(F_selectedHeatTrace
      ((({z₁,z₂}:Finset FPositiveZeroOccurrence):Set FPositiveZeroOccurrence)ᶜ) t).re) (x : ℝ) :
    density x=laplaceConvolutionJet (F_selectedResidualLaw
      ((({z₁,z₂}:Finset FPositiveZeroOccurrence):Set FPositiveZeroOccurrence)ᶜ))
      (a*b/(2*(b^2-a^2))) a b 0 x := by
  classical
  let S : Set FPositiveZeroOccurrence :=
    ((({z₁,z₂}:Finset FPositiveZeroOccurrence):Set FPositiveZeroOccurrence)ᶜ)
  letI := F_selectedResidualLaw_isProbability S hpos
  have hf : (fun u : ℝ ↦ twoLaplaceMultiplier a b u*charFun (F_selectedResidualLaw S) u)=
      reciprocalTransform := funext (reciprocalTransform_twoLaplace_residual z₁ z₂ ha hab hz₁ hz₂ hS hpos)
  have hh := angularInverse_mul_charFun (F_selectedResidualLaw S)
    (twoLaplaceMultiplier a b) (integrable_twoLaplaceMultiplier ha (ha.trans hab)) x
  rw [hf] at hh
  simp_rw [angularInverse_twoLaplaceMultiplier ha hab] at hh
  have hd : angularInverse reciprocalTransform x=(density x:ℂ) :=
    (density_eq_complex_integral x).symm
  rw [hd, integral_complex_ofReal] at hh
  exact Complex.ofReal_injective hh

theorem density_pos_of_two_real_roots
    (z₁ z₂ : FPositiveZeroOccurrence) {a b : ℝ} (ha : 0<a) (hab : a<b)
    (hz₁ : F_pairRoot z₁=(a:ℂ)) (hz₂ : F_pairRoot z₂=(b:ℂ))
    (hS : ∀ z∈(({z₁,z₂}:Finset FPositiveZeroOccurrence):Set FPositiveZeroOccurrence)ᶜ,
      F_pairConj z∈(({z₁,z₂}:Finset FPositiveZeroOccurrence):Set FPositiveZeroOccurrence)ᶜ)
    (hpos : ∀ t : ℝ, 0<t → 0≤(F_selectedHeatTrace
      ((({z₁,z₂}:Finset FPositiveZeroOccurrence):Set FPositiveZeroOccurrence)ᶜ) t).re) (x : ℝ) :
    0<density x := by
  classical
  let S : Set FPositiveZeroOccurrence :=
    ((({z₁,z₂}:Finset FPositiveZeroOccurrence):Set FPositiveZeroOccurrence)ᶜ)
  letI := F_selectedResidualLaw_isProbability S hpos
  rw [density_eq_twoLaplace_convolution z₁ z₂ ha hab hz₁ hz₂ hS hpos x]
  apply laplaceConvolution_pos _ _ _ _ 0 x
    (div_pos (mul_pos ha (ha.trans hab)) (by nlinarith)) ha hab le_rfl
  simpa only [zero_mul, Real.exp_zero] using
    (integrable_const (1:ℝ) (μ:=F_selectedResidualLaw S))

theorem density_pos_of_finite_zero_certificate
    (z₁ z₂ : FPositiveZeroOccurrence) {a b : ℝ} (ha : 0<a) (hab : a<b)
    (hz₁ : F_pairRoot z₁=(a:ℂ)) (hz₂ : F_pairRoot z₂=(b:ℂ))
    (c : ↥((({z₁,z₂}:Finset FPositiveZeroOccurrence):Set FPositiveZeroOccurrence)ᶜ))
    {T : ℝ} (hT : 100≤T) (hc : 2*(F_pairRoot c.val).re≤T)
    (hreal : ∀ z∈((({z₁,z₂}:Finset FPositiveZeroOccurrence):Set FPositiveZeroOccurrence)ᶜ),
      (F_pairRoot z).re<T → (F_pairRoot z).im=0) (x : ℝ) :
    0<density x := by
  classical
  apply density_pos_of_two_real_roots z₁ z₂ ha hab hz₁ hz₂
    (F_pairConj_compl_two_real z₁ z₂ hz₁ hz₂) _ x
  intro t ht
  exact (show 0≤(93/100)*Real.exp (-(F_pairRoot c.val).re^2*t) by positivity).trans
    (F_selectedHeatTrace_lower_of_finite_zero_certificate _ c hT hc hreal ht)

end ReciprocalXi
