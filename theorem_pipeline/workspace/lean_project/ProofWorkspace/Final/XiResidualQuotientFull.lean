import ProofWorkspace.Final.XiResidualMomentFull
import ProofWorkspace.Final.ExponentialAnalyticIdentityFull

set_option autoImplicit false
noncomputable section
open Set Filter Topology Complex MeasureTheory ProbabilityTheory Measure
open scoped ENNReal NNReal
namespace ReciprocalXi

theorem F_selectedResidualLaw_complexMGF_mul (s : Finset FPositiveZeroOccurrence)
    (hS : ∀ z∈((s:Set FPositiveZeroOccurrence)ᶜ), F_pairConj z∈((s:Set FPositiveZeroOccurrence)ᶜ))
    (hpos : ∀ t : ℝ, 0<t → 0≤(F_selectedHeatTrace ((s:Set FPositiveZeroOccurrence)ᶜ) t).re)
    {R : ℝ} (hR : 0<R)
    (hgap : ∀ z∈((s:Set FPositiveZeroOccurrence)ᶜ), R^2<((F_pairRoot z)^2).re)
    {w : ℂ} (hw : |w.re|<R) :
    complexMGF id (F_selectedResidualLaw ((s:Set FPositiveZeroOccurrence)ᶜ)) w*F w=
      F 0*(∏ z∈s, (1-w^2/(F_pairRoot z)^2)) := by
  let S : Set FPositiveZeroOccurrence := (s:Set FPositiveZeroOccurrence)ᶜ
  have hM := (F_selectedResidualLaw_absoluteMoment S hpos R hgap).1
  apply complexMGF_identity_from_imaginary (F_selectedResidualLaw S) hR hM F
    (fun w : ℂ ↦ F 0*(∏ z∈s, (1-w^2/(F_pairRoot z)^2))) differentiable_F_complex
    (by fun_prop) _ hw
  intro u
  rw [complexMGF_id_mul_I, charFun_F_selectedResidualLaw S hS hpos,
    ← reciprocalTransform_delete_finite_heat s u]
  have hf := F_imaginary_axis_ne_zero u
  have he : ∏ z∈s, (1-((u:ℂ)*I)^2/(F_pairRoot z)^2)=
      ∏ z∈s, (1+(u:ℂ)^2/(F_pairRoot z)^2) := by
    apply Finset.prod_congr rfl
    intro z hz
    rw [mul_pow, I_sq]
    ring
  dsimp only
  rw [he, mul_comm (u:ℂ) I, reciprocalTransform]
  field_simp

theorem F_selectedResidualLaw_moment_quotient (s : Finset FPositiveZeroOccurrence)
    (hS : ∀ z∈((s:Set FPositiveZeroOccurrence)ᶜ), F_pairConj z∈((s:Set FPositiveZeroOccurrence)ᶜ))
    (hpos : ∀ t : ℝ, 0<t → 0≤(F_selectedHeatTrace ((s:Set FPositiveZeroOccurrence)ᶜ) t).re)
    {R r : ℝ} (hR : 0<R)
    (hgap : ∀ z∈((s:Set FPositiveZeroOccurrence)ᶜ), R^2<((F_pairRoot z)^2).re)
    (hr : |r|<R) (hF : F (r:ℂ)≠0) :
    exponentialMoment (F_selectedResidualLaw ((s:Set FPositiveZeroOccurrence)ᶜ)) r=
      (F 0*(∏ z∈s, (1-(r:ℂ)^2/(F_pairRoot z)^2))/F (r:ℂ)).re := by
  have hh := F_selectedResidualLaw_complexMGF_mul s hS hpos hR hgap (w:=(r:ℂ)) hr
  rw [complexMGF_ofReal] at hh
  have hh' := congrArg Complex.re ((eq_div_iff hF).mpr hh)
  exact hh'

theorem F_selectedResidualLaw_absoluteMoment_quotient (s : Finset FPositiveZeroOccurrence)
    (hS : ∀ z∈((s:Set FPositiveZeroOccurrence)ᶜ), F_pairConj z∈((s:Set FPositiveZeroOccurrence)ᶜ))
    (hpos : ∀ t : ℝ, 0<t → 0≤(F_selectedHeatTrace ((s:Set FPositiveZeroOccurrence)ᶜ) t).re)
    {R r : ℝ} (hR : 0<R)
    (hgap : ∀ z∈((s:Set FPositiveZeroOccurrence)ᶜ), R^2<((F_pairRoot z)^2).re)
    (hr : |r|<R) (hF : F (r:ℂ)≠0) :
    Integrable (fun y : ℝ ↦ Real.exp (r*|y|))
      (F_selectedResidualLaw ((s:Set FPositiveZeroOccurrence)ᶜ)) ∧
    (∫ y : ℝ, Real.exp (r*|y|) ∂F_selectedResidualLaw ((s:Set FPositiveZeroOccurrence)ᶜ))≤
      2*(F 0*(∏ z∈s, (1-(r:ℂ)^2/(F_pairRoot z)^2))/F (r:ℂ)).re := by
  have hsq : r^2<R^2 := by nlinarith [sq_abs r, abs_nonneg r]
  have hgap' : ∀ z∈((s:Set FPositiveZeroOccurrence)ᶜ), r^2<((F_pairRoot z)^2).re :=
    fun z hz ↦ hsq.trans (hgap z hz)
  have hh := F_selectedResidualLaw_absoluteMoment _ hpos r hgap'
  have hm := (F_selectedResidualLaw_exponentialMoment _ hpos r hgap').2
  rw [← hm, F_selectedResidualLaw_moment_quotient s hS hpos hR hgap hr hF] at hh
  exact hh

end ReciprocalXi
