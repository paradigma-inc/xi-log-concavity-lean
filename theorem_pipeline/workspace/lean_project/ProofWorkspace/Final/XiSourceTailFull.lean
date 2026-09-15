import ProofWorkspace.Final.XiDensityTailFull
import ProofWorkspace.Final.XiFiniteGapFull
import ProofWorkspace.Final.SourceTailOverlapFull

set_option autoImplicit false
noncomputable section
open Set Filter Topology Complex MeasureTheory ProbabilityTheory Measure
namespace ReciprocalXi

variable (z₁ z₂ : FPositiveZeroOccurrence) {a b : ℝ}
  (hz₁ : F_pairRoot z₁=(a:ℂ)) (hz₂ : F_pairRoot z₂=(b:ℂ))
  (ha0 : 28269/1000≤a) (ha1 : a≤28270/1000)
  (hb0 : 42044/1000≤b) (hb1 : b≤42045/1000)
  (c : ↥((({z₁,z₂}:Finset FPositiveZeroOccurrence):Set FPositiveZeroOccurrence)ᶜ))
  (hc : (F_pairRoot c.val).re≤51)
  (hreal : ∀ z∈((({z₁,z₂}:Finset FPositiveZeroOccurrence):Set FPositiveZeroOccurrence)ᶜ),
    (F_pairRoot z).re<102 → (F_pairRoot z).im=0)
  (hmin : ∀ z∈((({z₁,z₂}:Finset FPositiveZeroOccurrence):Set FPositiveZeroOccurrence)ᶜ),
    (F_pairRoot z).re<102 → 50≤(F_pairRoot z).re)
  (hM : 2*(F 0*((1-(48:ℂ)^2/(a:ℂ)^2)*(1-(48:ℂ)^2/(b:ℂ)^2))/F (48:ℂ)).re≤268341)

include hz₁ hz₂ ha0 ha1 hb0 hb1 c hc hreal hmin hM

theorem density_tail_enclosures_of_finite_source_inputs : Nonempty DensityTailEnclosures := by
  classical
  have ha : 0<a := by linarith
  have hab : a<b := by linarith
  have hpos : ∀ t : ℝ, 0<t → 0≤(F_selectedHeatTrace
      ((({z₁,z₂}:Finset FPositiveZeroOccurrence):Set FPositiveZeroOccurrence)ᶜ) t).re := by
    intro t ht
    exact (show 0≤(93/100)*Real.exp (-(F_pairRoot c.val).re^2*t) by positivity).trans
      (F_selectedHeatTrace_lower_of_finite_zero_certificate _ c (T:=102)
        (by norm_num) (by linarith) hreal ht)
  have hgap : ∀ z∈((({z₁,z₂}:Finset FPositiveZeroOccurrence):Set FPositiveZeroOccurrence)ᶜ),
      (49:ℝ)^2<((F_pairRoot z)^2).re :=
    F_selected_gap_of_finite_zero_certificate _ (c:=50) (R:=49) (T:=102)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hreal hmin
  have hF := F_real_ne_zero_between_deleted_and_remaining z₁ z₂ (r:=48) (L:=49)
    ha hab (by linarith) (by norm_num) hz₁ hz₂ hgap
  have hne : z₁≠z₂ := by
    intro h
    have hh : (a:ℂ)=(b:ℂ) := hz₁.symm.trans ((congrArg F_pairRoot h).trans hz₂)
    exact hab.ne (Complex.ofReal_injective hh)
  have hnot : z₁∉({z₂}:Finset FPositiveZeroOccurrence) := by simpa using hne
  apply density_tail_enclosures_nonempty z₁ z₂ ha hab hz₁ hz₂ hpos
    (R:=48) (L:=49) (M:=268341) (by linarith) (by norm_num) (by norm_num) hgap hF
  · simpa only [Finset.prod_insert hnot, Finset.prod_singleton, hz₁, hz₂] using hM
  · exact source_tail_threshold_le_overlap ha0 ha1 hb0 hb1

theorem density_strictConcaveOn_log_of_finite_source_inputs
    (hcompact : DensityCompactEnclosures) :
    StrictConcaveOn ℝ Set.univ (fun x ↦ Real.log (density x)) := by
  obtain ⟨htail⟩ := density_tail_enclosures_of_finite_source_inputs
    z₁ z₂ hz₁ hz₂ ha0 ha1 hb0 hb1 c hc hreal hmin hM
  apply density_strictConcaveOn_log_of_enclosures hcompact htail
  exact density_pos_of_finite_zero_certificate z₁ z₂ (by linarith) (by linarith)
    hz₁ hz₂ c (T:=102) (by norm_num) (by linarith) hreal

theorem density_pf2_minor_pos_of_finite_source_inputs
    (hcompact : DensityCompactEnclosures)
    (x₁ x₂ y₁ y₂ : ℝ) (hx : x₁<x₂) (hy : y₁<y₂) :
    0<density (x₁-y₁)*density (x₂-y₂)-density (x₁-y₂)*density (x₂-y₁) := by
  obtain ⟨htail⟩ := density_tail_enclosures_of_finite_source_inputs
    z₁ z₂ hz₁ hz₂ ha0 ha1 hb0 hb1 c hc hreal hmin hM
  apply density_pf2_minor_pos_of_enclosures hcompact htail _ x₁ x₂ y₁ y₂ hx hy
  exact density_pos_of_finite_zero_certificate z₁ z₂ (by linarith) (by linarith)
    hz₁ hz₂ c (T:=102) (by norm_num) (by linarith) hreal

end ReciprocalXi
