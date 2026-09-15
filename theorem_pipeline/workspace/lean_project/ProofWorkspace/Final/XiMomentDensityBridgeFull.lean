import ProofWorkspace.Final.XiMomentRootCertificateFull
import ProofWorkspace.Final.XiModerateHeatFull
import ProofWorkspace.Final.XiSourceTailFull
import ProofWorkspace.Final.XiThetaCertifiedQuadratureFull

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 6000000
noncomputable section
open Set
namespace ReciprocalXi

theorem ThreeLowZeroCertificate.value_pos (C : ThreeLowZeroCertificate) (j : Fin 3) :
    0<C.value j := (originalLowRootLower_pos j).trans (C.lower j)

theorem ThreeLowZeroCertificate.value_zero_bounds (C : ThreeLowZeroCertificate) :
    2826945028346/(10:ℝ)^11≤C.value 0 ∧ C.value 0≤28270/1000 := by
  have hL := C.lower 0
  have hU := C.upper 0
  norm_num [originalLowRootLower,originalLowRootUpper,momentRootUpperEndpoints] at hL hU
  constructor <;> linarith

theorem ThreeLowZeroCertificate.value_one_bounds (C : ThreeLowZeroCertificate) :
    4204407927754/(10:ℝ)^11≤C.value 1 ∧ C.value 1≤42045/1000 := by
  have hL := C.lower 1
  have hU := C.upper 1
  norm_num [originalLowRootLower,originalLowRootUpper,momentRootUpperEndpoints] at hL hU
  constructor <;> linarith

theorem ThreeLowZeroCertificate.value_two_bounds (C : ThreeLowZeroCertificate) :
    50≤C.value 2 ∧ C.value 2≤51 := by
  have hL := C.lower 2
  have hU := C.upper 2
  norm_num [originalLowRootLower,originalLowRootUpper,momentRootUpperEndpoints] at hL hU
  constructor <;> linarith

def ThreeLowZeroCertificate.residualSet (C : ThreeLowZeroCertificate) :
    Set FPositiveZeroOccurrence :=
  ((({C.occurrence 0,C.occurrence 1}:Finset FPositiveZeroOccurrence):
    Set FPositiveZeroOccurrence)ᶜ)

theorem ThreeLowZeroCertificate.mem_residualSet (C : ThreeLowZeroCertificate)
    (z : FPositiveZeroOccurrence) :
    z∈C.residualSet ↔ z≠C.occurrence 0 ∧ z≠C.occurrence 1 := by
  classical
  simp [ThreeLowZeroCertificate.residualSet]

theorem ThreeLowZeroCertificate.third_mem_residualSet (C : ThreeLowZeroCertificate) :
    C.occurrence 2∈C.residualSet := by
  rw [C.mem_residualSet]
  exact ⟨C.occurrence_injective.ne (by decide),C.occurrence_injective.ne (by decide)⟩

theorem ThreeLowZeroCertificate.residual_other_gap (C : ThreeLowZeroCertificate)
    (z : FPositiveZeroOccurrence) (hz : z∈C.residualSet) (hz2 : z≠C.occurrence 2) :
    60<(F_pairRoot z).re := by
  obtain ⟨h0,h1⟩ := (C.mem_residualSet z).mp hz
  apply C.other_gap z
  intro j
  fin_cases j
  · exact h0
  · exact h1
  · exact hz2

theorem ThreeLowZeroCertificate.residual_heat_nonneg (C : ThreeLowZeroCertificate)
    (t : ℝ) (ht : 0<t) : 0≤(F_selectedHeatTrace C.residualSet t).re := by
  have h := F_selectedHeatTrace_lower_of_three_zero_certificate C.residualSet
    ⟨C.occurrence 2,C.third_mem_residualSet⟩
    (by rw [C.root_eq,Complex.ofReal_im])
    (by simpa only [C.root_eq,Complex.ofReal_re] using C.value_two_bounds.2)
    (fun z hz hz2 ↦ (C.residual_other_gap z hz hz2).le) ht
  exact (show 0≤(1/36:ℝ)*Real.exp (-(F_pairRoot (C.occurrence 2)).re^2*t)
    by positivity).trans h

theorem ThreeLowZeroCertificate.residual_square_gap (C : ThreeLowZeroCertificate)
    (z : FPositiveZeroOccurrence) (hz : z∈C.residualSet) :
    (49:ℝ)^2<((F_pairRoot z)^2).re := by
  by_cases he : z=C.occurrence 2
  · rw [he,C.root_eq,←Complex.ofReal_pow,Complex.ofReal_re]
    nlinarith [C.value_two_bounds.1]
  · have hr := C.residual_other_gap z hz he
    have hi : (F_pairRoot z).im^2<1 :=
      (sq_lt_one_iff_abs_lt_one _).mpr (F_zero_im_bound _ (F_pairRoot_is_zero z))
    simp only [pow_two,Complex.mul_re]
    nlinarith

theorem density_pos_of_threeLowZeroCertificate (C : ThreeLowZeroCertificate) (x : ℝ) :
    0<density x := by
  exact density_pos_of_two_real_roots (C.occurrence 0) (C.occurrence 1)
    (C.value_pos 0) (C.value_strictMono (by decide)) (C.root_eq 0) (C.root_eq 1)
    (F_pairConj_compl_two_real _ _ (C.root_eq 0) (C.root_eq 1))
    C.residual_heat_nonneg x

theorem density_tail_enclosures_of_threeLowZeroCertificate (C : ThreeLowZeroCertificate) :
    Nonempty DensityTailEnclosures := by
  classical
  have ha := C.value_pos 0
  have hab : C.value 0<C.value 1 := C.value_strictMono (by decide)
  have ha0 : 28269/1000≤C.value 0 := by linarith [C.value_zero_bounds.1]
  have ha1 := C.value_zero_bounds.2
  have hb0 : 42044/1000≤C.value 1 := by linarith [C.value_one_bounds.1]
  have hb1 := C.value_one_bounds.2
  have hF : F (48:ℂ)≠0 := by
    intro hh
    have h := F48_source_lower
    rw [hh,Complex.zero_re] at h
    norm_num at h
  have hM := source_moment_cap_of_F48_lower C.value_zero_bounds.1
    C.value_one_bounds.1 (by linarith) (by linarith) F48_source_lower
  have hnot : C.occurrence 0∉({C.occurrence 1}:Finset FPositiveZeroOccurrence) := by
    simpa using C.occurrence_injective.ne (show (0:Fin 3)≠1 by decide)
  apply density_tail_enclosures_nonempty (C.occurrence 0) (C.occurrence 1)
    ha hab (C.root_eq 0) (C.root_eq 1) C.residual_heat_nonneg
    (R:=48) (L:=49) (M:=268341) (by linarith) (by norm_num) (by norm_num)
    C.residual_square_gap hF
  · simpa only [Finset.prod_insert hnot,Finset.prod_singleton,C.root_eq] using hM
  · exact source_tail_threshold_le_overlap ha0 ha1 hb0 hb1

theorem density_curvature_positive_of_threeLowZeroCertificate
    (C : ThreeLowZeroCertificate) (hcompact : DensityCompactEnclosures) :
    ∀ x : ℝ, 0<curvatureJet (density x) (deriv density x) (deriv (deriv density) x) := by
  obtain ⟨htail⟩ := density_tail_enclosures_of_threeLowZeroCertificate C
  exact density_curvature_positive_of_enclosures hcompact htail

theorem density_strictConcaveOn_log_of_threeLowZeroCertificate
    (C : ThreeLowZeroCertificate) (hcompact : DensityCompactEnclosures) :
    StrictConcaveOn ℝ Set.univ (fun x ↦ Real.log (density x)) := by
  obtain ⟨htail⟩ := density_tail_enclosures_of_threeLowZeroCertificate C
  exact density_strictConcaveOn_log_of_enclosures hcompact htail
    (density_pos_of_threeLowZeroCertificate C)

theorem density_pf2_minor_pos_of_threeLowZeroCertificate
    (C : ThreeLowZeroCertificate) (hcompact : DensityCompactEnclosures)
    (x₁ x₂ y₁ y₂ : ℝ) (hx : x₁<x₂) (hy : y₁<y₂) :
    0<density (x₁-y₁)*density (x₂-y₂)-density (x₁-y₂)*density (x₂-y₁) := by
  obtain ⟨htail⟩ := density_tail_enclosures_of_threeLowZeroCertificate C
  exact density_pf2_minor_pos_of_enclosures hcompact htail
    (density_pos_of_threeLowZeroCertificate C) x₁ x₂ y₁ y₂ hx hy

/-- The final mathematical assembly, still conditional on the six actual endpoint signs
    and the full actual compact enclosure. Neither prerequisite is asserted here. -/
theorem density_global_conclusions_of_original_signs_and_compact
    (hs : ∀ j : Fin 3, (F (originalLowRootLower j:ℂ)).re*
      (F (originalLowRootUpper j:ℂ)).re<0)
    (hcompact : DensityCompactEnclosures) :
    (∀ x : ℝ, 0<density x ∧
      0<curvatureJet (density x) (deriv density x) (deriv (deriv density) x)) ∧
    StrictConcaveOn ℝ Set.univ (fun x ↦ Real.log (density x)) ∧
    (∀ x₁ x₂ y₁ y₂ : ℝ, x₁<x₂ → y₁<y₂ →
      0<density (x₁-y₁)*density (x₂-y₂)-density (x₁-y₂)*density (x₂-y₁)) := by
  obtain ⟨C⟩ := threeLowZeroCertificate_of_signs hs
  exact ⟨fun x ↦ ⟨density_pos_of_threeLowZeroCertificate C x,
    density_curvature_positive_of_threeLowZeroCertificate C hcompact x⟩,
    density_strictConcaveOn_log_of_threeLowZeroCertificate C hcompact,
    density_pf2_minor_pos_of_threeLowZeroCertificate C hcompact⟩

end ReciprocalXi
