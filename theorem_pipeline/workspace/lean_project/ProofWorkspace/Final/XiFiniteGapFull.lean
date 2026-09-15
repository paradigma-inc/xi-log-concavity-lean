import ProofWorkspace.Final.XiRealDeletionFull
import ProofWorkspace.Final.XiSelectedHeatFull

set_option autoImplicit false
noncomputable section
open Set Filter Topology Complex MeasureTheory
namespace ReciprocalXi

theorem F_selected_gap_of_finite_zero_certificate
    (S : Set FPositiveZeroOccurrence) {c R T : ℝ}
    (hR : 0≤R) (hc : R<c) (hT : 0≤T) (hTR : R^2+1≤T^2)
    (hreal : ∀ z∈S, (F_pairRoot z).re<T → (F_pairRoot z).im=0)
    (hmin : ∀ z∈S, (F_pairRoot z).re<T → c≤(F_pairRoot z).re) :
    ∀ z∈S, R^2<((F_pairRoot z)^2).re := by
  intro z hz
  by_cases hlo : (F_pairRoot z).re<T
  · have hr := hmin z hz hlo
    have hi := hreal z hz hlo
    simp only [pow_two, Complex.mul_re, hi, mul_zero, sub_zero]
    nlinarith
  · have hr := le_of_not_gt hlo
    have hi : (F_pairRoot z).im^2<1 :=
      (sq_lt_one_iff_abs_lt_one _).mpr (F_zero_im_bound _ (F_pairRoot_is_zero z))
    simp only [pow_two, Complex.mul_re]
    nlinarith

theorem F_real_ne_zero_of_deleted_gap (s : Finset FPositiveZeroOccurrence)
    {r : ℝ} (hr : 0<r)
    (havoid : ∀ z∈s, F_pairRoot z≠(r:ℂ))
    (hgap : ∀ z∈((s:Set FPositiveZeroOccurrence)ᶜ), r^2<((F_pairRoot z)^2).re) :
    F (r:ℂ)≠0 := by
  intro hf
  let z : FPositiveZeroOccurrence :=
    ⟨⟨⟨(r:ℂ),hf⟩, ⟨0,F_zero_order_pos (r:ℂ) hf⟩⟩, hr⟩
  have hz : z∈((s:Set FPositiveZeroOccurrence)ᶜ) := by
    intro hmem
    exact havoid z hmem rfl
  have hh := hgap z hz
  change r^2<(((r:ℂ)^2).re) at hh
  norm_cast at hh
  exact lt_irrefl _ hh

theorem F_real_ne_zero_between_deleted_and_remaining
    (z₁ z₂ : FPositiveZeroOccurrence) {a b r L : ℝ}
    (ha : 0<a) (hab : a<b) (hbr : b<r) (hrL : r≤L)
    (hz₁ : F_pairRoot z₁=(a:ℂ)) (hz₂ : F_pairRoot z₂=(b:ℂ))
    (hgap : ∀ z∈((({z₁,z₂}:Finset FPositiveZeroOccurrence):Set FPositiveZeroOccurrence)ᶜ),
      L^2<((F_pairRoot z)^2).re) : F (r:ℂ)≠0 := by
  classical
  have hr : 0<r := (ha.trans hab).trans hbr
  apply F_real_ne_zero_of_deleted_gap ({z₁,z₂}:Finset FPositiveZeroOccurrence) hr
  · intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · rw [hz₁]; exact_mod_cast (hab.trans hbr).ne
    · rw [hz₂]; exact_mod_cast hbr.ne
  · intro z hz
    have hh := hgap z hz
    nlinarith

end ReciprocalXi
