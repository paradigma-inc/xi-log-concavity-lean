import ProofWorkspace.Final.XiHeatTraceFull

set_option autoImplicit false
noncomputable section
open Set Filter Topology Complex MeasureTheory
open scoped ComplexConjugate
namespace ReciprocalXi

theorem F_pairConj_eq_self_of_real (z : FPositiveZeroOccurrence)
    (hr : (F_pairRoot z).im=0) : F_pairConj z=z := by
  have hc : conj (F_pairRoot z)=F_pairRoot z := Complex.conj_eq_iff_im.mpr hr
  apply Subtype.ext
  apply Sigma.ext
  · exact Subtype.ext hc
  · apply (Fin.heq_ext_iff (by
      change analyticOrderNatAt F (conj (F_pairRoot z)) = analyticOrderNatAt F (F_pairRoot z)
      rw [hc])).mpr
    rfl

theorem F_pairConj_compl_finite_real (s : Finset FPositiveZeroOccurrence)
    (hr : ∀ z∈s, (F_pairRoot z).im=0) :
    ∀ z∈((s:Set FPositiveZeroOccurrence)ᶜ), F_pairConj z∈((s:Set FPositiveZeroOccurrence)ᶜ) := by
  intro z hz hmem
  have hh := F_pairConj_eq_self_of_real (F_pairConj z) (hr _ hmem)
  rw [F_pairConj_involutive z] at hh
  exact hz (hh.symm ▸ hmem)

theorem F_pairConj_compl_two_real (z₁ z₂ : FPositiveZeroOccurrence)
    {a b : ℝ} (h₁ : F_pairRoot z₁=(a:ℂ)) (h₂ : F_pairRoot z₂=(b:ℂ)) :
    ∀ z∈((({z₁,z₂}:Finset FPositiveZeroOccurrence):Set FPositiveZeroOccurrence)ᶜ),
      F_pairConj z∈((({z₁,z₂}:Finset FPositiveZeroOccurrence):Set FPositiveZeroOccurrence)ᶜ) := by
  classical
  apply F_pairConj_compl_finite_real
  intro z hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl
  · rw [h₁, Complex.ofReal_im]
  · rw [h₂, Complex.ofReal_im]

end ReciprocalXi
