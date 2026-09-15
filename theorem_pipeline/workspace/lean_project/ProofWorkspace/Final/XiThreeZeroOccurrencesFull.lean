import ProofWorkspace.Final.XiPairedProductOrderFull

set_option autoImplicit false
noncomputable section
open Set
namespace ReciprocalXi

theorem F_pairRoot_injective_at_simple (z w : FPositiveZeroOccurrence)
    (hs : analyticOrderNatAt F (F_pairRoot z)=1)
    (he : F_pairRoot z=F_pairRoot w) : z=w := by
  let a : FZero := ⟨F_pairRoot z,F_pairRoot_is_zero z⟩
  let e := F_pairRootFiberEquiv a z.property
  have hfin : e ⟨z,rfl⟩=e ⟨w,he.symm⟩ := by
    apply Fin.ext
    have hz := (e ⟨z,rfl⟩).isLt
    have hw := (e ⟨w,he.symm⟩).isLt
    change (e ⟨z,rfl⟩).val<analyticOrderNatAt F (F_pairRoot z) at hz
    change (e ⟨w,he.symm⟩).val<analyticOrderNatAt F (F_pairRoot z) at hw
    omega
  exact congrArg Subtype.val (e.injective hfin)

theorem F_threeZero_values_to_occurrences
    (a b c z : FPositiveZeroOccurrence)
    (ha : analyticOrderNatAt F (F_pairRoot a)=1)
    (hb : analyticOrderNatAt F (F_pairRoot b)=1)
    (hc : analyticOrderNatAt F (F_pairRoot c)=1)
    (hz : F_pairRoot z=F_pairRoot a ∨ F_pairRoot z=F_pairRoot b ∨
      F_pairRoot z=F_pairRoot c) : z=a ∨ z=b ∨ z=c := by
  rcases hz with hz | hz | hz
  · exact Or.inl (F_pairRoot_injective_at_simple a z ha hz.symm).symm
  · exact Or.inr (Or.inl (F_pairRoot_injective_at_simple b z hb hz.symm).symm)
  · exact Or.inr (Or.inr (F_pairRoot_injective_at_simple c z hc hz.symm).symm)

theorem F_threeZero_other_occurrence_ge_sixty
    (a b c : FPositiveZeroOccurrence)
    (ha : analyticOrderNatAt F (F_pairRoot a)=1)
    (hb : analyticOrderNatAt F (F_pairRoot b)=1)
    (hc : analyticOrderNatAt F (F_pairRoot c)=1)
    (hcomplete : ∀ w : ℂ, F w=0 → 0<w.re → w.re<60 →
      w=F_pairRoot a ∨ w=F_pairRoot b ∨ w=F_pairRoot c)
    (z : FPositiveZeroOccurrence) (hza : z≠a) (hzb : z≠b) (hzc : z≠c) :
    60≤(F_pairRoot z).re := by
  by_contra hz
  have hp : 0<(F_pairRoot z).re := z.property
  have h := F_threeZero_values_to_occurrences a b c z ha hb hc
    (hcomplete (F_pairRoot z) (F_pairRoot_is_zero z) hp (lt_of_not_ge hz))
  rcases h with h | h | h
  · exact hza h
  · exact hzb h
  · exact hzc h

end ReciprocalXi

