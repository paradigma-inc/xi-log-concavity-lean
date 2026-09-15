import ProofWorkspace.Final.XiZeroSummabilityFull
import ProofWorkspace.Final.XiZeroSymmetryFull
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Complex.LocallyUniformLimit

set_option autoImplicit false
noncomputable section
open Set Metric Filter Topology
namespace ReciprocalXi

abbrev FZeroOccurrence := Σ z : FZero, Fin (analyticOrderNatAt F z.val)

theorem summable_F_zeroOccurrence_inv_norm_sq :
    Summable (fun z : FZeroOccurrence ↦ (‖z.1.val‖^2)⁻¹) := by
  apply (summable_sigma_of_nonneg (fun _ ↦ by positivity)).mpr
  constructor
  · intro z
    exact summable_of_finite_support (Set.toFinite _)
  · simpa only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, div_eq_mul_inv] using summable_F_zero_order_div_norm_sq

abbrev FPositiveZeroOccurrence := {z : FZeroOccurrence // 0 < z.1.val.re}

def F_pairRoot (z : FPositiveZeroOccurrence) : ℂ := z.val.1.val

theorem F_pairRoot_is_zero (z : FPositiveZeroOccurrence) : F (F_pairRoot z) = 0 :=
  z.val.1.property

theorem F_pairRoot_ne_zero (z : FPositiveZeroOccurrence) : F_pairRoot z ≠ 0 := by
  intro h
  exact F_zero_ne_zero (h ▸ F_pairRoot_is_zero z)

theorem summable_F_pairRoot_inv_norm_sq :
    Summable (fun z : FPositiveZeroOccurrence ↦ (‖F_pairRoot z‖^2)⁻¹) :=
  summable_F_zeroOccurrence_inv_norm_sq.subtype _

def F_pairTerm (z : FPositiveZeroOccurrence) (w : ℂ) : ℂ := -(w/F_pairRoot z)^2

theorem norm_F_pairTerm (z : FPositiveZeroOccurrence) (w : ℂ) :
    ‖F_pairTerm z w‖ = ‖w‖^2*(‖F_pairRoot z‖^2)⁻¹ := by
  rw [F_pairTerm, norm_neg, norm_pow, norm_div, div_pow, div_eq_mul_inv]

theorem summable_norm_F_pairTerm (w : ℂ) :
    Summable (fun z : FPositiveZeroOccurrence ↦ ‖F_pairTerm z w‖) := by
  simpa only [norm_F_pairTerm] using summable_F_pairRoot_inv_norm_sq.mul_left (‖w‖^2)

def F_pairedProduct (w : ℂ) : ℂ := ∏' z : FPositiveZeroOccurrence, (1+F_pairTerm z w)

theorem multipliable_F_pairFactors (w : ℂ) :
    Multipliable (fun z : FPositiveZeroOccurrence ↦ 1+F_pairTerm z w) :=
  multipliable_one_add_of_summable (summable_norm_F_pairTerm w)

theorem F_pairedProduct_hasProdUniformlyOn (K : Set ℂ) (hK : IsCompact K) :
    HasProdUniformlyOn (fun z w ↦ 1+F_pairTerm z w) F_pairedProduct K := by
  obtain ⟨R,hR⟩ := hK.isBounded.exists_norm_le
  apply (summable_F_pairRoot_inv_norm_sq.mul_left (R^2)).hasProdUniformlyOn_one_add hK
  · filter_upwards with z w hw
    rw [norm_F_pairTerm]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hR w hw) 2) (by positivity)
  · intro z
    unfold F_pairTerm
    fun_prop

theorem F_pairedProduct_hasProdLocallyUniformlyOn :
    HasProdLocallyUniformlyOn (fun z w ↦ 1+F_pairTerm z w) F_pairedProduct univ := by
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _ hK
  exact F_pairedProduct_hasProdUniformlyOn K hK

theorem differentiable_F_pairedProduct : Differentiable ℂ F_pairedProduct := by
  rw [← differentiableOn_univ]
  apply F_pairedProduct_hasProdLocallyUniformlyOn.differentiableOn _ isOpen_univ
  filter_upwards with s
  apply Differentiable.differentiableOn
  apply Differentiable.fun_finset_prod
  intro z hz
  unfold F_pairTerm
  fun_prop

theorem F_pairedProduct_zero : F_pairedProduct 0 = 1 := by
  simp [F_pairedProduct, F_pairTerm]

theorem F_pairedProduct_even (w : ℂ) : F_pairedProduct (-w) = F_pairedProduct w := by
  apply tprod_congr
  intro z
  simp [F_pairTerm, neg_div]

theorem F_pairFactor_zero_iff (z : FPositiveZeroOccurrence) (w : ℂ) :
    1+F_pairTerm z w = 0 ↔ w = F_pairRoot z ∨ w = -F_pairRoot z := by
  rw [F_pairTerm, ← sub_eq_add_neg, sub_eq_zero, eq_comm, div_pow,
    div_eq_one_iff_eq (pow_ne_zero 2 (F_pairRoot_ne_zero z)), sq_eq_sq_iff_eq_or_eq_neg]

theorem F_pairedProduct_ne_zero_of_F_ne_zero (w : ℂ) (hw : F w ≠ 0) :
    F_pairedProduct w ≠ 0 := by
  apply tprod_one_add_ne_zero_of_summable _ (summable_norm_F_pairTerm w)
  intro z hz
  rcases (F_pairFactor_zero_iff z w).mp hz with h | h
  · exact hw (h ▸ F_pairRoot_is_zero z)
  · rw [h, F_even] at hw
    exact hw (F_pairRoot_is_zero z)

theorem F_pairedProduct_eq_zero_of_F_eq_zero (w : ℂ) (hw : F w = 0) :
    F_pairedProduct w = 0 := by
  apply tprod_of_exists_eq_zero
  by_cases hr : 0 < w.re
  · let z : FPositiveZeroOccurrence :=
      ⟨⟨⟨w,hw⟩, ⟨0,F_zero_order_pos w hw⟩⟩, hr⟩
    exact ⟨z,(F_pairFactor_zero_iff z w).mpr (Or.inl rfl)⟩
  · have hre : w.re ≠ 0 := by
      intro h
      have ht := F_zero_abs_re_gt_one w hw
      norm_num [h] at ht
    have hneg : 0 < (-w).re := by
      simp only [Complex.neg_re]
      exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hr) hre)
    have hfw : F (-w) = 0 := by rw [F_even, hw]
    let z : FPositiveZeroOccurrence :=
      ⟨⟨⟨-w,hfw⟩, ⟨0,F_zero_order_pos (-w) hfw⟩⟩, hneg⟩
    exact ⟨z,(F_pairFactor_zero_iff z w).mpr (Or.inr (by simp [F_pairRoot,z]))⟩

theorem F_pairedProduct_zero_iff (w : ℂ) : F_pairedProduct w = 0 ↔ F w = 0 := by
  constructor
  · intro h
    by_contra hn
    exact F_pairedProduct_ne_zero_of_F_ne_zero w hn h
  · exact F_pairedProduct_eq_zero_of_F_eq_zero w

end ReciprocalXi

