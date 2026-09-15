import ProofWorkspace.Final.XiPairedProductFull
import Mathlib.Logic.Equiv.Basic

set_option autoImplicit false
noncomputable section
open Set Metric Filter Topology
namespace ReciprocalXi

def F_pairSubproduct (S : Set FPositiveZeroOccurrence) (w : ℂ) : ℂ :=
  ∏' z : S, (1+F_pairTerm z.val w)

theorem F_pairSubproduct_hasProdUniformlyOn (S : Set FPositiveZeroOccurrence)
    (K : Set ℂ) (hK : IsCompact K) :
    HasProdUniformlyOn (fun z : S ↦ fun w ↦ 1+F_pairTerm z.val w) (F_pairSubproduct S) K := by
  obtain ⟨R,hR⟩ := hK.isBounded.exists_norm_le
  apply ((summable_F_pairRoot_inv_norm_sq.subtype S).mul_left (R^2)).hasProdUniformlyOn_one_add hK
  · filter_upwards with z w hw
    rw [norm_F_pairTerm]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hR w hw) 2) (by positivity)
  · intro z
    unfold F_pairTerm
    fun_prop

theorem differentiable_F_pairSubproduct (S : Set FPositiveZeroOccurrence) :
    Differentiable ℂ (F_pairSubproduct S) := by
  have hh : HasProdLocallyUniformlyOn (fun z : S ↦ fun w ↦ 1+F_pairTerm z.val w)
      (F_pairSubproduct S) univ := by
    apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
    intro K _ hK
    exact F_pairSubproduct_hasProdUniformlyOn S K hK
  rw [← differentiableOn_univ]
  apply hh.differentiableOn _ isOpen_univ
  filter_upwards with s
  apply Differentiable.differentiableOn
  apply Differentiable.fun_finset_prod
  intro z hz
  unfold F_pairTerm
  fun_prop

theorem F_pairedProduct_split (S : Set FPositiveZeroOccurrence) (w : ℂ) :
    F_pairedProduct w = F_pairSubproduct S w * F_pairSubproduct Sᶜ w := by
  have hs : Multipliable (fun z : S ↦ 1+F_pairTerm z.val w) :=
    multipliable_one_add_of_summable ((summable_norm_F_pairTerm w).subtype S)
  have hc : Multipliable (fun z : (Sᶜ : Set FPositiveZeroOccurrence) ↦ 1+F_pairTerm z.val w) :=
    multipliable_one_add_of_summable ((summable_norm_F_pairTerm w).subtype Sᶜ)
  have ht := Multipliable.tprod_mul_tprod_compl (f:=fun z ↦ 1+F_pairTerm z w) (s:=S) hs hc
  exact ht.symm

def F_pairRootFiberEquiv (a : FZero) (ha : 0 < a.val.re) :
    {z : FPositiveZeroOccurrence // F_pairRoot z = a.val} ≃ Fin (analyticOrderNatAt F a.val) :=
  (show {z : FPositiveZeroOccurrence // F_pairRoot z = a.val} ≃
      {z : FZeroOccurrence // z.1 = a} from
    { toFun := fun z ↦ ⟨z.val.val, Subtype.ext z.property⟩
      invFun := fun z ↦ ⟨⟨z.val, by rw [z.property]; exact ha⟩, congrArg Subtype.val z.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }).trans (Equiv.sigmaSubtype a)

theorem F_pairRootFiber_product (a : FZero) (ha : 0 < a.val.re) (w : ℂ) :
    F_pairSubproduct {z | F_pairRoot z = a.val} w =
      (1-(w/a.val)^2)^(analyticOrderNatAt F a.val) := by
  unfold F_pairSubproduct
  calc
    _ = ∏' _ : {z : FPositiveZeroOccurrence // F_pairRoot z = a.val}, (1-(w/a.val)^2) := by
      apply tprod_congr
      intro z
      have hz : F_pairRoot z.val = a.val := z.property
      rw [F_pairTerm, hz, sub_eq_add_neg]
    _ = ∏' _ : Fin (analyticOrderNatAt F a.val), (1-(w/a.val)^2) :=
      (F_pairRootFiberEquiv a ha).tprod_eq (fun _ ↦ _)
    _ = _ := by simp [tprod_fintype]

theorem F_pairComplement_ne_zero (a : FZero) (ha : 0 < a.val.re) :
    F_pairSubproduct {z | F_pairRoot z = a.val}ᶜ a.val ≠ 0 := by
  apply tprod_one_add_ne_zero_of_summable _
    ((summable_norm_F_pairTerm a.val).subtype {z | F_pairRoot z = a.val}ᶜ)
  intro z hz
  rcases (F_pairFactor_zero_iff z.val a.val).mp hz with h | h
  · exact z.property h.symm
  · have ht := congrArg Complex.re h
    have hp := z.val.property
    change 0 < (F_pairRoot z.val).re at hp
    simp only [Complex.neg_re] at ht
    linarith

theorem F_pairPolynomial_order_one (a : ℂ) (ha : a ≠ 0) :
    analyticOrderAt (fun w : ℂ ↦ 1-(w/a)^2) a = 1 := by
  have hd : HasDerivAt (fun w : ℂ ↦ 1-(w/a)^2) (-(2*(a/a)^(2-1)*(1/a))) a :=
    (((hasDerivAt_id a).div_const a).pow 2).const_sub 1
  have hdne : deriv (fun w : ℂ ↦ 1-(w/a)^2) a ≠ 0 := by
    rw [hd.deriv]
    simp [ha]
  have hfa : AnalyticAt ℂ (fun w : ℂ ↦ 1-(w/a)^2) a := by fun_prop
  have ho := hfa.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hdne
  simpa [ha] using ho

theorem F_pairedProduct_order_positive (a : FZero) (ha : 0 < a.val.re) :
    analyticOrderAt F_pairedProduct a.val = analyticOrderAt F a.val := by
  have ha0 : a.val ≠ 0 := by
    intro h
    apply F_zero_ne_zero
    simpa only [h] using a.property
  let S : Set FPositiveZeroOccurrence := {z | F_pairRoot z = a.val}
  have hfun : F_pairedProduct =
      (fun w : ℂ ↦ 1-(w/a.val)^2)^(analyticOrderNatAt F a.val) * F_pairSubproduct Sᶜ := by
    funext w
    rw [F_pairedProduct_split S w, F_pairRootFiber_product a ha w]
    rfl
  have hfa : AnalyticAt ℂ (fun w : ℂ ↦ 1-(w/a.val)^2) a.val := by fun_prop
  have hga : AnalyticAt ℂ (F_pairSubproduct Sᶜ) a.val :=
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr (differentiable_F_pairSubproduct Sᶜ)) _ (mem_univ _)
  have hgn := hga.analyticOrderAt_eq_zero.mpr (F_pairComplement_ne_zero a ha)
  rw [hfun, analyticOrderAt_mul (hfa.pow _) hga, analyticOrderAt_pow hfa,
    F_pairPolynomial_order_one a.val ha0, hgn, add_zero]
  simpa using Nat.cast_analyticOrderNatAt (F_analyticOrderAt_ne_top a.val)

theorem F_pairedProduct_order_neg (w : ℂ) :
    analyticOrderAt F_pairedProduct (-w) = analyticOrderAt F_pairedProduct w := by
  have h := analyticOrderAt_comp_of_deriv_ne_zero (f:=F_pairedProduct) (g:=fun z : ℂ ↦ -z)
    (z₀:=w) (by fun_prop) (by simp)
  have he : (F_pairedProduct ∘ fun z : ℂ ↦ -z) = F_pairedProduct := funext F_pairedProduct_even
  rw [he] at h
  exact h.symm

theorem F_pairedProduct_order_eq (w : ℂ) :
    analyticOrderAt F_pairedProduct w = analyticOrderAt F w := by
  by_cases hw : F w = 0
  · by_cases hr : 0 < w.re
    · exact F_pairedProduct_order_positive ⟨w,hw⟩ hr
    · have hre : w.re ≠ 0 := by
        intro h
        have ht := F_zero_abs_re_gt_one w hw
        norm_num [h] at ht
      have hneg : 0 < (-w).re := by
        simp only [Complex.neg_re]
        exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hr) hre)
      have hfw : F (-w) = 0 := by rw [F_even, hw]
      have h := F_pairedProduct_order_positive ⟨-w,hfw⟩ hneg
      simpa only [F_pairedProduct_order_neg, F_order_neg] using h
  · have hp := F_pairedProduct_ne_zero_of_F_ne_zero w hw
    have hpa := Complex.analyticOnNhd_univ_iff_differentiable.mpr differentiable_F_pairedProduct
    rw [(hpa w (mem_univ _)).analyticOrderAt_eq_zero.mpr hp,
      (analyticOnNhd_F w (mem_univ _)).analyticOrderAt_eq_zero.mpr hw]

end ReciprocalXi

