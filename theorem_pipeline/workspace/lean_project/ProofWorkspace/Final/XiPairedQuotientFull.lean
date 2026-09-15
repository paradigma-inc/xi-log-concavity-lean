import ProofWorkspace.Final.XiPairedProductOrderFull
import Mathlib.Analysis.Meromorphic.NormalForm

set_option autoImplicit false
noncomputable section
open Set Filter Topology
namespace ReciprocalXi

theorem analyticOnNhd_F_pairedProduct : AnalyticOnNhd ℂ F_pairedProduct univ :=
  Complex.analyticOnNhd_univ_iff_differentiable.mpr differentiable_F_pairedProduct

theorem meromorphicOn_F_div_pairedProduct : MeromorphicOn (F/F_pairedProduct) univ :=
  analyticOnNhd_F.meromorphicOn.div analyticOnNhd_F_pairedProduct.meromorphicOn

theorem F_div_pairedProduct_order_zero (w : ℂ) :
    meromorphicOrderAt (F/F_pairedProduct) w = 0 := by
  have hf := analyticOnNhd_F w (mem_univ _)
  have hp := analyticOnNhd_F_pairedProduct w (mem_univ _)
  change meromorphicOrderAt (F*F_pairedProduct⁻¹) w = 0
  rw [meromorphicOrderAt_mul hf.meromorphicAt hp.meromorphicAt.inv,
    meromorphicOrderAt_inv, hf.meromorphicOrderAt_eq, hp.meromorphicOrderAt_eq,
    F_pairedProduct_order_eq, ← Nat.cast_analyticOrderNatAt (F_analyticOrderAt_ne_top w)]
  simp

def F_pairQuotient : ℂ → ℂ := toMeromorphicNFOn (F/F_pairedProduct) univ

theorem F_pairQuotient_order_zero (w : ℂ) : meromorphicOrderAt F_pairQuotient w = 0 := by
  rw [F_pairQuotient,
    meromorphicOrderAt_toMeromorphicNFOn meromorphicOn_F_div_pairedProduct (mem_univ _)]
  exact F_div_pairedProduct_order_zero w

theorem analyticOnNhd_F_pairQuotient : AnalyticOnNhd ℂ F_pairQuotient univ := by
  intro w hw
  have hnf := meromorphicNFOn_toMeromorphicNFOn (F/F_pairedProduct) univ hw
  apply hnf.meromorphicOrderAt_nonneg_iff_analyticAt.mp
  change 0 ≤ meromorphicOrderAt F_pairQuotient w
  rw [F_pairQuotient_order_zero]

theorem F_pairQuotient_ne_zero (w : ℂ) : F_pairQuotient w ≠ 0 := by
  have hnf := meromorphicNFOn_toMeromorphicNFOn (F/F_pairedProduct) univ (mem_univ w)
  exact hnf.meromorphicOrderAt_eq_zero_iff.mp (F_pairQuotient_order_zero w)

theorem F_pairQuotient_eq_div (w : ℂ) (hw : F_pairedProduct w ≠ 0) :
    F_pairQuotient w = F w/F_pairedProduct w := by
  have ha := (analyticOnNhd_F w (mem_univ _)).div
    (analyticOnNhd_F_pairedProduct w (mem_univ _)) hw
  rw [F_pairQuotient,
    toMeromorphicNFOn_eq_toMeromorphicNFAt meromorphicOn_F_div_pairedProduct (mem_univ _),
    toMeromorphicNFAt_eq_self.mpr ha.meromorphicNFAt]
  rfl

theorem F_pairQuotient_mul_product (w : ℂ) : F_pairQuotient w*F_pairedProduct w = F w := by
  by_cases hw : F_pairedProduct w = 0
  · simp [hw, (F_pairedProduct_zero_iff w).mp hw]
  · rw [F_pairQuotient_eq_div w hw, div_mul_cancel₀ _ hw]

theorem F_pairQuotient_zero : F_pairQuotient 0 = F 0 := by
  have h := F_pairQuotient_mul_product 0
  simpa only [F_pairedProduct_zero, mul_one] using h

theorem differentiable_F_pairQuotient : Differentiable ℂ F_pairQuotient :=
  Complex.analyticOnNhd_univ_iff_differentiable.mp analyticOnNhd_F_pairQuotient

theorem F_pairQuotient_even (w : ℂ) : F_pairQuotient (-w) = F_pairQuotient w := by
  have hg : AnalyticOnNhd ℂ (fun z : ℂ ↦ F_pairQuotient (-z)) univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr
      (differentiable_F_pairQuotient.comp differentiable_neg)
  have hp0 : F_pairedProduct 0 ≠ 0 := by rw [F_pairedProduct_zero]; exact one_ne_zero
  have he : F_pairQuotient =ᶠ[𝓝 (0:ℂ)] (fun z : ℂ ↦ F_pairQuotient (-z)) := by
    filter_upwards [differentiable_F_pairedProduct.continuous.continuousAt.eventually_ne hp0] with z hz
    have hzn : F_pairedProduct (-z) ≠ 0 := by rwa [F_pairedProduct_even]
    rw [F_pairQuotient_eq_div z hz, F_pairQuotient_eq_div (-z) hzn,
      F_even, F_pairedProduct_even]
  exact (congrFun (analyticOnNhd_F_pairQuotient.eq_of_eventuallyEq hg he) w).symm

end ReciprocalXi

