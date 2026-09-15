import ProofWorkspace.Final.XiHighHeatFull

set_option autoImplicit false
noncomputable section
open Set Filter Topology Complex
namespace ReciprocalXi

def F_selectedHeatTrace (S : Set FPositiveZeroOccurrence) (t : ℝ) : ℂ :=
  ∑' z : S, F_zeroHeatTerm z.val t

theorem F_zeroHeatTerm_re_of_real (z : FPositiveZeroOccurrence) (t : ℝ)
    (hz : (F_pairRoot z).im=0) :
    (F_zeroHeatTerm z t).re = Real.exp (-(F_pairRoot z).re^2*t) := by
  simp [F_zeroHeatTerm, Complex.exp_re, pow_two, hz]

theorem F_selectedHighHeat_lower (S : Set FPositiveZeroOccurrence) {T c t : ℝ}
    (hS : ∀ z∈S, T≤(F_pairRoot z).re) (hT : 100≤T)
    (hc : 0≤c) (hTc : 2*c≤T) (ht : 0<t) :
    -(7/100)*Real.exp (-c^2*t) ≤ (F_selectedHeatTrace S t).re := by
  let e : S → FHighZeroOccurrence T := fun z ↦ ⟨z.val,hS z.val z.property⟩
  have he : Function.Injective e := by
    intro a b hab
    exact Subtype.ext (show a.val=b.val from
      congrArg (fun q : FHighZeroOccurrence T ↦ q.val) hab)
  have hsexp : Summable (fun z : S ↦ Real.exp (-(F_pairRoot z.val).re/2)) := by
    exact ((summable_F_pairRoot_inv_norm_sq.subtype S).div_const 1000).of_nonneg_of_le
      (fun _ ↦ (Real.exp_pos _).le)
      (fun z ↦ F_highZero_exp_le z.val (hT.trans (hS z.val z.property)))
  have hbudget : (∑' z : S, Real.exp (-(F_pairRoot z.val).re/2)) ≤ 7/100 := by
    apply le_trans _ (F_highZero_exp_tsum_le hT)
    exact hsexp.tsum_le_tsum_of_inj e he (fun _ _ ↦ (Real.exp_pos _).le)
      (fun _ ↦ le_rfl) (summable_F_highZero_exp hT)
  have hs : Summable (fun z : S ↦ F_zeroHeatTerm z.val t) :=
    (summable_F_zeroHeatTerm ht).subtype S
  have hsre : Summable (fun z : S ↦ (F_zeroHeatTerm z.val t).re) :=
    (Complex.reCLM.hasSum hs.hasSum).summable
  have hb := hsexp.mul_left (-Real.exp (-c^2*t))
  rw [F_selectedHeatTrace, Complex.re_tsum hs]
  calc
    _ ≤ -Real.exp (-c^2*t)*(∑' z : S, Real.exp (-(F_pairRoot z.val).re/2)) := by
      have h := mul_le_mul_of_nonpos_left hbudget
        (neg_nonpos.mpr (Real.exp_pos (-c^2*t)).le)
      simpa only [neg_mul, mul_neg, mul_comm] using h
    _ = ∑' z : S, -Real.exp (-c^2*t)*Real.exp (-(F_pairRoot z.val).re/2) :=
      tsum_mul_left.symm
    _ ≤ _ := hb.tsum_le_tsum (fun z ↦ high_zero_heat_lower (hT.trans (hS z.val z.property))
      (F_zero_im_bound _ (F_pairRoot_is_zero z.val)).le hc
      (hTc.trans (hS z.val z.property)) ht) hsre

theorem F_selectedRealHeat_lower (S : Set FPositiveZeroOccurrence) (a : S)
    (hS : ∀ z∈S, (F_pairRoot z).im=0) {t : ℝ} (ht : 0<t) :
    Real.exp (-(F_pairRoot a.val).re^2*t) ≤ (F_selectedHeatTrace S t).re := by
  have hs : Summable (fun z : S ↦ F_zeroHeatTerm z.val t) :=
    (summable_F_zeroHeatTerm ht).subtype S
  have hsre : Summable (fun z : S ↦ (F_zeroHeatTerm z.val t).re) :=
    (Complex.reCLM.hasSum hs.hasSum).summable
  rw [F_selectedHeatTrace, Complex.re_tsum hs,
    ← F_zeroHeatTerm_re_of_real a.val t (hS a.val a.property)]
  exact hsre.le_tsum a (fun z _ ↦ by
    rw [F_zeroHeatTerm_re_of_real z.val t (hS z.val z.property)]
    exact (Real.exp_pos _).le)

theorem F_selectedHeatTrace_lower_of_finite_zero_certificate
    (S : Set FPositiveZeroOccurrence) (a : S) {T t : ℝ} (hT : 100≤T)
    (hca : 2*(F_pairRoot a.val).re≤T)
    (hreal : ∀ z∈S, (F_pairRoot z).re<T → (F_pairRoot z).im=0) (ht : 0<t) :
    (93/100)*Real.exp (-(F_pairRoot a.val).re^2*t) ≤ (F_selectedHeatTrace S t).re := by
  classical
  let L : Set FPositiveZeroOccurrence := S ∩ {z | (F_pairRoot z).re<T}
  let H : Set FPositiveZeroOccurrence := S ∩ {z | T≤(F_pairRoot z).re}
  have haL : a.val∈L := ⟨a.property, by
    change (F_pairRoot a.val).re<T
    have hp := F_pairRoot_re_gt_one a.val
    linarith⟩
  have hLo := F_selectedRealHeat_lower L ⟨a.val,haL⟩
    (fun z hz ↦ hreal z hz.1 hz.2) ht
  have hHi := F_selectedHighHeat_lower H (fun _ hz ↦ hz.2) hT
    (F_pairRoot_re_gt_one a.val |>.le.trans' (by norm_num : (0:ℝ)≤1)) hca ht
  have hdis : Disjoint L H := by
    rw [Set.disjoint_left]
    intro z hzL hzH
    exact not_lt_of_ge (show T≤(F_pairRoot z).re from hzH.2)
      (show (F_pairRoot z).re<T from hzL.2)
  have hunion : L ∪ H=S := by
    ext z
    simp only [L,H,Set.mem_union,Set.mem_inter_iff,Set.mem_setOf_eq]
    constructor
    · rintro (h|h) <;> exact h.1
    · intro h
      rcases lt_or_ge (F_pairRoot z).re T with hz|hz
      · exact Or.inl ⟨h,hz⟩
      · exact Or.inr ⟨h,hz⟩
  have hsplit := Summable.tsum_union_disjoint (f:=fun z ↦ F_zeroHeatTerm z t) hdis
    ((summable_F_zeroHeatTerm ht).subtype L) ((summable_F_zeroHeatTerm ht).subtype H)
  rw [hunion] at hsplit
  change F_selectedHeatTrace S t=F_selectedHeatTrace L t+F_selectedHeatTrace H t at hsplit
  rw [hsplit, Complex.add_re]
  change Real.exp (-(F_pairRoot a.val).re^2*t) ≤ (F_selectedHeatTrace L t).re at hLo
  nlinarith

end ReciprocalXi
