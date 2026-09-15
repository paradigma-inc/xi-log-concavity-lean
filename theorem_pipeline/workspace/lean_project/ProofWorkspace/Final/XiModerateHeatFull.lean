import ProofWorkspace.Final.XiSelectedHeatFull

set_option autoImplicit false
noncomputable section
open Set Filter Topology Complex
namespace ReciprocalXi

theorem exp_499_over_40_lower : (259272:ℝ)≤Real.exp (499/40) := by
  have hq : (259272:ℚ)≤∑ n ∈ Finset.range 32, (499/40:ℚ)^n/n.factorial := by
    decide +kernel
  have hr : (259272:ℝ)≤∑ n ∈ Finset.range 32, (499/40:ℝ)^n/n.factorial := by
    have hr' : ((259272:ℚ):ℝ)≤
        ((∑ n ∈ Finset.range 32, (499/40:ℚ)^n/n.factorial:ℚ):ℝ) := Rat.cast_le.mpr hq
    push_cast at hr'
    exact hr'
  exact hr.trans (Real.sum_le_exp_of_nonneg (by norm_num) 32)

theorem exponential_dominates_moderate_zero_weight {A : ℝ} (hA : 60≤A) :
    72*(A^2+1)≤Real.exp ((499/2400)*A) := by
  have hA2 : (3600:ℝ)≤A^2 := by nlinarith
  have hd : 0≤A-60 := by linarith
  have hquad := Real.quadratic_le_exp_of_nonneg
    (show 0≤(499/2400)*(A-60) by positivity)
  have hs : (A/60)^2≤Real.exp ((499/2400)*(A-60)) := by
    apply le_trans _ hquad
    nlinarith [sq_nonneg (A-60)]
  have he := mul_le_mul exp_499_over_40_lower hs (sq_nonneg (A/60))
    (Real.exp_pos (499/40)).le
  have heq : (499/2400)*A=499/40+(499/2400)*(A-60) := by ring
  rw [heq,Real.exp_add]
  exact le_trans (by nlinarith [hA2]) he

theorem moderate_zero_heat_lower {a : ℂ} {c t : ℝ} (ha : 60≤a.re)
    (hi : |a.im|≤1) (hc : 0≤c) (hc1 : c≤51) (ht : 0<t) :
    -Real.exp (-c^2*t)*Real.exp (-((499/2400)*a.re))≤
      (Complex.exp (-a^2*(t:ℂ))).re := by
  by_cases hn : 0≤(Complex.exp (-a^2*(t:ℂ))).re
  · exact (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Real.exp_pos _).le)
      (Real.exp_pos _).le).trans hn
  have hneg : (Complex.exp (-a^2*(t:ℂ))).re<0 := lt_of_not_ge hn
  have hcos : Real.cos ((-a^2*(t:ℂ)).im)<0 := by
    rw [Complex.exp_re] at hneg
    by_contra h
    exact not_lt_of_ge (mul_nonneg (Real.exp_pos _).le (le_of_not_gt h)) hneg
  have hang : Real.pi/2 < |(-a^2*(t:ℂ)).im| := by
    by_contra h
    have hh : |(-a^2*(t:ℂ)).im|≤Real.pi/2 := le_of_not_gt h
    exact not_le_of_gt hcos (Real.cos_nonneg_of_mem_Icc (abs_le.mp hh))
  have harg : (-a^2*(t:ℂ)).im=-2*a.re*a.im*t := by
    simp only [pow_two,Complex.mul_im,Complex.neg_im,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im]
    ring
  have ha0 : 0≤a.re := by linarith
  have hangb : |(-a^2*(t:ℂ)).im|≤2*a.re*t := by
    rw [harg,abs_mul,abs_mul,abs_mul]
    norm_num only [abs_neg,abs_of_pos (by norm_num : (0:ℝ)<2)]
    rw [abs_of_nonneg ha0,abs_of_pos ht]
    calc
      2*a.re * |a.im| * t≤2*a.re*1*t := by gcongr
      _=_ := by ring
  have hat : 3/4≤a.re*t := by linarith [Real.pi_gt_three]
  have ha2 : (3600:ℝ)≤a.re^2 := by nlinarith
  have hi2 : a.im^2≤1 := (sq_le_one_iff_abs_le_one _).mpr hi
  have hc2 : c^2≤2601 := by nlinarith
  have hd : (499/1800)*a.re^2≤(a^2).re-c^2 := by
    simp only [pow_two,Complex.mul_re]
    nlinarith
  have hdt := mul_le_mul_of_nonneg_right hd ht.le
  have hat' := mul_le_mul_of_nonneg_left hat ha0
  have hexp : c^2*t+(499/2400)*a.re≤(a^2).re*t := by nlinarith
  have hnorm : ‖Complex.exp (-a^2*(t:ℂ))‖≤
      Real.exp (-c^2*t)*Real.exp (-((499/2400)*a.re)) := by
    rw [Complex.norm_exp,←Real.exp_add,Real.exp_le_exp]
    simp only [Complex.mul_re,Complex.neg_re,Complex.ofReal_re,Complex.ofReal_im,
      mul_zero,sub_zero]
    nlinarith
  have hreal := Complex.re_le_norm (-Complex.exp (-a^2*(t:ℂ)))
  simp only [Complex.neg_re,norm_neg] at hreal
  nlinarith

theorem F_moderateZero_exp_le (z : FPositiveZeroOccurrence)
    (hz : 60≤(F_pairRoot z).re) :
    Real.exp (-((499/2400)*(F_pairRoot z).re))≤(‖F_pairRoot z‖^2)⁻¹/72 := by
  have hi : (F_pairRoot z).im^2≤1 :=
    ((sq_lt_one_iff_abs_lt_one _).mpr (F_zero_im_bound _ (F_pairRoot_is_zero z))).le
  have hn : ‖F_pairRoot z‖^2≤(F_pairRoot z).re^2+1 := by
    rw [Complex.sq_norm,Complex.normSq_apply]
    nlinarith
  have he : 72*‖F_pairRoot z‖^2≤Real.exp ((499/2400)*(F_pairRoot z).re) :=
    (mul_le_mul_of_nonneg_left hn (by norm_num)).trans
      (exponential_dominates_moderate_zero_weight hz)
  have hp : 0<72*‖F_pairRoot z‖^2 := by
    positivity [norm_pos_iff.mpr (F_pairRoot_ne_zero z)]
  rw [Real.exp_neg]
  calc
    _≤(72*‖F_pairRoot z‖^2)⁻¹ := inv_anti₀ hp he
    _=_ := by rw [mul_inv_rev,div_eq_mul_inv]

theorem F_selectedModerateHeat_lower (S : Set FPositiveZeroOccurrence) {c t : ℝ}
    (hS : ∀ z∈S, 60≤(F_pairRoot z).re) (hc : 0≤c) (hc1 : c≤51) (ht : 0<t) :
    -(35/36)*Real.exp (-c^2*t)≤(F_selectedHeatTrace S t).re := by
  have hdom := (summable_F_pairRoot_inv_norm_sq.subtype S).div_const 72
  have hsweights : Summable (fun z : S ↦
      Real.exp (-((499/2400)*(F_pairRoot z.val).re))) :=
    hdom.of_nonneg_of_le (fun _ ↦ (Real.exp_pos _).le)
      (fun z ↦ F_moderateZero_exp_le z.val (hS z.val z.property))
  have hnorm : (∑' z : S, (‖F_pairRoot z.val‖^2)⁻¹)≤70 := by
    apply le_trans _ F_pairRoot_inv_norm_sq_tsum_le_seventy
    exact Summable.tsum_le_tsum_of_inj Subtype.val Subtype.val_injective
      (fun _ _ ↦ by positivity) (fun _ ↦ le_rfl)
      (summable_F_pairRoot_inv_norm_sq.subtype S) summable_F_pairRoot_inv_norm_sq
  have hbudget : (∑' z : S, Real.exp (-((499/2400)*(F_pairRoot z.val).re)))≤35/36 := by
    calc
      _≤∑' z : S, (‖F_pairRoot z.val‖^2)⁻¹/72 :=
        hsweights.tsum_le_tsum (fun z ↦ F_moderateZero_exp_le z.val
          (hS z.val z.property)) hdom
      _=(∑' z : S, (‖F_pairRoot z.val‖^2)⁻¹)/72 := tsum_div_const
      _≤70/72 := div_le_div_of_nonneg_right hnorm (by norm_num)
      _=35/36 := by norm_num
  have hs : Summable (fun z : S ↦ F_zeroHeatTerm z.val t) :=
    (summable_F_zeroHeatTerm ht).subtype S
  have hsre := (Complex.reCLM.hasSum hs.hasSum).summable
  have hb := hsweights.mul_left (-Real.exp (-c^2*t))
  rw [F_selectedHeatTrace,Complex.re_tsum hs]
  calc
    _≤-Real.exp (-c^2*t)*(∑' z : S,
        Real.exp (-((499/2400)*(F_pairRoot z.val).re))) := by
      have h := mul_le_mul_of_nonpos_left hbudget
        (neg_nonpos.mpr (Real.exp_pos (-c^2*t)).le)
      nlinarith
    _=∑' z : S, -Real.exp (-c^2*t)*
        Real.exp (-((499/2400)*(F_pairRoot z.val).re)) := tsum_mul_left.symm
    _≤_ := hb.tsum_le_tsum (fun z ↦ moderate_zero_heat_lower (hS z.val z.property)
      (F_zero_im_bound _ (F_pairRoot_is_zero z.val)).le hc hc1 ht) hsre

theorem F_selectedHeatTrace_lower_of_three_zero_certificate
    (S : Set FPositiveZeroOccurrence) (a : S) {t : ℝ}
    (har : (F_pairRoot a.val).im=0) (ha : (F_pairRoot a.val).re≤51)
    (hother : ∀ z∈S, z≠a.val → 60≤(F_pairRoot z).re) (ht : 0<t) :
    (1/36)*Real.exp (-(F_pairRoot a.val).re^2*t)≤(F_selectedHeatTrace S t).re := by
  classical
  let L : Set FPositiveZeroOccurrence := {a.val}
  let H : Set FPositiveZeroOccurrence := S \ {a.val}
  have haL : a.val∈L := by simp [L]
  have hLo := F_selectedRealHeat_lower L ⟨a.val,haL⟩ (fun z hz ↦ by
    have he : z=a.val := Set.mem_singleton_iff.mp hz
    simpa only [he] using har) ht
  have hHi := F_selectedModerateHeat_lower H (fun z hz ↦ hother z hz.1 hz.2)
    (show 0≤(F_pairRoot a.val).re from
      (by linarith [F_pairRoot_re_gt_one a.val])) ha ht
  have hdis : Disjoint L H := by
    rw [Set.disjoint_left]
    intro z hzL hzH
    exact hzH.2 hzL
  have hunion : L∪H=S := by
    ext z
    change (z=a.val ∨ z∈S ∧ z≠a.val) ↔ z∈S
    constructor
    · rintro (h|h)
      · rw [h]; exact a.property
      · exact h.1
    · intro hz
      by_cases he : z=a.val
      · exact Or.inl he
      · exact Or.inr ⟨hz,he⟩
  have hsplit := Summable.tsum_union_disjoint (f:=fun z ↦ F_zeroHeatTerm z t) hdis
    ((summable_F_zeroHeatTerm ht).subtype L) ((summable_F_zeroHeatTerm ht).subtype H)
  rw [hunion] at hsplit
  change F_selectedHeatTrace S t=F_selectedHeatTrace L t+F_selectedHeatTrace H t at hsplit
  rw [hsplit,Complex.add_re]
  change Real.exp (-(F_pairRoot a.val).re^2*t)≤(F_selectedHeatTrace L t).re at hLo
  nlinarith

end ReciprocalXi

