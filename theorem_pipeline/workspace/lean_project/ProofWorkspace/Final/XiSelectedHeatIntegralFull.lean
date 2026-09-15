import ProofWorkspace.Final.XiSelectedHeatFull

set_option autoImplicit false
noncomputable section
open Set Filter Topology Complex MeasureTheory
open scoped ComplexConjugate
namespace ReciprocalXi

theorem continuousOn_F_selectedHeatTrace_Ici (S : Set FPositiveZeroOccurrence)
    {r : ℝ} (hr : 0<r) : ContinuousOn (F_selectedHeatTrace S) (Ici r) := by
  have hs : Summable (fun z : S ↦ ‖F_zeroHeatTerm z.val r‖) :=
    (summable_norm_F_zeroHeatTerm hr).subtype S
  change ContinuousOn (fun t ↦ ∑' z : S, F_zeroHeatTerm z.val t) (Ici r)
  apply continuousOn_tsum (fun z : S ↦ (continuous_F_zeroHeatTerm z.val).continuousOn) hs
  intro z t ht
  rw [norm_F_zeroHeatTerm, norm_F_zeroHeatTerm, Real.exp_le_exp]
  exact mul_le_mul_of_nonpos_left ht (neg_nonpos.mpr (F_pairRoot_sq_re_pos z.val).le)

theorem continuousOn_F_selectedHeatTrace (S : Set FPositiveZeroOccurrence) :
    ContinuousOn (F_selectedHeatTrace S) (Ioi 0) := by
  intro t ht
  change 0<t at ht
  have hm : Ici (t/2)∈𝓝 t := Ici_mem_nhds (by linarith : t/2<t)
  exact ((continuousOn_F_selectedHeatTrace_Ici S (show 0<t/2 by linarith)) t
    (show t∈Ici (t/2) by change t/2≤t; linarith)).continuousAt hm |>.continuousWithinAt

theorem summable_F_selectedRoot_inv_gap (S : Set FPositiveZeroOccurrence) (x : ℝ)
    (hgap : ∀ z∈S, x<((F_pairRoot z)^2).re) :
    Summable (fun z : S ↦ (((F_pairRoot z.val)^2).re-x)⁻¹) := by
  have hs := summable_F_pairRoot_inv_sq_re.subtype S
  apply (hs.mul_left 2).of_norm_bounded_eventually
  filter_upwards [hs.tendsto_cofinite_zero.eventually_le_const
    (show (0:ℝ)<(2*|x|+1)⁻¹ by positivity)] with z hz
  have hp := F_pairRoot_sq_re_pos z.val
  have hlarge : 2*|x|+1≤((F_pairRoot z.val)^2).re :=
    (inv_le_inv₀ hp (by positivity)).mp hz
  have hd : ((F_pairRoot z.val)^2).re/2≤((F_pairRoot z.val)^2).re-x := by
    linarith [le_abs_self x]
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (sub_pos.mpr (hgap z.val z.property)))]
  calc
    _ ≤ (((F_pairRoot z.val)^2).re/2)⁻¹ := inv_anti₀ (by positivity) hd
    _ = 2*(((F_pairRoot z.val)^2).re)⁻¹ := by rw [inv_div]; rfl

theorem F_zeroHeatTerm_weight_eq (z : FPositiveZeroOccurrence) (x t : ℝ) :
    Complex.exp ((x:ℂ)*(t:ℂ))*F_zeroHeatTerm z t =
      Complex.exp (-((F_pairRoot z)^2-(x:ℂ))*(t:ℂ)) := by
  rw [F_zeroHeatTerm, ← Complex.exp_add]
  congr 1
  ring

theorem integrableOn_F_zeroHeatTerm_weight (z : FPositiveZeroOccurrence) (x : ℝ)
    (hx : x<((F_pairRoot z)^2).re) :
    IntegrableOn (fun t : ℝ ↦ Complex.exp ((x:ℂ)*(t:ℂ))*F_zeroHeatTerm z t) (Ioi 0) := by
  simp_rw [F_zeroHeatTerm_weight_eq]
  apply integrableOn_exp_mul_complex_Ioi
  simp only [Complex.neg_re, Complex.sub_re, Complex.ofReal_re]
  linarith

theorem integral_norm_F_zeroHeatTerm_weight (z : FPositiveZeroOccurrence) (x : ℝ)
    (hx : x<((F_pairRoot z)^2).re) :
    (∫ t : ℝ in Ioi 0, ‖Complex.exp ((x:ℂ)*(t:ℂ))*F_zeroHeatTerm z t‖) =
      (((F_pairRoot z)^2).re-x)⁻¹ := by
  simp_rw [F_zeroHeatTerm_weight_eq, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.neg_re, Complex.sub_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  rw [integral_exp_mul_Ioi (by linarith) 0]
  simp only [mul_zero, Real.exp_zero, neg_div_neg_eq, one_div]

theorem integral_F_zeroHeatTerm_weight (z : FPositiveZeroOccurrence) (x : ℝ)
    (hx : x<((F_pairRoot z)^2).re) :
    (∫ t : ℝ in Ioi 0, Complex.exp ((x:ℂ)*(t:ℂ))*F_zeroHeatTerm z t) =
      ((F_pairRoot z)^2-(x:ℂ))⁻¹ := by
  simp_rw [F_zeroHeatTerm_weight_eq]
  rw [integral_exp_mul_complex_Ioi (by
    simp only [Complex.neg_re, Complex.sub_re, Complex.ofReal_re]
    linarith) 0]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, neg_div_neg_eq, one_div]

theorem integrableOn_F_selectedHeatTrace_weight (S : Set FPositiveZeroOccurrence)
    (x : ℝ) (hgap : ∀ z∈S, x<((F_pairRoot z)^2).re) :
    IntegrableOn (fun t : ℝ ↦ Complex.exp ((x:ℂ)*(t:ℂ))*F_selectedHeatTrace S t) (Ioi 0) := by
  letI : Countable FZero := F_zero_set_countable.to_subtype
  have hi (z : S) := integrableOn_F_zeroHeatTerm_weight z.val x (hgap z.val z.property)
  have hv (z : S) := integral_norm_F_zeroHeatTerm_weight z.val x (hgap z.val z.property)
  refine ⟨((show Continuous (fun t : ℝ ↦ Complex.exp ((x:ℂ)*(t:ℂ))) by
    fun_prop).continuousOn.mul (continuousOn_F_selectedHeatTrace S)).aestronglyMeasurable
      measurableSet_Ioi, ?_⟩
  have he : (∑' z : S, ∫⁻ t : ℝ in Ioi 0,
      ‖Complex.exp ((x:ℂ)*(t:ℂ))*F_zeroHeatTerm z.val t‖ₑ) < ⊤ := by
    simp_rw [← ofReal_integral_norm_eq_lintegral_enorm (hi _), hv]
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun z : S ↦ (inv_pos.mpr (sub_pos.mpr (hgap z.val z.property))).le)
      (summable_F_selectedRoot_inv_gap S x hgap)]
    exact ENNReal.ofReal_lt_top
  simp_rw [F_selectedHeatTrace, ← tsum_mul_left]
  calc
    _ ≤ ∫⁻ t : ℝ in Ioi 0, ∑' z : S,
        ‖Complex.exp ((x:ℂ)*(t:ℂ))*F_zeroHeatTerm z.val t‖ₑ :=
      lintegral_mono (fun _ ↦ enorm_tsum_le_tsum_enorm)
    _ = ∑' z : S, ∫⁻ t : ℝ in Ioi 0,
        ‖Complex.exp ((x:ℂ)*(t:ℂ))*F_zeroHeatTerm z.val t‖ₑ :=
      lintegral_tsum (fun z ↦ (integrableOn_F_zeroHeatTerm_weight z.val x
        (hgap z.val z.property)).1.enorm)
    _ < ⊤ := he

theorem integral_F_selectedHeatTrace_weight (S : Set FPositiveZeroOccurrence)
    (x : ℝ) (hgap : ∀ z∈S, x<((F_pairRoot z)^2).re) :
    (∫ t : ℝ in Ioi 0, Complex.exp ((x:ℂ)*(t:ℂ))*F_selectedHeatTrace S t) =
      ∑' z : S, ((F_pairRoot z.val)^2-(x:ℂ))⁻¹ := by
  letI : Countable FZero := F_zero_set_countable.to_subtype
  have hi (z : S) := integrableOn_F_zeroHeatTerm_weight z.val x (hgap z.val z.property)
  have hv (z : S) := integral_norm_F_zeroHeatTerm_weight z.val x (hgap z.val z.property)
  have hs : Summable (fun z : S ↦ ∫ t : ℝ in Ioi 0,
      ‖Complex.exp ((x:ℂ)*(t:ℂ))*F_zeroHeatTerm z.val t‖) := by
    simp_rw [hv]
    exact summable_F_selectedRoot_inv_gap S x hgap
  simp_rw [F_selectedHeatTrace, ← tsum_mul_left]
  rw [← integral_tsum_of_summable_integral_norm
    hi hs]
  exact tsum_congr (fun z ↦ integral_F_zeroHeatTerm_weight z.val x (hgap z.val z.property))

theorem integrableOn_F_selectedHeatTrace (S : Set FPositiveZeroOccurrence) :
    IntegrableOn (F_selectedHeatTrace S) (Ioi 0) := by
  simpa only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul] using
    integrableOn_F_selectedHeatTrace_weight S 0 (fun z _ ↦ F_pairRoot_sq_re_pos z)

def F_selectedConjEquiv (S : Set FPositiveZeroOccurrence)
    (hS : ∀ z∈S, F_pairConj z∈S) : S ≃ S where
  toFun z := ⟨F_pairConj z.val, hS z.val z.property⟩
  invFun z := ⟨F_pairConj z.val, hS z.val z.property⟩
  left_inv z := Subtype.ext (F_pairConj_involutive z.val)
  right_inv z := Subtype.ext (F_pairConj_involutive z.val)

theorem F_selectedHeatTrace_conj (S : Set FPositiveZeroOccurrence)
    (hS : ∀ z∈S, F_pairConj z∈S) (t : ℝ) :
    conj (F_selectedHeatTrace S t)=F_selectedHeatTrace S t := by
  rw [F_selectedHeatTrace, Complex.conj_tsum]
  calc
    _ = ∑' z : S, F_zeroHeatTerm (F_selectedConjEquiv S hS z).val t := by
      apply tsum_congr
      intro z
      exact (F_zeroHeatTerm_conj z.val t).symm
    _ = _ := (F_selectedConjEquiv S hS).tsum_eq (fun z ↦ F_zeroHeatTerm z.val t)

theorem F_selectedHeatTrace_im (S : Set FPositiveZeroOccurrence)
    (hS : ∀ z∈S, F_pairConj z∈S) (t : ℝ) : (F_selectedHeatTrace S t).im=0 := by
  have h := congrArg Complex.im (F_selectedHeatTrace_conj S hS t)
  simp only [Complex.conj_im] at h
  linarith

end ReciprocalXi
