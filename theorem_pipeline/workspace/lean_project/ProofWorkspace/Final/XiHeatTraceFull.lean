import ProofWorkspace.Final.XiPairedProductFull
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Group.FunctionSeries

set_option autoImplicit false
noncomputable section
open Set Filter Topology Complex MeasureTheory
open scoped ComplexConjugate
namespace ReciprocalXi

theorem F_pairRoot_re_gt_one (z : FPositiveZeroOccurrence) : 1 < (F_pairRoot z).re := by
  have hp : 0 < (F_pairRoot z).re := z.property
  simpa only [abs_of_pos hp] using
    F_zero_abs_re_gt_one (F_pairRoot z) (F_pairRoot_is_zero z)

theorem F_pairRoot_sq_re_pos (z : FPositiveZeroOccurrence) : 0 < ((F_pairRoot z)^2).re := by
  have hr := F_pairRoot_re_gt_one z
  have hi : (F_pairRoot z).im^2 < 1 :=
    (sq_lt_one_iff_abs_lt_one _).mpr (F_zero_im_bound _ (F_pairRoot_is_zero z))
  simp only [pow_two, Complex.mul_re]
  nlinarith

theorem F_pairRoot_sq_re_eq (z : FPositiveZeroOccurrence) :
    ((F_pairRoot z)^2).re = ‖F_pairRoot z‖^2-2*(F_pairRoot z).im^2 := by
  rw [Complex.sq_norm]
  simp only [pow_two, Complex.mul_re, Complex.normSq_apply]
  ring

theorem summable_F_pairRoot_inv_sq_re :
    Summable (fun z : FPositiveZeroOccurrence ↦ (((F_pairRoot z)^2).re)⁻¹) := by
  apply (summable_F_pairRoot_inv_norm_sq.mul_left 2).of_norm_bounded_eventually
  filter_upwards [summable_F_pairRoot_inv_norm_sq.tendsto_cofinite_zero.eventually_le_const
    (show (0:ℝ)<1/4 by norm_num)] with z hz
  have hn : 0 < ‖F_pairRoot z‖^2 := pow_pos (norm_pos_iff.mpr (F_pairRoot_ne_zero z)) 2
  have hlarge : 4 ≤ ‖F_pairRoot z‖^2 := by
    have hm := mul_le_mul_of_nonneg_right hz hn.le
    rw [inv_mul_cancel₀ (ne_of_gt hn)] at hm
    linarith
  have hi : (F_pairRoot z).im^2 < 1 :=
    (sq_lt_one_iff_abs_lt_one _).mpr (F_zero_im_bound _ (F_pairRoot_is_zero z))
  have hd : ‖F_pairRoot z‖^2/2 ≤ ((F_pairRoot z)^2).re := by
    rw [F_pairRoot_sq_re_eq]
    linarith
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (F_pairRoot_sq_re_pos z))]
  calc
    (((F_pairRoot z)^2).re)⁻¹ ≤ (‖F_pairRoot z‖^2/2)⁻¹ :=
      inv_anti₀ (by positivity) hd
    _ = 2*(‖F_pairRoot z‖^2)⁻¹ := by rw [inv_div]; rfl

def F_zeroHeatTerm (z : FPositiveZeroOccurrence) (t : ℝ) : ℂ :=
  Complex.exp (-((F_pairRoot z)^2)*(t:ℂ))

def F_zeroHeatTrace (t : ℝ) : ℂ := ∑' z : FPositiveZeroOccurrence, F_zeroHeatTerm z t

theorem norm_F_zeroHeatTerm (z : FPositiveZeroOccurrence) (t : ℝ) :
    ‖F_zeroHeatTerm z t‖ = Real.exp (-((F_pairRoot z)^2).re*t) := by
  simp [F_zeroHeatTerm, Complex.norm_exp, Complex.mul_re]

theorem norm_F_zeroHeatTerm_le (z : FPositiveZeroOccurrence) {t : ℝ} (ht : 0 < t) :
    ‖F_zeroHeatTerm z t‖ ≤ t⁻¹*(((F_pairRoot z)^2).re)⁻¹ := by
  rw [norm_F_zeroHeatTerm, neg_mul, Real.exp_neg]
  have hp : 0 < ((F_pairRoot z)^2).re*t := mul_pos (F_pairRoot_sq_re_pos z) ht
  have he : ((F_pairRoot z)^2).re*t ≤ Real.exp (((F_pairRoot z)^2).re*t) := by
    linarith [Real.add_one_le_exp (((F_pairRoot z)^2).re*t)]
  calc
    (Real.exp (((F_pairRoot z)^2).re*t))⁻¹ ≤ (((F_pairRoot z)^2).re*t)⁻¹ :=
      inv_anti₀ hp he
    _ = _ := by rw [mul_inv_rev]

theorem summable_norm_F_zeroHeatTerm {t : ℝ} (ht : 0 < t) :
    Summable (fun z : FPositiveZeroOccurrence ↦ ‖F_zeroHeatTerm z t‖) := by
  exact (summable_F_pairRoot_inv_sq_re.mul_left t⁻¹).of_nonneg_of_le
    (fun _ ↦ norm_nonneg _) (fun z ↦ norm_F_zeroHeatTerm_le z ht)

theorem summable_F_zeroHeatTerm {t : ℝ} (ht : 0 < t) :
    Summable (fun z : FPositiveZeroOccurrence ↦ F_zeroHeatTerm z t) :=
  (summable_norm_F_zeroHeatTerm ht).of_norm

theorem continuous_F_zeroHeatTerm (z : FPositiveZeroOccurrence) :
    Continuous (F_zeroHeatTerm z) := by
  unfold F_zeroHeatTerm
  fun_prop

theorem continuousOn_F_zeroHeatTrace_Ici {r : ℝ} (hr : 0 < r) :
    ContinuousOn F_zeroHeatTrace (Ici r) := by
  apply continuousOn_tsum (fun z ↦ (continuous_F_zeroHeatTerm z).continuousOn)
    (summable_norm_F_zeroHeatTerm hr)
  intro z t ht
  rw [norm_F_zeroHeatTerm, norm_F_zeroHeatTerm, Real.exp_le_exp]
  exact mul_le_mul_of_nonpos_left ht (neg_nonpos.mpr (F_pairRoot_sq_re_pos z).le)

theorem continuousOn_F_zeroHeatTrace : ContinuousOn F_zeroHeatTrace (Ioi 0) := by
  intro t ht
  change 0 < t at ht
  have hm : Ici (t/2) ∈ 𝓝 t := Ici_mem_nhds (by linarith : t/2<t)
  exact ((continuousOn_F_zeroHeatTrace_Ici (show 0<t/2 by linarith)) t
    (show t∈Ici (t/2) by change t/2≤t; linarith)).continuousAt hm |>.continuousWithinAt

theorem integrableOn_F_zeroHeatTerm (z : FPositiveZeroOccurrence) :
    IntegrableOn (F_zeroHeatTerm z) (Ioi 0) := by
  exact integrableOn_exp_mul_complex_Ioi (by
    simpa only [Complex.neg_re] using neg_neg_of_pos (F_pairRoot_sq_re_pos z)) 0

theorem integral_norm_F_zeroHeatTerm (z : FPositiveZeroOccurrence) :
    (∫ t : ℝ in Ioi 0, ‖F_zeroHeatTerm z t‖) = (((F_pairRoot z)^2).re)⁻¹ := by
  simp_rw [norm_F_zeroHeatTerm]
  rw [integral_exp_mul_Ioi (neg_neg_of_pos (F_pairRoot_sq_re_pos z)) 0]
  simp

theorem integral_F_zeroHeatTerm (z : FPositiveZeroOccurrence) :
    (∫ t : ℝ in Ioi 0, F_zeroHeatTerm z t) = ((F_pairRoot z)^2)⁻¹ := by
  unfold F_zeroHeatTerm
  rw [integral_exp_mul_complex_Ioi (by
    simpa only [Complex.neg_re] using neg_neg_of_pos (F_pairRoot_sq_re_pos z)) 0]
  simp

theorem integrableOn_F_zeroHeatTrace : IntegrableOn F_zeroHeatTrace (Ioi 0) := by
  letI : Countable FZero := F_zero_set_countable.to_subtype
  refine ⟨continuousOn_F_zeroHeatTrace.aestronglyMeasurable measurableSet_Ioi, ?_⟩
  have he : (∑' z : FPositiveZeroOccurrence, ∫⁻ t : ℝ in Ioi 0,
      ‖F_zeroHeatTerm z t‖ₑ) < ⊤ := by
    simp_rw [← ofReal_integral_norm_eq_lintegral_enorm (integrableOn_F_zeroHeatTerm _),
      integral_norm_F_zeroHeatTerm]
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun z ↦ (inv_pos.mpr (F_pairRoot_sq_re_pos z)).le) summable_F_pairRoot_inv_sq_re]
    exact ENNReal.ofReal_lt_top
  calc
    ∫⁻ t : ℝ in Ioi 0, ‖F_zeroHeatTrace t‖ₑ ≤
        ∫⁻ t : ℝ in Ioi 0, ∑' z : FPositiveZeroOccurrence, ‖F_zeroHeatTerm z t‖ₑ :=
      lintegral_mono (fun _ ↦ enorm_tsum_le_tsum_enorm)
    _ = ∑' z : FPositiveZeroOccurrence, ∫⁻ t : ℝ in Ioi 0, ‖F_zeroHeatTerm z t‖ₑ :=
      lintegral_tsum (fun z ↦ (integrableOn_F_zeroHeatTerm z).1.enorm)
    _ < ⊤ := he

theorem integral_F_zeroHeatTrace : (∫ t : ℝ in Ioi 0, F_zeroHeatTrace t) =
    ∑' z : FPositiveZeroOccurrence, ((F_pairRoot z)^2)⁻¹ := by
  letI : Countable FZero := F_zero_set_countable.to_subtype
  have hs : Summable (fun z : FPositiveZeroOccurrence ↦
      ∫ t : ℝ in Ioi 0, ‖F_zeroHeatTerm z t‖) := by
    simpa only [integral_norm_F_zeroHeatTerm] using summable_F_pairRoot_inv_sq_re
  calc
    _ = ∑' z : FPositiveZeroOccurrence, ∫ t : ℝ in Ioi 0, F_zeroHeatTerm z t :=
      (integral_tsum_of_summable_integral_norm integrableOn_F_zeroHeatTerm hs).symm
    _ = _ := tsum_congr integral_F_zeroHeatTerm

def F_pairConj (z : FPositiveZeroOccurrence) : FPositiveZeroOccurrence :=
  ⟨⟨⟨conj (F_pairRoot z), F_zero_conj _ (F_pairRoot_is_zero z)⟩,
    ⟨z.val.2.val, by
      change z.val.2.val < analyticOrderNatAt F (conj (F_pairRoot z))
      rw [F_orderNat_conj]
      exact z.val.2.isLt⟩⟩, by simpa using z.property⟩

theorem F_pairRoot_conj (z : FPositiveZeroOccurrence) :
    F_pairRoot (F_pairConj z) = conj (F_pairRoot z) := rfl

theorem F_pairConj_involutive : Function.Involutive F_pairConj := by
  intro z
  apply Subtype.ext
  apply Sigma.ext
  · apply Subtype.ext
    exact conj_conj _
  · apply (Fin.heq_ext_iff (by simp only [F_pairConj, F_pairRoot, conj_conj])).mpr
    rfl

def F_pairConjEquiv : FPositiveZeroOccurrence ≃ FPositiveZeroOccurrence :=
  { toFun := F_pairConj, invFun := F_pairConj,
    left_inv := F_pairConj_involutive, right_inv := F_pairConj_involutive }

theorem F_zeroHeatTerm_conj (z : FPositiveZeroOccurrence) (t : ℝ) :
    F_zeroHeatTerm (F_pairConj z) t = conj (F_zeroHeatTerm z t) := by
  simp only [F_zeroHeatTerm, F_pairRoot_conj, ← Complex.exp_conj,
    map_mul, map_neg, map_pow, Complex.conj_ofReal]

theorem F_zeroHeatTrace_conj (t : ℝ) : conj (F_zeroHeatTrace t) = F_zeroHeatTrace t := by
  rw [F_zeroHeatTrace, Complex.conj_tsum]
  calc
    _ = ∑' z : FPositiveZeroOccurrence, F_zeroHeatTerm (F_pairConjEquiv z) t := by
      apply tsum_congr
      intro z
      exact (F_zeroHeatTerm_conj z t).symm
    _ = _ := F_pairConjEquiv.tsum_eq (fun z ↦ F_zeroHeatTerm z t)

theorem F_zeroHeatTrace_im (t : ℝ) : (F_zeroHeatTrace t).im = 0 := by
  have h := congrArg Complex.im (F_zeroHeatTrace_conj t)
  simp only [Complex.conj_im] at h
  linarith

end ReciprocalXi

