import ProofWorkspace.Final.XiHeatExponentFull
import ProofWorkspace.Final.XiSelectedHeatIntegralFull

set_option autoImplicit false
noncomputable section
open Set Filter Topology Complex MeasureTheory Metric
namespace ReciprocalXi

def heatExponentIntegrandOf (H : ℝ → ℂ) (u t : ℝ) : ℂ := F_heatExponentKernel u t*H t
def heatExponentOf (H : ℝ → ℂ) (u : ℝ) : ℂ := ∫ t : ℝ in Ioi 0, heatExponentIntegrandOf H u t
def heatExponentDerivativeOf (H : ℝ → ℂ) (u t : ℝ) : ℂ :=
  -2*(u:ℂ)*Complex.exp (-((u^2:ℝ):ℂ)*(t:ℂ))*H t

theorem aestronglyMeasurable_heatExponentIntegrandOf {H : ℝ → ℂ} (hH : IntegrableOn H (Ioi 0)) (u : ℝ) :
    AEStronglyMeasurable (heatExponentIntegrandOf H u) (volume.restrict (Ioi 0)) := by
  apply AEStronglyMeasurable.mul _ hH.1
  exact (show Measurable (F_heatExponentKernel u) by
    unfold F_heatExponentKernel
    fun_prop).aestronglyMeasurable

theorem integrableOn_heatExponentIntegrandOf {H : ℝ → ℂ} (hH : IntegrableOn H (Ioi 0)) (u : ℝ) :
    IntegrableOn (heatExponentIntegrandOf H u) (Ioi 0) := by
  apply (hH.norm.const_mul (u^2)).mono'
    (aestronglyMeasurable_heatExponentIntegrandOf hH u)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [heatExponentIntegrandOf, norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_F_heatExponentKernel_le u ht) (norm_nonneg _)

theorem heatExponentIntegrandOf_hasDerivAt {H : ℝ → ℂ} (hH : IntegrableOn H (Ioi 0)) (u : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun v : ℝ ↦ heatExponentIntegrandOf H v t) (heatExponentDerivativeOf H u t) u :=
  (F_heatExponentKernel_hasDerivAt u ht).mul_const (H t)

theorem norm_heatExponentDerivativeOf_le {H : ℝ → ℂ} (hH : IntegrableOn H (Ioi 0)) (u : ℝ) {t : ℝ} (ht : 0 < t) :
    ‖heatExponentDerivativeOf H u t‖ ≤ 2 * |u| * ‖H t‖ := by
  have he : ‖Complex.exp (-((u^2:ℝ):ℂ)*(t:ℂ))‖ ≤ 1 := by
    rw [Complex.norm_exp, Real.exp_le_one_iff]
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg u)) ht.le
  simp only [heatExponentDerivativeOf, norm_mul, norm_neg, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ 2 * |u| * 1 * ‖H t‖ := by gcongr
    _ = _ := by ring

theorem aestronglyMeasurable_heatExponentDerivativeOf {H : ℝ → ℂ} (hH : IntegrableOn H (Ioi 0)) (u : ℝ) :
    AEStronglyMeasurable (heatExponentDerivativeOf H u) (volume.restrict (Ioi 0)) := by
  apply AEStronglyMeasurable.mul _ hH.1
  exact (show Continuous (fun t : ℝ ↦ -2*(u:ℂ)*
    Complex.exp (-((u^2:ℝ):ℂ)*(t:ℂ))) by fun_prop).aestronglyMeasurable

theorem heatExponentOf_hasDerivAt {H : ℝ → ℂ} (hH : IntegrableOn H (Ioi 0)) (u : ℝ) :
    HasDerivAt (heatExponentOf H)
      (-2*(u:ℂ)*(∫ t : ℝ in Ioi 0,
        Complex.exp (-((u^2:ℝ):ℂ)*(t:ℂ))*H t)) u := by
  have hb : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0), ∀ v∈ball u 1,
      ‖heatExponentDerivativeOf H v t‖ ≤ 2*(|u|+1)*‖H t‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro v hv
    have hv' : |v| ≤ |u|+1 := by
      have hd : |v-u| < 1 := by simpa [Real.dist_eq] using hv
      have hm := abs_add_le (v-u) u
      rw [sub_add_cancel] at hm
      linarith
    exact (norm_heatExponentDerivativeOf_le hH v ht).trans (by gcongr)
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F:=heatExponentIntegrandOf H) (F':=heatExponentDerivativeOf H)
    (μ:=volume.restrict (Ioi 0)) (x₀:=u) (s:=ball u 1)
    (bound:=fun t ↦ 2*(|u|+1)*‖H t‖)
    (ball_mem_nhds u (by norm_num))
    (Eventually.of_forall (aestronglyMeasurable_heatExponentIntegrandOf hH))
    (integrableOn_heatExponentIntegrandOf hH u)
    (aestronglyMeasurable_heatExponentDerivativeOf hH u) hb
    (hH.norm.const_mul (2*(|u|+1)))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact fun v _ ↦ heatExponentIntegrandOf_hasDerivAt hH v ht)
  convert hd.2 using 1
  simp only [heatExponentDerivativeOf, mul_assoc, integral_const_mul]


theorem heatExponentOf_zero (H : ℝ → ℂ) : heatExponentOf H 0=0 := by
  simp [heatExponentOf, heatExponentIntegrandOf, F_heatExponentKernel]

theorem F_heatExponentTerm_hasDerivAt (z : FPositiveZeroOccurrence) (u : ℝ) :
    HasDerivAt (heatExponentOf (F_zeroHeatTerm z))
      (-2*(u:ℂ)*((F_pairRoot z)^2+(u:ℂ)^2)⁻¹) u := by
  have hd := heatExponentOf_hasDerivAt (integrableOn_F_zeroHeatTerm z) u
  rw [integral_F_zeroHeatTerm_laplace z (sq_nonneg u)] at hd
  simpa only [Complex.ofReal_pow] using hd

theorem F_pairRoot_sq_add_real_sq_ne_zero (z : FPositiveZeroOccurrence) (u : ℝ) :
    (F_pairRoot z)^2+(u:ℂ)^2≠0 := by
  intro h
  have he := congrArg Complex.re h
  simp only [Complex.add_re, ← Complex.ofReal_pow, Complex.ofReal_re, Complex.zero_re] at he
  linarith [F_pairRoot_sq_re_pos z, sq_nonneg u]

theorem F_heatExponentTerm_exp_mul (z : FPositiveZeroOccurrence) (u : ℝ) :
    Complex.exp (heatExponentOf (F_zeroHeatTerm z) u)*((F_pairRoot z)^2+(u:ℂ)^2) =
      (F_pairRoot z)^2 := by
  let h (v : ℝ) := Complex.exp (heatExponentOf (F_zeroHeatTerm z) v)*
    ((F_pairRoot z)^2+(v:ℂ)^2)
  have hh : ∀ v, HasDerivAt h 0 v := by
    intro v
    have hq := ((hasDerivAt_id v).ofReal_comp.pow 2).const_add ((F_pairRoot z)^2)
    have hd := (F_heatExponentTerm_hasDerivAt z v).cexp.mul hq
    convert hd using 1
    simp only [Nat.reduceSub, pow_one, Pi.pow_apply, id_eq, Complex.ofReal_one,
      Complex.ofReal_ofNat, mul_one]
    field_simp [F_pairRoot_sq_add_real_sq_ne_zero z v]
    ring
  have he := is_const_of_deriv_eq_zero (fun v ↦ (hh v).differentiableAt)
    (fun v ↦ (hh v).deriv) u 0
  simpa only [h, heatExponentOf_zero, Complex.exp_zero, Complex.ofReal_zero,
    zero_pow (by decide : (2:ℕ)≠0), add_zero, one_mul] using he

theorem F_heatExponentTerm_exp (z : FPositiveZeroOccurrence) (u : ℝ) :
    Complex.exp (heatExponentOf (F_zeroHeatTerm z) u) =
      (F_pairRoot z)^2/((F_pairRoot z)^2+(u:ℂ)^2) := by
  exact (eq_div_iff (F_pairRoot_sq_add_real_sq_ne_zero z u)).mpr
    (F_heatExponentTerm_exp_mul z u)

theorem F_heatExponentTerm_cancel_factor (z : FPositiveZeroOccurrence) (u : ℝ) :
    Complex.exp (heatExponentOf (F_zeroHeatTerm z) u)*(1+(u:ℂ)^2/(F_pairRoot z)^2)=1 := by
  rw [F_heatExponentTerm_exp]
  field_simp [F_pairRoot_ne_zero z, F_pairRoot_sq_add_real_sq_ne_zero z u]

theorem F_heatExponent_delete_finite (s : Finset FPositiveZeroOccurrence) (u : ℝ) :
    F_heatExponent u = (∑ z∈s, heatExponentOf (F_zeroHeatTerm z) u)+
      heatExponentOf (F_selectedHeatTrace ((s : Set FPositiveZeroOccurrence)ᶜ)) u := by
  have hi (z : FPositiveZeroOccurrence) :=
    integrableOn_heatExponentIntegrandOf (integrableOn_F_zeroHeatTerm z) u
  have hs := integrableOn_heatExponentIntegrandOf
    (integrableOn_F_selectedHeatTrace ((s : Set FPositiveZeroOccurrence)ᶜ)) u
  have hsplit : ∀ t>0, F_zeroHeatTrace t=(∑ z∈s, F_zeroHeatTerm z t)+
      F_selectedHeatTrace ((s : Set FPositiveZeroOccurrence)ᶜ) t := by
    intro t ht
    exact ((summable_F_zeroHeatTerm ht).sum_add_tsum_subtype_compl s).symm
  unfold F_heatExponent heatExponentOf
  calc
    _ = ∫ t : ℝ in Ioi 0, (∑ z∈s, heatExponentIntegrandOf (F_zeroHeatTerm z) u t)+
        heatExponentIntegrandOf (F_selectedHeatTrace ((s : Set FPositiveZeroOccurrence)ᶜ)) u t := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      simp only [F_heatExponentIntegrand, heatExponentIntegrandOf, hsplit t ht,
        mul_add, Finset.mul_sum]
    _ = _ := by
      rw [integral_add (integrable_finset_sum s (fun z _ ↦ hi z)) hs,
        integral_finset_sum s (fun z _ ↦ hi z)]

/-- Exact finite deletion identity; this does not assert a positive probability law. -/
theorem reciprocalTransform_delete_finite_heat (s : Finset FPositiveZeroOccurrence) (u : ℝ) :
    reciprocalTransform u*(∏ z∈s, (1+(u:ℂ)^2/(F_pairRoot z)^2)) =
      Complex.exp (heatExponentOf
        (F_selectedHeatTrace ((s : Set FPositiveZeroOccurrence)ᶜ)) u) := by
  have hp : Complex.exp (∑ z∈s, heatExponentOf (F_zeroHeatTerm z) u)*
      (∏ z∈s, (1+(u:ℂ)^2/(F_pairRoot z)^2))=1 := by
    rw [Complex.exp_sum, ← Finset.prod_mul_distrib]
    simp only [F_heatExponentTerm_cancel_factor, Finset.prod_const_one]
  rw [reciprocalTransform_eq_exp_heatExponent, F_heatExponent_delete_finite, Complex.exp_add]
  calc
    _ = (Complex.exp (∑ z∈s, heatExponentOf (F_zeroHeatTerm z) u)*
        (∏ z∈s, (1+(u:ℂ)^2/(F_pairRoot z)^2)))*
        Complex.exp (heatExponentOf
          (F_selectedHeatTrace ((s : Set FPositiveZeroOccurrence)ᶜ)) u) := by ring
    _ = _ := by rw [hp, one_mul]

end ReciprocalXi
