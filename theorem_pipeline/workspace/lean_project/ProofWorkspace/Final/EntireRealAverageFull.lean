import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Analysis.Complex.Schwarz

set_option autoImplicit false
noncomputable section
open Set Metric Filter Topology Real Complex
namespace ReciprocalXi

theorem reflectedKernel_denom_ne_zero (R : ℝ) (hR : 0<R) (w z : ℂ)
    (hw : ‖w‖<R) (hz : ‖z‖≤R) :
    (R:ℂ)^2-starRingEnd ℂ w*z ≠ 0 := by
  have hlt : ‖starRingEnd ℂ w*z‖ < R^2 := by
    rw [norm_mul, norm_conj]
    calc
      _ ≤ ‖w‖*R := mul_le_mul_of_nonneg_left hz (norm_nonneg _)
      _ < R*R := mul_lt_mul_of_pos_right hw hR
      _ = _ := by ring
  intro he
  have he' := congrArg norm (sub_eq_zero.mp he)
  simp only [norm_pow, norm_real, Real.norm_eq_abs, abs_of_pos hR] at he'
  linarith

theorem cauchyKernel_conj_on_circle (R : ℝ) (hR : 0<R) (w z : ℂ)
    (hw : ‖w‖<R) (hz : ‖z‖=R) :
    starRingEnd ℂ (z/(z-w)) = (R:ℂ)^2/((R:ℂ)^2-starRingEnd ℂ w*z) := by
  have hden := reflectedKernel_denom_ne_zero R hR w z hw hz.le
  have hzw : z-w≠0 := by intro h; rw [sub_eq_zero.mp h] at hz; linarith
  have hconj : starRingEnd ℂ z-starRingEnd ℂ w≠0 := by
    rw [← map_sub]
    exact (map_ne_zero (starRingEnd ℂ)).mpr hzw
  have hnorm : z*starRingEnd ℂ z = (R:ℂ)^2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz, Complex.ofReal_pow]
  simp only [map_div₀, map_sub]
  field_simp [hden, hconj]
  linear_combination -(starRingEnd ℂ w)*hnorm

theorem entire_circleAverage_conj_kernel {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (R : ℝ) (hR : 0<R) (w : ℂ) (hw : ‖w‖<R) :
    circleAverage (fun z ↦ starRingEnd ℂ (z/(z-w))*f z) 0 R = f 0 := by
  let g (z : ℂ) := (R:ℂ)^2/((R:ℂ)^2-starRingEnd ℂ w*z)*f z
  have hg : DifferentiableOn ℂ g (closedBall 0 R) := by
    intro z hz
    have hden := reflectedKernel_denom_ne_zero R hR w z hw
      (by simpa only [mem_closedBall, dist_zero_right] using hz)
    apply DifferentiableAt.differentiableWithinAt
    dsimp [g]
    fun_prop (disch := assumption)
  have he : circleAverage (fun z ↦ starRingEnd ℂ (z/(z-w))*f z) 0 R =
      circleAverage g 0 R := by
    apply circleAverage_congr_sphere
    intro z hz
    dsimp only [g]
    rw [cauchyKernel_conj_on_circle R hR w z hw
      (by simpa only [mem_sphere_iff_norm, sub_zero, abs_of_pos hR] using hz)]
  rw [he]
  have hg' : DifferentiableOn ℂ g (closedBall 0 |R|) := by rwa [abs_of_pos hR]
  have hmean := hg'.diffContOnCl_ball subset_rfl |>.circleAverage
  rw [hmean]
  simp [g, ne_of_gt hR]

theorem cauchyKernel_continuousOn_sphere (R : ℝ) (hR : 0<R) (w : ℂ) (hw : ‖w‖<R) :
    ContinuousOn (fun z : ℂ ↦ z/(z-w)) (sphere 0 |R|) := by
  apply continuousOn_id.div (continuousOn_id.sub continuousOn_const)
  intro z hz he
  change z-w=0 at he
  have hz' : ‖z‖=R := by simpa only [mem_sphere_iff_norm, sub_zero, abs_of_pos hR] using hz
  rw [sub_eq_zero.mp he] at hz'
  linarith

theorem entire_circleAverage_kernel_conj {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (R : ℝ) (hR : 0<R) (w : ℂ) (hw : ‖w‖<R) :
    circleAverage (fun z ↦ z/(z-w)*starRingEnd ℂ (f z)) 0 R = starRingEnd ℂ (f 0) := by
  have hi : CircleIntegrable (fun z ↦ starRingEnd ℂ (z/(z-w))*f z) 0 R :=
    (Complex.continuous_conj.comp_continuousOn (cauchyKernel_continuousOn_sphere R hR w hw)
      |>.mul hf.continuous.continuousOn).circleIntegrable'
  have h := conjCLE.toContinuousLinearMap.circleAverage_comp_comm hi
  rw [entire_circleAverage_conj_kernel hf R hR w hw] at h
  simpa only [Function.comp_def, ContinuousLinearEquiv.coe_coe, conjCLE_apply, map_mul,
    starRingEnd_self_apply] using h

theorem entire_realpart_cauchy {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (R : ℝ) (hR : 0<R) (w : ℂ) (hw : ‖w‖<R) :
    f w+starRingEnd ℂ (f 0) =
      circleAverage (fun z ↦ z/(z-w)*(f z+starRingEnd ℂ (f z))) 0 R := by
  have hk := cauchyKernel_continuousOn_sphere R hR w hw
  have hi : CircleIntegrable (fun z ↦ z/(z-w)*f z) 0 R :=
    (hk.mul hf.continuous.continuousOn).circleIntegrable'
  have hi' : CircleIntegrable (fun z ↦ z/(z-w)*starRingEnd ℂ (f z)) 0 R :=
    (hk.mul (Complex.continuous_conj.comp hf.continuous).continuousOn).circleIntegrable'
  have hd : DiffContOnCl ℂ f (ball 0 |R|) :=
    (hf.differentiableOn : DifferentiableOn ℂ f (closedBall 0 |R|)).diffContOnCl_ball subset_rfl
  have hc := hd.circleAverage_smul_div (w := w)
    (by simpa only [mem_ball_iff_norm, sub_zero, abs_of_pos hR] using hw)
  simp only [sub_zero, smul_eq_mul] at hc
  simp_rw [mul_add]
  rw [circleAverage_fun_add hi hi', hc, entire_circleAverage_kernel_conj hf R hR w hw]

theorem norm_circleAverage_le_average_norm (f : ℂ → ℂ) (R : ℝ) :
    ‖circleAverage f 0 R‖ ≤ circleAverage (fun z ↦ ‖f z‖) 0 R := by
  rw [circleAverage_def, circleAverage_def, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0:ℝ)≤(2*Real.pi)⁻¹), smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (intervalIntegral.norm_integral_le_integral_norm
    (by positivity)) (by positivity)

theorem entire_norm_le_realpart_average {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hf0 : f 0=0) (R : ℝ) (hR : 0<R) (w : ℂ) (hw : ‖w‖<R) :
    ‖f w‖ ≤ (2*R/(R-‖w‖))*circleAverage (fun z ↦ |(f z).re|) 0 R := by
  have hrepr := entire_realpart_cauchy hf R hR w hw
  simp only [hf0, map_zero, add_zero] at hrepr
  rw [hrepr]
  apply (norm_circleAverage_le_average_norm _ R).trans
  have hc : ContinuousOn (fun z ↦ z/(z-w)*(f z+starRingEnd ℂ (f z))) (sphere 0 |R|) :=
    (cauchyKernel_continuousOn_sphere R hR w hw).mul
      (hf.continuous.add (Complex.continuous_conj.comp hf.continuous)).continuousOn
  have hi := hc.norm.circleIntegrable'
  have hi' : CircleIntegrable (fun z ↦ (2*R/(R-‖w‖))*|(f z).re|) 0 R :=
    (continuous_const.mul ((Complex.continuous_re.comp hf.continuous).abs)).continuousOn.circleIntegrable'
  have hb := circleAverage_mono hi hi' (fun z hz ↦ by
    have hz' : ‖z‖=R := by simpa only [mem_sphere_iff_norm, sub_zero, abs_of_pos hR] using hz
    have hd : R-‖w‖≤‖z-w‖ := by rw [← hz']; exact norm_sub_norm_le _ _
    have hk : ‖z/(z-w)‖≤R/(R-‖w‖) := by
      rw [norm_div, hz']
      exact div_le_div_of_nonneg_left hR.le (by linarith) hd
    rw [norm_mul, Complex.add_conj, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos (by norm_num : (0:ℝ)<2)]
    calc
      _ ≤ (R/(R-‖w‖))*(2*|(f z).re|) := mul_le_mul_of_nonneg_right hk (by positivity)
      _ = _ := by ring)
  apply hb.trans_eq
  exact circleAverage_fun_smul (𝕜 := ℝ)

theorem entire_abs_re_average_eq_twice_positive {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hf0 : f 0=0) (R : ℝ) :
    circleAverage (fun z ↦ |(f z).re|) 0 R =
      2*circleAverage (fun z ↦ max 0 (f z).re) 0 R := by
  have hi : CircleIntegrable f 0 R := hf.continuous.continuousOn.circleIntegrable'
  have hd : DiffContOnCl ℂ f (ball 0 |R|) :=
    (hf.differentiableOn : DifferentiableOn ℂ f (closedBall 0 |R|)).diffContOnCl_ball subset_rfl
  have hmean : circleAverage (fun z ↦ (f z).re) 0 R = 0 := by
    have h := Complex.reCLM.circleAverage_comp_comm hi
    rw [hd.circleAverage, hf0] at h
    exact h
  have hr : Continuous (fun z ↦ (f z).re) := Complex.continuous_re.comp hf.continuous
  have hp : Continuous (fun z ↦ max 0 (f z).re) := continuous_const.max hr
  have he : (fun z ↦ |(f z).re|) = (fun z ↦ 2*max 0 (f z).re-(f z).re) := by
    ext z
    by_cases hz : 0≤(f z).re
    · rw [abs_of_nonneg hz, max_eq_right hz]; ring
    · rw [abs_of_nonpos (le_of_not_ge hz), max_eq_left (le_of_not_ge hz)]; ring
  have hi2 : CircleIntegrable (fun z ↦ (2:ℝ)*max 0 (f z).re) 0 R :=
    (continuous_const.mul hp).continuousOn.circleIntegrable'
  rw [he, circleAverage_fun_sub hi2 hr.continuousOn.circleIntegrable', hmean,
    sub_zero]
  exact circleAverage_fun_smul (𝕜 := ℝ)

theorem entire_norm_le_positive_average_half {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hf0 : f 0=0) (R : ℝ) (hR : 0<R) (w : ℂ) (hw : ‖w‖<R/2) :
    ‖f w‖ ≤ 8*circleAverage (fun z ↦ max 0 (f z).re) 0 R := by
  have ha : 0≤circleAverage (fun z ↦ max 0 (f z).re) 0 R :=
    circleAverage_nonneg_of_nonneg (fun _ _ ↦ le_max_left _ _)
  have h := entire_norm_le_realpart_average hf hf0 R hR w (by linarith)
  rw [entire_abs_re_average_eq_twice_positive hf hf0 R] at h
  have hc : 2*R/(R-‖w‖)≤4 := (div_le_iff₀ (by linarith)).mpr (by linarith)
  calc
    _ ≤ (2*R/(R-‖w‖))*(2*circleAverage (fun z ↦ max 0 (f z).re) 0 R) := h
    _ ≤ 4*(2*circleAverage (fun z ↦ max 0 (f z).re) 0 R) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by ring

theorem entire_eq_zero_of_subquadratic_positive_average {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hf0 : f 0=0) (hfd : deriv f 0=0)
    (hgrowth : Tendsto (fun R : ℝ ↦ circleAverage (fun z ↦ max 0 (f z).re) 0 R/R^2)
      atTop (𝓝 0)) (w : ℂ) : f w=0 := by
  have hd : HasDerivAt f 0 0 := by simpa only [hfd] using (hf 0).hasDerivAt
  have ho := (hasDerivAt_iff_isLittleO.mp hd).norm_right
  simp only [smul_zero, sub_zero, hf0] at ho
  have hlim : Tendsto (fun R : ℝ ↦ 32*‖w‖^2*
      (circleAverage (fun z ↦ max 0 (f z).re) 0 R/R^2)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hgrowth.const_mul (32*‖w‖^2)
  have hle : ∀ᶠ R : ℝ in atTop, ‖f w‖≤32*‖w‖^2*
      (circleAverage (fun z ↦ max 0 (f z).re) 0 R/R^2) := by
    filter_upwards [eventually_gt_atTop (2*‖w‖+1)] with R hR
    have hRpos : 0<R := by linarith [norm_nonneg w]
    have hmaps : MapsTo f (ball 0 (R/2))
        (closedBall (f 0) (8*circleAverage (fun z ↦ max 0 (f z).re) 0 R)) := by
      intro z hz
      rw [mem_closedBall, hf0, dist_zero_right]
      exact entire_norm_le_positive_average_half hf hf0 R hRpos z
        (by simpa only [mem_ball_iff_norm, sub_zero] using hz)
    have hs := Complex.dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO (n := 1)
      hf.differentiableOn hmaps (by simpa only [hf0, sub_zero, pow_one] using ho)
      (z := w) (by simpa only [mem_ball_iff_norm, sub_zero] using
        (show ‖w‖<R/2 by linarith))
    simp only [hf0, dist_zero_right] at hs
    apply hs.trans_eq
    norm_num only [Nat.reduceAdd]
    field_simp [ne_of_gt hRpos]
    ring
  exact norm_eq_zero.mp (le_antisymm (ge_of_tendsto hlim hle) (norm_nonneg _))

end ReciprocalXi

