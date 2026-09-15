import ProofWorkspace.Final.XiQuotientLogFull
import ProofWorkspace.Final.XiProductGrowthFull
import Mathlib.Analysis.Complex.ValueDistribution.FirstMainTheorem

set_option autoImplicit false
noncomputable section
open Set Metric Filter Topology Real ValueDistribution MeromorphicOn
namespace ReciprocalXi

theorem entire_logCounting_top_zero {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f univ) :
    logCounting f ⊤ = 0 := by
  rw [logCounting_top, negPart_eq_zero.mpr hf.divisor_nonneg]
  exact map_zero _

theorem F_pairedProduct_proximity_inv_le (R : ℝ) (hR : 1 ≤ R) :
    proximity F_pairedProduct⁻¹ ⊤ R ≤ proximity F_pairedProduct ⊤ R := by
  have hm : Meromorphic F_pairedProduct := fun z ↦
    (analyticOnNhd_F_pairedProduct z (mem_univ _)).meromorphicAt
  have h := characteristic_sub_characteristic_inv_of_ne_zero hm (by linarith : R≠0)
  have htc := (analyticOnNhd_F_pairedProduct 0 (mem_univ _)).meromorphicTrailingCoeffAt_of_ne_zero
    (by rw [F_pairedProduct_zero]; exact one_ne_zero)
  rw [htc, F_pairedProduct_zero, norm_one, log_one, sub_eq_zero] at h
  have hpos := logCounting_nonneg (f := F_pairedProduct⁻¹) (e := ⊤) hR
  simp only [characteristic, Pi.add_apply, entire_logCounting_top_zero analyticOnNhd_F_pairedProduct,
    Pi.zero_apply, add_zero] at h
  linarith

theorem F_pairQuotient_proximity_le (R : ℝ) (hR : 1 ≤ R) :
    proximity F_pairQuotient ⊤ R ≤ proximity F ⊤ R + proximity F_pairedProduct ⊤ R := by
  have he : F/F_pairedProduct =ᶠ[codiscrete ℂ] F_pairQuotient := by
    simpa only [F_pairQuotient] using
      toMeromorphicNFOn_eqOn_codiscrete meromorphicOn_F_div_pairedProduct
  rw [← proximity_congr_codiscrete he (by linarith : R≠0)]
  have hf : Meromorphic F := fun z ↦ (analyticOnNhd_F z (mem_univ _)).meromorphicAt
  have hp : Meromorphic F_pairedProduct := fun z ↦
    (analyticOnNhd_F_pairedProduct z (mem_univ _)).meromorphicAt
  change proximity (F*F_pairedProduct⁻¹) ⊤ R ≤ _
  exact (proximity_mul_top_le hf hp.inv R).trans
    (add_le_add_right (F_pairedProduct_proximity_inv_le R hR) _)

theorem posLog_norm_F_pairedProduct_le (R : ℝ) (hR : 0 ≤ R) (w : ℂ) (hw : ‖w‖≤R) :
    log⁺ ‖F_pairedProduct w‖ ≤ F_pairLogMajorant R := by
  have h := posLog_le_posLog (norm_nonneg _) (norm_F_pairedProduct_le_exp R hR w hw)
  simpa only [posLog_def, log_exp, max_eq_right (F_pairLogMajorant_nonneg R)] using h

theorem F_pairedProduct_proximity_le (R : ℝ) (hR : 0 ≤ R) :
    proximity F_pairedProduct ⊤ R ≤ F_pairLogMajorant R := by
  rw [proximity_top]
  apply circleAverage_mono_on_of_le_circle
  · exact circleIntegrable_posLog_norm_meromorphicOn
      (fun z _ ↦ (analyticOnNhd_F_pairedProduct z (mem_univ _)).meromorphicAt)
  · intro w hw
    apply posLog_norm_F_pairedProduct_le R hR w
    simpa only [dist_zero_right, abs_of_nonneg hR] using hw.le

def F_logGrowthBound (R : ℝ) : ℝ := (R+3)*log (R+3)

theorem F_logGrowthBound_nonneg (R : ℝ) (hR : 1≤R) : 0 ≤ F_logGrowthBound R := by
  exact mul_nonneg (by linarith) (log_nonneg (by linarith))

theorem posLog_norm_F_le (R : ℝ) (hR : 1≤R) (w : ℂ) (hw : ‖w‖≤R) :
    log⁺ ‖F w‖ ≤ F_logGrowthBound R := by
  let n : ℕ := ⌈R⌉₊
  have hn : R ≤ (n:ℝ) := Nat.le_ceil R
  have hn' : (n:ℝ) < R+1 := Nat.ceil_lt_add_one (by linarith)
  have hb := F_norm_le_factorial w n (by linarith)
  have hb' : ‖F w‖ ≤ ((n:ℝ)+2)^2*(n.factorial:ℝ) := by
    have : (0:ℝ)≤((n:ℝ)+2)^2*(n.factorial:ℝ) := by positivity
    linarith
  have hp : (1:ℝ) ≤ ((n:ℝ)+2)^2*(n.factorial:ℝ) := by
    have hf : (1:ℝ) ≤ n.factorial := by exact_mod_cast Nat.factorial_pos n
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hl := posLog_le_posLog (norm_nonneg _) hb'
  have hpabs : 1 ≤ |((n:ℝ)+2)^2*(n.factorial:ℝ)| := hp.trans (le_abs_self _)
  rw [posLog_eq_log hpabs] at hl
  apply (hl.trans (xiGrowth_log_le n)).trans
  apply mul_le_mul (by linarith : (n:ℝ)+2≤R+3)
    (log_le_log (by positivity) (by linarith))
    (log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])) (by linarith)

theorem F_proximity_le (R : ℝ) (hR : 1≤R) : proximity F ⊤ R ≤ F_logGrowthBound R := by
  rw [proximity_top]
  apply circleAverage_mono_on_of_le_circle
  · exact circleIntegrable_posLog_norm_meromorphicOn
      (fun z _ ↦ (analyticOnNhd_F z (mem_univ _)).meromorphicAt)
  · intro w hw
    apply posLog_norm_F_le R hR w
    have hw' : ‖w‖=|R| := by simpa only [mem_sphere_iff_norm, sub_zero] using hw
    rw [hw', abs_of_nonneg (by linarith)]

theorem F_pairQuotient_proximity_bound (R : ℝ) (hR : 1≤R) :
    proximity F_pairQuotient ⊤ R ≤ F_logGrowthBound R+F_pairLogMajorant R :=
  (F_pairQuotient_proximity_le R hR).trans
    (add_le_add (F_proximity_le R hR) (F_pairedProduct_proximity_le R (by linarith)))

theorem F_logGrowthBound_div_sq_tendsto :
    Tendsto (fun R : ℝ ↦ F_logGrowthBound R/R^2) atTop (𝓝 0) := by
  have hshift : Tendsto (fun R : ℝ ↦ R+3) atTop atTop := tendsto_id.atTop_add tendsto_const_nhds
  have hlog : Tendsto (fun R : ℝ ↦ log (R+3)/R) atTop (𝓝 0) := by
    have h := (tendsto_pow_log_div_mul_add_atTop 1 (-3) 1 one_ne_zero).comp hshift
    convert h using 1
    ext R
    simp only [Function.comp_apply, pow_one, one_mul]
    congr 1
    ring
  have hrat : Tendsto (fun R : ℝ ↦ (R+3)/R) atTop (𝓝 1) := by
    have h := tendsto_const_nhds.add (tendsto_id.const_div_atTop (3:ℝ))
      (a := (1:ℝ))
    simp only [add_zero] at h
    apply h.congr'
    filter_upwards [eventually_ne_atTop (0:ℝ)] with R hR
    dsimp
    field_simp
  have h := hrat.mul hlog
  simpa only [mul_zero, F_logGrowthBound, ← mul_div_mul_comm, ← pow_two] using h

theorem F_pairQuotient_proximity_div_sq_tendsto :
    Tendsto (fun R : ℝ ↦ proximity F_pairQuotient ⊤ R/R^2) atTop (𝓝 0) := by
  have h := F_logGrowthBound_div_sq_tendsto.add F_pairLogMajorant_div_sq_tendsto
  simp only [add_zero, ← add_div] at h
  apply squeeze_zero' _ _ h
  · filter_upwards with R
    exact div_nonneg (proximity_nonneg R) (sq_nonneg R)
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with R hR
    exact div_le_div_of_nonneg_right (F_pairQuotient_proximity_bound R hR) (sq_nonneg R)

theorem log_norm_F_pairQuotient (w : ℂ) :
    log ‖F_pairQuotient w‖ = log ‖F 0‖+(F_quotientLog w).re := by
  rw [F_pairQuotient_eq_exp, norm_mul, Complex.norm_exp,
    log_mul (norm_ne_zero_iff.mpr F_zero_ne_zero) (ne_of_gt (exp_pos _)), log_exp]

def F_quotientLogPositiveAverage (R : ℝ) : ℝ :=
  circleAverage (fun z ↦ max 0 (F_quotientLog z).re) 0 R

theorem F_quotientLogPositiveAverage_nonneg (R : ℝ) : 0≤F_quotientLogPositiveAverage R :=
  circleAverage_nonneg_of_nonneg (fun _ _ ↦ le_max_left _ _)

theorem F_quotientLogPositiveAverage_le (R : ℝ) :
    F_quotientLogPositiveAverage R ≤ proximity F_pairQuotient ⊤ R+|log ‖F 0‖| := by
  have hc : Continuous (fun z ↦ max 0 (F_quotientLog z).re) := by
    apply continuous_const.max
    exact Complex.continuous_re.comp differentiable_F_quotientLog.continuous
  have hi : CircleIntegrable (fun z ↦ log⁺ ‖F_pairQuotient z‖) 0 R :=
    circleIntegrable_posLog_norm_meromorphicOn
      (fun z _ ↦ (analyticOnNhd_F_pairQuotient z (mem_univ _)).meromorphicAt)
  have hiConst : CircleIntegrable (fun _ : ℂ ↦ |log ‖F 0‖|) 0 R := circleIntegrable_const _ _ _
  have h := circleAverage_mono hc.continuousOn.circleIntegrable' (hi.add hiConst)
    (fun z _ ↦ show max 0 (F_quotientLog z).re ≤ log⁺ ‖F_pairQuotient z‖+|log ‖F 0‖| by
      rw [max_le_iff]
      constructor
      · exact add_nonneg posLog_nonneg (abs_nonneg _)
      · have h1 : log ‖F_pairQuotient z‖ ≤ log⁺ ‖F_pairQuotient z‖ := le_max_right _ _
        rw [log_norm_F_pairQuotient] at h1
        linarith [neg_le_abs (log ‖F 0‖)])
  simpa only [circleAverage_add hi hiConst, circleAverage_const,
    ← proximity_top, F_quotientLogPositiveAverage] using h

theorem F_quotientLogPositiveAverage_div_sq_tendsto :
    Tendsto (fun R : ℝ ↦ F_quotientLogPositiveAverage R/R^2) atTop (𝓝 0) := by
  have hc : Tendsto (fun R : ℝ ↦ |log ‖F 0‖|/R^2) atTop (𝓝 0) :=
    (tendsto_pow_atTop (by norm_num : (2:ℕ)≠0)).const_div_atTop _
  have h := F_pairQuotient_proximity_div_sq_tendsto.add hc
  simp only [add_zero, ← add_div] at h
  apply squeeze_zero (fun R ↦ div_nonneg (F_quotientLogPositiveAverage_nonneg R) (sq_nonneg R))
    (fun R ↦ div_le_div_of_nonneg_right (F_quotientLogPositiveAverage_le R) (sq_nonneg R)) h

end ReciprocalXi

