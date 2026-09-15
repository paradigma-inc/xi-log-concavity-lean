import ProofWorkspace.Final.XiPairedProductFull
import Mathlib.Analysis.Normed.Group.Tannery

set_option autoImplicit false
noncomputable section
open Set Metric Filter Topology
namespace ReciprocalXi

def F_pairLogMajorantTerm (R : ℝ) (z : FPositiveZeroOccurrence) : ℝ :=
  Real.log (1+R^2*(‖F_pairRoot z‖^2)⁻¹)

theorem F_pairLogMajorantTerm_nonneg (R : ℝ) (z : FPositiveZeroOccurrence) :
    0 ≤ F_pairLogMajorantTerm R z := by
  apply Real.log_nonneg
  exact le_add_of_nonneg_right (by positivity)

theorem F_pairLogMajorantTerm_le (R : ℝ) (z : FPositiveZeroOccurrence) :
    F_pairLogMajorantTerm R z ≤ R^2*(‖F_pairRoot z‖^2)⁻¹ := by
  have h := Real.log_le_sub_one_of_pos
    (by positivity : (0:ℝ)<1+R^2*(‖F_pairRoot z‖^2)⁻¹)
  simpa only [add_sub_cancel_left] using h

theorem summable_F_pairLogMajorantTerm (R : ℝ) : Summable (F_pairLogMajorantTerm R) :=
  Summable.of_nonneg_of_le (F_pairLogMajorantTerm_nonneg R) (F_pairLogMajorantTerm_le R)
    (summable_F_pairRoot_inv_norm_sq.mul_left (R^2))

def F_pairLogMajorant (R : ℝ) : ℝ := ∑' z, F_pairLogMajorantTerm R z

theorem F_pairLogMajorant_nonneg (R : ℝ) : 0 ≤ F_pairLogMajorant R :=
  tsum_nonneg (F_pairLogMajorantTerm_nonneg R)

theorem norm_F_pairedProduct_le_exp (R : ℝ) (hR : 0 ≤ R) (w : ℂ) (hw : ‖w‖ ≤ R) :
    ‖F_pairedProduct w‖ ≤ Real.exp (F_pairLogMajorant R) := by
  apply le_of_tendsto ((continuous_norm.tendsto _).comp (multipliable_F_pairFactors w).hasProd)
  filter_upwards with s
  calc
    ‖∏ z ∈ s, (1+F_pairTerm z w)‖ ≤ ∏ z ∈ s, (1+R^2*(‖F_pairRoot z‖^2)⁻¹) := by
      apply (Finset.norm_prod_le s _).trans
      apply Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _)
      intro z hz
      calc
        _ ≤ 1+‖F_pairTerm z w‖ := by simpa using norm_add_le (1:ℂ) (F_pairTerm z w)
        _ ≤ _ := by
          rw [norm_F_pairTerm]
          gcongr
    _ = Real.exp (∑ z ∈ s, F_pairLogMajorantTerm R z) := by
      rw [Real.exp_sum]
      apply Finset.prod_congr rfl
      intro z hz
      exact (Real.exp_log (by positivity)).symm
    _ ≤ Real.exp (F_pairLogMajorant R) := Real.exp_le_exp.mpr
      ((summable_F_pairLogMajorantTerm R).sum_le_tsum s
        (fun z _ ↦ F_pairLogMajorantTerm_nonneg R z))

theorem F_pairLogMajorantTerm_div_sq_tendsto (z : FPositiveZeroOccurrence) :
    Tendsto (fun R : ℝ ↦ F_pairLogMajorantTerm R z/R^2) atTop (𝓝 0) := by
  let a : ℝ := (‖F_pairRoot z‖^2)⁻¹
  have ha : 0 < a := by exact inv_pos.mpr (sq_pos_of_pos (norm_pos_iff.mpr (F_pairRoot_ne_zero z)))
  have ht : Tendsto (fun R : ℝ ↦ a*R^2+1) atTop atTop :=
    (Filter.Tendsto.const_mul_atTop ha (tendsto_pow_atTop (by norm_num : (2:ℕ)≠0))).atTop_add
      tendsto_const_nhds
  have h := (Real.tendsto_pow_log_div_mul_add_atTop a⁻¹ (-a⁻¹) 1
    (ne_of_gt (inv_pos.mpr ha))).comp ht
  convert h using 1
  ext R
  simp only [Function.comp_apply, pow_one, F_pairLogMajorantTerm]
  change Real.log (1+R^2*a)/R^2 = Real.log (a*R^2+1)/(a⁻¹*(a*R^2+1)+ -a⁻¹)
  congr 1
  · ring
  · field_simp [ne_of_gt ha]
    ring

theorem F_pairLogMajorant_div_sq_tendsto :
    Tendsto (fun R : ℝ ↦ F_pairLogMajorant R/R^2) atTop (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence summable_F_pairRoot_inv_norm_sq
    F_pairLogMajorantTerm_div_sq_tendsto (f := fun R z ↦ F_pairLogMajorantTerm R z/R^2)
    (g := fun _ ↦ (0:ℝ)) (by
      filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR z
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (F_pairLogMajorantTerm_nonneg R z)
        (sq_nonneg R))]
      exact (div_le_iff₀ (sq_pos_of_pos hR)).mpr (by
        simpa only [mul_comm] using F_pairLogMajorantTerm_le R z))
  simpa only [tsum_zero, F_pairLogMajorant, tsum_div_const] using h

end ReciprocalXi

