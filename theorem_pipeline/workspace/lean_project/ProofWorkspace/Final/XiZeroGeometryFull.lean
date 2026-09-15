import ProofWorkspace.Final.XiZeroStripFull
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Order

set_option autoImplicit false
noncomputable section
namespace ReciprocalXi

/-- Includes the boundary line using the established zeta nonvanishing theorem. -/
theorem xi_ne_zero_of_one_le_re (s : ℂ) (hs : 1 ≤ s.re) : xi s ≠ 0 := by
  by_cases h1 : s = 1
  · subst s
    rw [xi_one]
    norm_num
  have h0 : s ≠ 0 := by
    intro h
    simp only [h, Complex.zero_re] at hs
    linarith
  have hg : Complex.Gammaℝ s ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (lt_of_lt_of_le zero_lt_one hs)
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs
  have hc : completedRiemannZeta s = riemannZeta s * Complex.Gammaℝ s :=
    ((eq_div_iff hg).mp (riemannZeta_def_of_ne_zero h0)).symm
  rw [xi_eq_completed s h0 h1, hc]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero h0 (sub_ne_zero.mpr h1))
    (mul_ne_zero hz hg)) (by norm_num)

theorem xi_ne_zero_of_re_nonpos (s : ℂ) (hs : s.re ≤ 0) : xi s ≠ 0 := by
  have h := xi_ne_zero_of_one_le_re (1-s) (by
    simp only [Complex.sub_re, Complex.one_re]
    linarith)
  simpa only [xi_one_sub] using h

theorem xi_zero_re_bounds (s : ℂ) (hs : xi s = 0) : 0 < s.re ∧ s.re < 1 := by
  constructor
  · by_contra h
    exact xi_ne_zero_of_re_nonpos s (le_of_not_gt h) hs
  · by_contra h
    exact xi_ne_zero_of_one_le_re s (le_of_not_gt h) hs

theorem F_zero_xi (z : ℂ) (hz : F z = 0) : xi (1/2+Complex.I*z/2) = 0 := by
  exact (div_eq_zero_iff.mp hz).resolve_right (by norm_num)

theorem F_zero_im_bound (z : ℂ) (hz : F z = 0) : |z.im| < 1 := by
  have hs := xi_zero_re_bounds _ (F_zero_xi z hz)
  have he : (1/2+Complex.I*z/2:ℂ).re = (1-z.im)/2 := by
    simp [Complex.mul_re]
    ring
  rw [he] at hs
  rw [abs_lt]
  constructor <;> linarith [hs.1, hs.2]

theorem F_zero_abs_re_gt_one (z : ℂ) (hz : F z = 0) : 1 < |z.re| := by
  by_contra h
  have hr : |z.re| ≤ 1 := le_of_not_gt h
  have he : (1/2+Complex.I*z/2:ℂ).im = z.re/2 := by
    simp [Complex.mul_im]
  have hs : |(1/2+Complex.I*z/2:ℂ).im| ≤ 1/2 := by
    rw [he, abs_div]
    rw [abs_of_pos (by norm_num : (0:ℝ) < 2)]
    linarith
  exact xi_ne_zero_of_abs_im_le_half _ hs (F_zero_xi z hz)

theorem F_zero_norm_gt_one (z : ℂ) (hz : F z = 0) : 1 < ‖z‖ :=
  (F_zero_abs_re_gt_one z hz).trans_le (Complex.abs_re_le_norm z)

theorem F_zero_ne_zero : F 0 ≠ 0 := by
  intro h
  have hn := F_zero_norm_gt_one 0 h
  norm_num at hn

theorem analyticOnNhd_F : AnalyticOnNhd ℂ F Set.univ :=
  Complex.analyticOnNhd_univ_iff_differentiable.mpr differentiable_F_complex

theorem F_zero_set_closed : IsClosed {z : ℂ | F z = 0} :=
  isClosed_singleton.preimage differentiable_F_complex.continuous

theorem F_zero_set_discrete : IsDiscrete {z : ℂ | F z = 0} := by
  have h := (mem_codiscrete'.mp
    (analyticOnNhd_F.preimage_zero_mem_codiscrete F_zero_ne_zero)).2
  simpa only [Set.preimage_compl, compl_compl] using h

theorem F_zeros_closedBall_finite (R : ℝ) :
    ({z : ℂ | F z = 0} ∩ Metric.closedBall 0 R).Finite := by
  exact ((isCompact_closedBall (0:ℂ) R).inter_left F_zero_set_closed).finite
    (F_zero_set_discrete.mono Set.inter_subset_left)

theorem F_analyticOrderAt_ne_top (z : ℂ) : analyticOrderAt F z ≠ ⊤ := by
  exact analyticOnNhd_F.analyticOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (Set.mem_univ 0) (Set.mem_univ z)
    ((analyticOnNhd_F 0 (Set.mem_univ 0)).analyticOrderAt_eq_zero.mpr F_zero_ne_zero ▸
      (by simp))

theorem F_zero_set_countable : Set.Countable {z : ℂ | F z = 0} := by
  rw [← Metric.iUnion_inter_closedBall_nat {z : ℂ | F z = 0} 0]
  exact Set.countable_iUnion (fun n : ℕ => (F_zeros_closedBall_finite n).countable)

theorem F_zero_order_pos (z : ℂ) (hz : F z = 0) : 0 < analyticOrderNatAt F z := by
  have hne := (analyticOnNhd_F z (Set.mem_univ z)).analyticOrderAt_ne_zero.mpr hz
  have hcast := Nat.cast_analyticOrderNatAt (F_analyticOrderAt_ne_top z)
  apply Nat.pos_of_ne_zero
  intro hn
  rw [hn, Nat.cast_zero] at hcast
  exact hne hcast.symm

end ReciprocalXi
