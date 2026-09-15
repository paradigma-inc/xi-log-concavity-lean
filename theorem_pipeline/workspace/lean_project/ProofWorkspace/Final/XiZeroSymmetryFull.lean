import ProofWorkspace.Final.XiZeroGeometryFull
import ProofWorkspace.Final.XiStripBoundsFull
import ProofWorkspace.Final.XiFourierRealFull
import Mathlib.Analysis.Calculus.Deriv.Star

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open Filter
open scoped Topology
open scoped ComplexConjugate
namespace ReciprocalXi

theorem thetaMellinIntegrand_conj (s : ℂ) (t : ℝ) (ht : 0 < t) :
    thetaMellinIntegrand (conj s) t = conj (thetaMellinIntegrand s t) := by
  have ha : (t:ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg ht.le]
    exact ne_of_lt Real.pi_pos
  have hp : (t:ℂ)^(conj s-1) = conj ((t:ℂ)^(s-1)) := by
    simpa only [map_sub, map_one, Complex.conj_ofReal] using
      Complex.cpow_conj (t:ℂ) (s-1) ha
  unfold thetaMellinIntegrand
  rw [hp]
  simp only [map_mul, Complex.conj_ofReal]

theorem thetaMellinIntegral_conj (s : ℂ) :
    conj (∫ t : ℝ in Ioi 1, thetaMellinIntegrand s t) =
      ∫ t : ℝ in Ioi 1, thetaMellinIntegrand (conj s) t := by
  rw [← integral_conj]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  exact (thetaMellinIntegrand_conj s t (lt_trans zero_lt_one ht)).symm

theorem completedRiemannZeta₀_conj_wide (s : ℂ) (hs0 : -1 ≤ s.re) (hs1 : s.re ≤ 2) :
    completedRiemannZeta₀ (conj s) = conj (completedRiemannZeta₀ s) := by
  rw [completedRiemannZeta₀_eq_thetaMellin_wide s hs0 hs1,
    completedRiemannZeta₀_eq_thetaMellin_wide (conj s) hs0 hs1]
  simp only [map_div₀, map_add, thetaMellinIntegral_conj, map_sub, map_one, map_ofNat]

theorem xi_conj_central (s : ℂ) (hs0 : 0 ≤ s.re) (hs1 : s.re ≤ 1) :
    xi (conj s) = conj (xi s) := by
  unfold xi
  rw [completedRiemannZeta₀_conj_wide s (by linarith) (by linarith)]
  simp only [map_div₀, map_add, map_mul, map_sub, map_one, map_ofNat]

theorem F_conj_of_im_bound (z : ℂ) (hz : |z.im| ≤ 1) : F (conj z) = conj (F z) := by
  let s : ℂ := 1/2+Complex.I*z/2
  have hre : s.re = (1-z.im)/2 := by
    simp [s, Complex.mul_re]
    ring
  have hb := abs_le.mp hz
  have hs0 : 0 ≤ s.re := by rw [hre]; linarith [hb.2]
  have hs1 : s.re ≤ 1 := by rw [hre]; linarith [hb.1]
  have he : (1/2+Complex.I*conj z/2:ℂ) = 1-conj s := by
    simp only [s, map_add, map_div₀, map_mul, map_one, map_ofNat, Complex.conj_I]
    ring
  change xi (1/2+Complex.I*conj z/2)/4 = conj (xi s/4)
  rw [he, xi_one_sub, xi_conj_central s hs0 hs1]
  simp only [map_div₀, map_ofNat]

theorem F_zero_conj (z : ℂ) (hz : F z = 0) : F (conj z) = 0 := by
  rw [F_conj_of_im_bound z (F_zero_im_bound z hz).le, hz, map_zero]

theorem analyticAt_conj_reflection {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) :
    AnalyticAt ℂ (conj ∘ f ∘ conj) (conj z) := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt] at hf ⊢
  have ht : Tendsto conj (𝓝 (conj z)) (𝓝 z) := by
    simpa only [Complex.conj_conj] using (Complex.continuous_conj.tendsto (conj z))
  filter_upwards [ht.eventually hf] with w hw
  simpa only [Complex.conj_conj] using hw.conj_conj

theorem F_conj (z : ℂ) : F (conj z) = conj (F z) := by
  have hg : AnalyticOnNhd ℂ (conj ∘ F ∘ conj) univ := by
    intro w _
    simpa only [Complex.conj_conj] using
      analyticAt_conj_reflection (analyticOnNhd_F (conj w) (mem_univ _))
  have he : F =ᶠ[𝓝 (0:ℂ)] (conj ∘ F ∘ conj) := by
    filter_upwards [Metric.ball_mem_nhds (0:ℂ) (by norm_num : (0:ℝ)<1)] with w hw
    have hn : ‖w‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hw
    have hi : |w.im| ≤ 1 := (Complex.abs_im_le_norm w).trans hn.le
    simp only [Function.comp_apply, F_conj_of_im_bound w hi, Complex.conj_conj]
  have hfun := analyticOnNhd_F.eq_of_eventuallyEq hg he
  have h := congrFun hfun (conj z)
  simpa only [Function.comp_apply, Complex.conj_conj] using h

theorem F_order_neg (z : ℂ) : analyticOrderAt F (-z) = analyticOrderAt F z := by
  have h := analyticOrderAt_comp_of_deriv_ne_zero (f:=F) (g:=fun w : ℂ => -w)
    (z₀:=z) (by fun_prop) (by simp)
  have he : (F ∘ fun w : ℂ => -w) = F := funext F_even
  rw [he] at h
  exact h.symm

theorem F_orderNat_conj (z : ℂ) : analyticOrderNatAt F (conj z) = analyticOrderNatAt F z := by
  obtain ⟨g, hg, hg0, hfg⟩ :=
    ((analyticOnNhd_F z (mem_univ _)).analyticOrderNatAt_eq_iff
      (F_analyticOrderAt_ne_top z)).mp (rfl : analyticOrderNatAt F z = analyticOrderNatAt F z)
  apply ((analyticOnNhd_F (conj z) (mem_univ _)).analyticOrderNatAt_eq_iff
    (F_analyticOrderAt_ne_top (conj z))).mpr
  refine ⟨conj ∘ g ∘ conj, analyticAt_conj_reflection hg, ?_, ?_⟩
  · simpa only [Function.comp_apply, Complex.conj_conj, map_ne_zero] using hg0
  · have ht : Tendsto conj (𝓝 (conj z)) (𝓝 z) := by
      simpa only [Complex.conj_conj] using (Complex.continuous_conj.tendsto (conj z))
    filter_upwards [ht.eventually hfg] with w hw
    have h := congrArg conj hw
    simpa only [F_conj, Complex.conj_conj, smul_eq_mul, map_mul, map_pow, map_sub,
      Function.comp_apply] using h

theorem F_orderNat_neg (z : ℂ) : analyticOrderNatAt F (-z) = analyticOrderNatAt F z :=
  congrArg ENat.toNat (F_order_neg z)

end ReciprocalXi
