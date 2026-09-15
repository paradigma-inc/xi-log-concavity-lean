import ProofWorkspace.Final.XiGrowthFull
import Mathlib.Analysis.Complex.JensenFormula

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric MeromorphicOn Real
namespace ReciprocalXi

theorem F_divisor_eq_orderNat (R : ℝ) (z : ℂ) (hz : z ∈ closedBall 0 R) :
    divisor F (closedBall 0 R) z = (analyticOrderNatAt F z : ℤ) := by
  have ha := analyticOnNhd_F z (mem_univ z)
  have hm := (analyticOnNhd_F.mono (subset_univ (closedBall 0 R))).meromorphicOn
  rw [divisor_apply hm hz, ha.meromorphicOrderAt_eq,
    ← Nat.cast_analyticOrderNatAt (F_analyticOrderAt_ne_top z)]
  simp

theorem F_divisor_zero (R : ℝ) : divisor F (closedBall 0 R) 0 = 0 := by
  by_cases hR : 0 ≤ R
  · rw [F_divisor_eq_orderNat R 0 (by simpa)]
    have ha := (analyticOnNhd_F 0 (mem_univ 0)).analyticOrderAt_eq_zero.mpr F_zero_ne_zero
    simp [analyticOrderNatAt, ha]
  · simp [Metric.closedBall_eq_empty.mpr (lt_of_not_ge hR)]

theorem F_circleAverage_log_norm_le_factorial (R : ℝ) (n : ℕ)
    (hR : 0 < R) (hn : R+1 ≤ 2*(n:ℝ)) :
    circleAverage (fun z ↦ Real.log ‖F z‖) 0 R ≤
      Real.log (((n:ℝ)+2)^2*(n.factorial:ℝ)) := by
  have hf : (1:ℝ) ≤ n.factorial := by
    have hp := Nat.factorial_pos n
    exact_mod_cast (show 1 ≤ n.factorial by omega)
  have hb : (1:ℝ) ≤ ((n:ℝ)+2)^2*(n.factorial:ℝ) := by
    have hq : (1:ℝ) ≤ ((n:ℝ)+2)^2 := by nlinarith [Nat.cast_nonneg (α:=ℝ) n]
    exact one_le_mul_of_one_le_of_one_le hq hf
  apply circleAverage_mono_on_of_le_circle
    (circleIntegrable_log_norm_meromorphicOn
      (analyticOnNhd_F.mono (subset_univ _)).meromorphicOn)
  intro z hz
  have hzn : ‖z‖ = R := by simpa [mem_sphere_iff_norm, abs_of_pos hR] using hz
  have hg := F_norm_le_factorial z n (by rw [hzn]; exact hn)
  by_cases hz0 : F z = 0
  · simp only [hz0, norm_zero, Real.log_zero]
    exact Real.log_nonneg hb
  · apply Real.log_le_log (norm_pos_iff.mpr hz0)
    have hb0 : (0:ℝ) ≤ ((n:ℝ)+2)^2*(n.factorial:ℝ) := by positivity
    linarith

theorem F_jensen_sum_bound (R : ℝ) (n : ℕ)
    (hR : 0 < R) (hn : R+1 ≤ 2*(n:ℝ)) :
    (∑ᶠ z, (divisor F (closedBall 0 R) z : ℝ)*Real.log (R*‖z‖⁻¹)) ≤
      Real.log (((n:ℝ)+2)^2*(n.factorial:ℝ)) - Real.log ‖F 0‖ := by
  have hm := (analyticOnNhd_F.mono (subset_univ (closedBall 0 |R|))).meromorphicOn
  have hj := hm.circleAverage_log_norm (ne_of_gt hR)
  have ht := (analyticOnNhd_F 0 (mem_univ 0)).meromorphicTrailingCoeffAt_of_ne_zero F_zero_ne_zero
  have hd : (divisor F (closedBall 0 |R|) : ℂ → ℤ) =
      (divisor F (closedBall 0 R) : ℂ → ℤ) := by
    rw [abs_of_pos hR]
  rw [hd] at hj
  simp only [zero_sub, norm_neg, F_divisor_zero,
    Int.cast_zero, zero_mul, add_zero, ht] at hj
  have hu := F_circleAverage_log_norm_le_factorial R n hR hn
  linarith

def F_zeroFinset (R : ℝ) : Finset ℂ := (F_zeros_closedBall_finite R).toFinset

theorem mem_F_zeroFinset (R : ℝ) (z : ℂ) :
    z ∈ F_zeroFinset R ↔ F z = 0 ∧ ‖z‖ ≤ R := by
  simp [F_zeroFinset]

theorem F_zeroFinset_mono {R S : ℝ} (h : R ≤ S) : F_zeroFinset R ⊆ F_zeroFinset S := by
  intro z hz
  rw [mem_F_zeroFinset] at hz ⊢
  exact ⟨hz.1,hz.2.trans h⟩

theorem F_divisor_zero_of_not_mem (R : ℝ) (z : ℂ) (hz : z ∉ F_zeroFinset R) :
    divisor F (closedBall 0 R) z = 0 := by
  by_cases hb : z ∈ closedBall 0 R
  · have hzn : F z ≠ 0 := by
      intro h
      exact hz ((mem_F_zeroFinset R z).mpr ⟨h, by simpa [mem_closedBall_iff_norm] using hb⟩)
    rw [F_divisor_eq_orderNat R z hb]
    have ho : analyticOrderNatAt F z = 0 := by
      by_contra h
      exact hzn (apply_eq_zero_of_analyticOrderNatAt_ne_zero h)
    simp [ho]
  · exact Function.notMem_support.mp
      (fun h ↦ hb ((divisor F (closedBall 0 R)).supportWithinDomain h))

theorem F_jensen_finset_sum_bound (R : ℝ) (n : ℕ)
    (hR : 0 < R) (hn : R+1 ≤ 2*(n:ℝ)) :
    (∑ z ∈ F_zeroFinset R, (analyticOrderNatAt F z : ℝ)*Real.log (R*‖z‖⁻¹)) ≤
      Real.log (((n:ℝ)+2)^2*(n.factorial:ℝ)) - Real.log ‖F 0‖ := by
  classical
  have hj := F_jensen_sum_bound R n hR hn
  have hs : Function.support (fun z ↦ (divisor F (closedBall 0 R) z : ℝ)*
      Real.log (R*‖z‖⁻¹)) ⊆ (F_zeroFinset R : Set ℂ) := by
    intro z hz
    by_contra h
    have hd := F_divisor_zero_of_not_mem R z h
    simp [Function.mem_support, hd] at hz
  rw [finsum_eq_sum_of_support_subset _ hs] at hj
  convert hj using 1
  apply Finset.sum_congr rfl
  intro z hz
  rw [F_divisor_eq_orderNat R z
    (by simpa [mem_closedBall_iff_norm] using ((mem_F_zeroFinset R z).mp hz).2)]
  simp

def F_zeroCount (R : ℝ) : ℕ := ∑ z ∈ F_zeroFinset R, analyticOrderNatAt F z

theorem F_zeroCount_log_two_le (R : ℝ) (n : ℕ)
    (hR : 0 < R) (hn : R+1 ≤ 2*(n:ℝ)) :
    (F_zeroCount (R/2) : ℝ)*Real.log 2 ≤
      Real.log (((n:ℝ)+2)^2*(n.factorial:ℝ)) - Real.log ‖F 0‖ := by
  classical
  have hsub : F_zeroFinset (R/2) ⊆ F_zeroFinset R := F_zeroFinset_mono (by linarith)
  have hle : (F_zeroCount (R/2) : ℝ)*Real.log 2 ≤
      ∑ z ∈ F_zeroFinset (R/2), (analyticOrderNatAt F z : ℝ)*Real.log (R*‖z‖⁻¹) := by
    simp only [F_zeroCount, Nat.cast_sum, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro z hz
    have hz' := (mem_F_zeroFinset (R/2) z).mp hz
    have hzn : 0 < ‖z‖ := lt_trans (by norm_num) (F_zero_norm_gt_one z hz'.1)
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply Real.log_le_log (by norm_num)
    rw [← div_eq_mul_inv, le_div_iff₀ hzn]
    linarith
  apply hle.trans
  apply le_trans _ (F_jensen_finset_sum_bound R n hR hn)
  apply Finset.sum_le_sum_of_subset_of_nonneg hsub
  intro z hz _
  have hz' := (mem_F_zeroFinset R z).mp hz
  have hzn : 0 < ‖z‖ := lt_trans (by norm_num) (F_zero_norm_gt_one z hz'.1)
  apply mul_nonneg (Nat.cast_nonneg _)
  apply Real.log_nonneg
  rw [← div_eq_mul_inv, le_div_iff₀ hzn]
  simpa using hz'.2

theorem F_zeroCount_le (R : ℝ) (n : ℕ)
    (hR : 0 < R) (hn : R+1 ≤ 2*(n:ℝ)) :
    (F_zeroCount (R/2) : ℝ) ≤
      (Real.log (((n:ℝ)+2)^2*(n.factorial:ℝ)) - Real.log ‖F 0‖) / Real.log 2 := by
  exact (le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))).mpr
    (F_zeroCount_log_two_le R n hR hn)

end ReciprocalXi

