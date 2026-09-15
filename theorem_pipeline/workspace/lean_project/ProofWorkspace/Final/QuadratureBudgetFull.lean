import ProofWorkspace.Final.XiGridTailFull
import ProofWorkspace.Final.DensityAliasBoundsFull
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Concrete error budget for the actual infinite quadrature grid

Explicit integral majorants turn the proved alias estimate into a numerical
bound. All constants are derived from actual Xi and elementary inequalities.
-/

noncomputable section
open MeasureTheory Set
namespace ReciprocalXi

theorem reciprocalTransform_norm_le_two_central (u : ℝ) (hu : |u| ≤ 3) :
    ‖reciprocalTransform u‖ ≤ 2 := by
  have hu' := abs_le.mp hu
  have hn := xi_norm_le_real_wide (1 / 2) (by norm_num) (by norm_num)
  have hd := xi_re_ge_wide_rectangle ((1 + (u : ℂ)) / 2)
    (by simp; linarith) (by simp; linarith) (by simp)
  have hd' := hd.trans (Complex.re_le_norm _)
  rw [← reciprocalExtension_ofReal, reciprocalExtension_eq_xi_ratio, norm_div]
  have hn' : ‖xi (1 / 2)‖ ≤ 5 / 8 := by simpa using hn
  have hh := div_le_div₀ (by norm_num : (0 : ℝ) ≤ 5 / 8) hn'
    (by norm_num : (0 : ℝ) < 21 / 64) hd'
  norm_num at hh
  linarith

theorem reciprocalTailConstant_quarter_le : reciprocalTailConstant (1 / 4) ≤ Real.exp 16 := by
  have hn : ‖xi (1 / 2)‖ ≤ 1 := by
    have h := xi_norm_le_real_wide (1 / 2) (by norm_num) (by norm_num)
    norm_num at h
    linarith
  have hF : 4 * ‖F 0‖ = ‖xi (1 / 2)‖ := by simp [F]; ring
  have hpi : Real.log Real.pi ≤ 2 := le_trans log_pi_le_573_500 (by norm_num)
  have he : Real.exp (1 + Real.log Real.pi) ≤ 12 := by
    rw [Real.exp_add, Real.exp_log Real.pi_pos]
    nlinarith [Real.exp_one_lt_three, Real.pi_lt_four, Real.pi_pos]
  rw [reciprocalTailConstant, hF]
  calc
    _ ≤ 1 / (xiGrowthConstant (2 * (1 / 4)) * Real.exp (1 / 4)) :=
      div_le_div_of_nonneg_right hn
        (mul_pos (xiGrowthConstant_pos _) (Real.exp_pos _)).le
    _ = Real.exp (Real.exp (1 + Real.log Real.pi) + 2 + Real.log Real.pi - 1 / 4) := by
      unfold xiGrowthConstant
      rw [← Real.exp_add, one_div, ← Real.exp_neg]
      congr 1
      norm_num
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

theorem integrable_exp_neg_mul_abs (a : ℝ) (ha : 0 < a) :
    Integrable (fun u : ℝ => Real.exp (-a * |u|)) := by
  have hi : IntegrableOn (fun u : ℝ => Real.exp (-a * |u|)) (Ioi 0) := by
    exact (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr ha) 0).congr_fun
      (fun u hu => by rw [abs_of_pos hu]) measurableSet_Ioi
  have hl : IntegrableOn (fun u : ℝ => Real.exp (-a * |u|)) (Iic 0) := by
    apply (integrableOn_exp_mul_Iic ha 0).congr_fun _ measurableSet_Iic
    intro u hu
    change Real.exp (a * u) = Real.exp (-a * |u|)
    change u ≤ 0 at hu
    rw [abs_of_nonpos hu]
    congr 1
    ring
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  exact hl.union hi

theorem integral_exp_neg_mul_abs (a : ℝ) (ha : 0 < a) :
    (∫ u : ℝ, Real.exp (-a * |u|)) = 2 / a := by
  rw [integral_comp_abs (f := fun x : ℝ => Real.exp (-a * x)),
    integral_exp_mul_Ioi (neg_lt_zero.mpr ha) 0]
  simp
  ring

theorem weighted_reciprocal_integral_bound (q : ℝ) (hq0 : 0 ≤ q) (hq : q < 1 / 4) :
    (∫ u : ℝ, Real.exp (q * |u|) * ‖reciprocalTransform u‖) ≤
      12 * Real.exp (3 * q) + 2 * reciprocalTailConstant (1 / 4) / (1 / 4 - q) := by
  let c := 2 * Real.exp (3 * q)
  let C := reciprocalTailConstant (1 / 4)
  let a := (1 / 4 : ℝ) - q
  have ha : 0 < a := sub_pos.mpr hq
  have hC : 0 ≤ C := reciprocalTailConstant_nonneg _
  have hi : Integrable ((Icc (-3 : ℝ) 3).indicator (fun _ : ℝ => c)) := by
    apply (integrable_indicator_iff measurableSet_Icc).mpr
    exact (continuous_const : Continuous (fun _ : ℝ => c)).continuousOn.integrableOn_compact isCompact_Icc
  have ht := (integrable_exp_neg_mul_abs a ha).const_mul C
  have hm : ∀ u : ℝ, Real.exp (q * |u|) * ‖reciprocalTransform u‖ ≤
      (Icc (-3 : ℝ) 3).indicator (fun _ : ℝ => c) u + C * Real.exp (-a * |u|) := by
    intro u
    by_cases hu : |u| ≤ 3
    · rw [Set.indicator_of_mem (show u ∈ Icc (-3 : ℝ) 3 from abs_le.mp hu)]
      have hp := reciprocalTransform_norm_le_two_central u hu
      have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu hq0)
      have hh := mul_le_mul he hp (norm_nonneg _) (Real.exp_pos _).le
      rw [mul_comm q 3] at hh
      have hn : 0 ≤ C * Real.exp (-a * |u|) := by positivity
      dsimp [c]
      nlinarith
    · rw [Set.indicator_of_notMem (show u ∉ Icc (-3 : ℝ) 3 by
        simpa only [mem_Icc, ← abs_le] using hu), zero_add]
      have hp := reciprocalTransform_norm_le_exp_of_abs_three_le u (1 / 4) (le_of_not_ge hu)
      calc
        _ ≤ Real.exp (q * |u|) * (C * Real.exp (-((1 / 4) * |u|))) :=
          mul_le_mul_of_nonneg_left hp (Real.exp_pos _).le
        _ = _ := by
          rw [mul_left_comm, ← Real.exp_add]
          congr 2
          dsimp [a]
          ring
  have h := integral_mono (integrable_exp_norm_reciprocalTransform q) (hi.add ht) hm
  simp only [Pi.add_apply] at h
  rw [integral_add hi ht, integral_indicator measurableSet_Icc,
    integral_const_mul C (fun u : ℝ => Real.exp (-a * |u|)),
    integral_exp_neg_mul_abs a ha] at h
  have hv : (∫ _ : ℝ in Icc (-3 : ℝ) 3, c) = 6 * c := by norm_num
  rw [hv] at h
  convert h using 1
  dsimp [c, C, a]
  ring

theorem weighted_reciprocal_integral_hundredth_le (q : ℝ)
    (hq0 : 0 ≤ q) (hq : q ≤ 1 / 100) :
    (∫ u : ℝ, Real.exp (q * |u|) * ‖reciprocalTransform u‖) ≤ Real.exp 20 := by
  have hb := weighted_reciprocal_integral_bound q hq0 (by linarith)
  have hc := reciprocalTailConstant_quarter_le
  have hc0 := reciprocalTailConstant_nonneg (1 / 4)
  have he : Real.exp (3 * q) ≤ 3 :=
    (Real.exp_le_exp.mpr (by linarith : 3 * q ≤ 1)).trans Real.exp_one_lt_three.le
  have ht : 2 * reciprocalTailConstant (1 / 4) / (1 / 4 - q) ≤
      9 * reciprocalTailConstant (1 / 4) := by
    apply (div_le_iff₀ (by linarith : 0 < 1 / 4 - q)).mpr
    nlinarith
  have h16 : 17 ≤ Real.exp (16 : ℝ) := by linarith [Real.add_one_le_exp (16 : ℝ)]
  have h4 : 16 ≤ Real.exp (4 : ℝ) := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) Real.exp_one_gt_two.le 4
    rw [← Real.exp_nat_mul] at hh
    norm_num at hh
    exact hh
  calc
    _ ≤ 36 + 9 * Real.exp 16 := by linarith
    _ ≤ 16 * Real.exp 16 := by linarith
    _ ≤ Real.exp 4 * Real.exp 16 := mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; norm_num

theorem ten_pow_85_le_exp_200 : (10 : ℝ) ^ 85 ≤ Real.exp 200 := by
  have hl := (ratExp_scaled_enclosure (231 / 100) 3 12 (by norm_num) (by norm_num)
    (by norm_num)).1
  have hnum : (10 : ℝ) ≤ (ratExpScaledLower (231 / 100) 3 12 : ℝ) := by
    norm_num [ratExpScaledLower, ratExpTaylor, ratExpError,
      Finset.sum_range_succ, Nat.factorial]
  have h10 : (10 : ℝ) ≤ Real.exp (231 / 100) := by simpa using hnum.trans hl
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 10) h10 85
  rw [← Real.exp_nat_mul] at hp
  exact hp.trans (Real.exp_le_exp.mpr (by norm_num))

theorem densityAliasAmplitude_le_exp24 (z : ℂ)
    (hr : |z.re| ≤ 4) (hi : |z.im| ≤ 1 / 100) :
    densityAliasAmplitude z ≤ Real.exp 24 := by
  have hJ := weighted_reciprocal_integral_hundredth_le |z.im| (abs_nonneg _) hi
  have he := Real.exp_le_exp.mpr hr
  have hp : (5 : ℝ) / (2 * Real.pi) ≤ 1 :=
    (div_le_one (by positivity)).mpr (by linarith [Real.pi_gt_three])
  unfold densityAliasAmplitude
  calc
    _ ≤ (5 * Real.exp 4) / (2 * Real.pi) * Real.exp 20 := by gcongr
    _ = (5 / (2 * Real.pi)) * (Real.exp 4 * Real.exp 20) := by ring
    _ ≤ 1 * (Real.exp 4 * Real.exp 20) := mul_le_mul_of_nonneg_right hp (by positivity)
    _ = _ := by rw [one_mul, ← Real.exp_add]; norm_num

/-- The actual infinite trapezoid rule at h=1/40 has error less than one
quarter of the source's 10^-85 budget throughout the stated rectangle. -/
theorem infiniteTrapezoid_error_grid_lt (z : ℂ)
    (hr : |z.re| ≤ 4) (hi : |z.im| ≤ 1 / 100) :
    ‖infiniteTrapezoid z (1 / 40) - complexDensity z‖ < 1 / (4 * (10 : ℝ) ^ 85) := by
  have hA := densityAliasAmplitude_le_exp24 z hr hi
  have he240 : 2 ≤ Real.exp (240 : ℝ) := by linarith [Real.add_one_le_exp (240 : ℝ)]
  have hep : Real.exp (240 : ℝ) ≤ Real.exp (2 * Real.pi / (1 / 40)) :=
    Real.exp_le_exp.mpr (by linarith [Real.pi_gt_three])
  have hd : Real.exp (240 : ℝ) / 2 ≤ Real.exp (2 * Real.pi / (1 / 40)) - 1 := by linarith
  have heq : 2 * Real.exp 24 / (Real.exp 240 / 2) = 4 * Real.exp (-216) := by
    calc
      _ = 4 * (Real.exp 24 / Real.exp 240) := by ring
      _ = 4 * Real.exp ((24 : ℝ) - 240) := by rw [Real.exp_sub]
      _ = _ := by norm_num
  have hnum := ten_pow_85_le_exp_200
  have h16 : 16 < Real.exp (16 : ℝ) := by linarith [Real.add_one_le_exp (16 : ℝ)]
  have h216 : 16 * (10 : ℝ) ^ 85 < Real.exp 216 := by
    calc
      _ ≤ 16 * Real.exp 200 := mul_le_mul_of_nonneg_left hnum (by norm_num)
      _ < Real.exp 16 * Real.exp 200 := mul_lt_mul_of_pos_right h16 (Real.exp_pos _)
      _ = _ := by rw [← Real.exp_add]; norm_num
  calc
    _ ≤ 2 * densityAliasAmplitude z / (Real.exp (2 * Real.pi / (1 / 40)) - 1) :=
      infiniteTrapezoid_error_le z (1 / 40) (by norm_num)
    _ ≤ 2 * Real.exp 24 / (Real.exp 240 / 2) :=
      div_le_div₀ (by positivity) (by linarith) (by positivity) hd
    _ = 4 * Real.exp (-216) := heq
    _ < _ := by
      rw [Real.exp_neg, ← div_eq_mul_inv]
      apply (div_lt_div_iff₀ (Real.exp_pos _) (by positivity : 0 < 4 * (10 : ℝ) ^ 85)).mpr
      nlinarith

end ReciprocalXi
