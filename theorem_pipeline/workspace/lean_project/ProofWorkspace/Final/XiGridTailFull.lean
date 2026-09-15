import ProofWorkspace.Final.XiFourierRealFull
import ProofWorkspace.Final.XiStripBoundsFull
import ProofWorkspace.Final.RationalExpBoundsFull

/-!
# A concrete actual Xi bound beyond the retained Fourier grid

Exact rational exponential witnesses and a fixed interval of the Euler Gamma
integral certify the tail without a Stirling-expansion assumption.
-/

noncomputable section
namespace ReciprocalXi

theorem log_eightyfour_ge : (443 : ℝ) / 100 ≤ Real.log 84 := by
  apply (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 84)).mpr
  have h := (ratExp_scaled_enclosure (443 / 100) 5 12 (by norm_num) (by norm_num)
    (by norm_num)).2
  have hu : (ratExpScaledUpper (443 / 100) 5 12 : ℝ) ≤ 84 := by
    norm_num [ratExpScaledUpper, ratExpTaylor, ratExpError,
      Finset.sum_range_succ, Nat.factorial]
  simpa using h.trans hu

theorem log_pi_le_573_500 : Real.log Real.pi ≤ (573 : ℝ) / 500 := by
  apply (Real.log_le_iff_le_exp Real.pi_pos).mpr
  have h := (ratExp_scaled_enclosure (573 / 500) 2 12 (by norm_num) (by norm_num)
    (by norm_num)).1
  have hl : (3143 : ℝ) / 1000 ≤ (ratExpScaledLower (573 / 500) 2 12 : ℝ) := by
    norm_num [ratExpScaledLower, ratExpTaylor, ratExpError,
      Finset.sum_range_succ, Nat.factorial]
  exact (le_of_lt Real.pi_lt_d4).trans (by linarith [hl.trans h])

theorem exp_957_100_le : Real.exp ((957 : ℝ) / 100) ≤ (115599 : ℝ) / 8 := by
  have h := (ratExp_scaled_enclosure (957 / 100) 10 12 (by norm_num) (by norm_num)
    (by norm_num)).2
  have hu : (ratExpScaledUpper (957 / 100) 10 12 : ℝ) ≤ (115599 : ℝ) / 8 := by
    norm_num [ratExpScaledUpper, ratExpTaylor, ratExpError,
      Finset.sum_range_succ, Nat.factorial]
  simpa using h.trans hu

/-- A directed lower bound obtained from just the interval [84,85] in
the actual Gamma integral. No Stirling evaluation is needed for this tail. -/
theorem xi_re_ge_grid_tail (u : ℝ) (hu : 340 ≤ u) :
    Real.exp (200 + (4 / 5 : ℝ) * (u - 340)) ≤
      (xi (((1 + u) / 2 : ℝ) : ℂ)).re := by
  let s : ℝ := (1 + u) / 2
  have hs : (341 : ℝ) / 2 ≤ s := by dsimp [s]; linarith
  have hpref : Real.exp ((957 : ℝ) / 100) ≤ s * (s - 1) / 2 := by
    have hp := exp_957_100_le
    nlinarith
  have hx := xi_re_lower_bound_from_unit_interval s 84 (by linarith) (by norm_num)
  have hlog := log_eightyfour_ge
  have hpi := log_pi_le_573_500
  have he : 200 + (4 / 5 : ℝ) * (u - 340) ≤
      957 / 100 + Real.log Real.pi * (-s / 2) - 85 + Real.log 84 * (s / 2 - 1) := by
    have h1 := mul_le_mul_of_nonneg_left hpi (by linarith : 0 ≤ s / 2)
    have h2 := mul_le_mul_of_nonneg_right hlog (by linarith : 0 ≤ s / 2 - 1)
    dsimp [s] at *
    nlinarith
  calc
    _ ≤ Real.exp (957 / 100 + Real.log Real.pi * (-s / 2) - 85 +
        Real.log 84 * (s / 2 - 1)) := Real.exp_le_exp.mpr he
    _ = Real.exp (957 / 100) *
        (Real.pi ^ (-s / 2) * (Real.exp (-(84 + 1)) * (84 : ℝ) ^ (s / 2 - 1))) := by
      rw [Real.rpow_def_of_pos Real.pi_pos, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 84)]
      repeat rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ (s * (s - 1) / 2) *
        (Real.pi ^ (-s / 2) * (Real.exp (-(84 + 1)) * (84 : ℝ) ^ (s / 2 - 1))) := by
      exact mul_le_mul_of_nonneg_right hpref (by positivity)
    _ ≤ _ := by convert hx using 1; ring

theorem reciprocalTransform_grid_tail (u : ℝ) (hu : 340 ≤ |u|) :
    ‖reciprocalTransform u‖ ≤ Real.exp (-200) * Real.exp (-(4 / 5 : ℝ) * (|u| - 340)) := by
  have heven : ‖reciprocalTransform u‖ = ‖reciprocalTransform |u|‖ := by
    by_cases hp : 0 ≤ u
    · rw [abs_of_nonneg hp]
    · rw [abs_of_neg (lt_of_not_ge hp), reciprocalTransform_even]
  rw [heven, ← reciprocalExtension_ofReal, reciprocalExtension_eq_xi_ratio, norm_div]
  have hn : ‖xi (1 / 2)‖ ≤ 1 := by
    have hn := xi_norm_le_real_wide (1 / 2) (by norm_num) (by norm_num)
    norm_num at hn
    linarith
  have hl := xi_re_ge_grid_tail |u| hu
  have hc : (((1 + |u|) / 2 : ℝ) : ℂ) = (1 + ((|u| : ℝ) : ℂ)) / 2 := by push_cast; rfl
  rw [hc] at hl
  have hd := hl.trans ((le_abs_self _).trans (Complex.abs_re_le_norm _))
  calc
    _ ≤ 1 / Real.exp (200 + (4 / 5 : ℝ) * (|u| - 340)) :=
      div_le_div₀ (by norm_num) hn (Real.exp_pos _) hd
    _ = Real.exp (-200) * Real.exp (-((4 / 5 : ℝ) * (|u| - 340))) := by
      rw [Real.exp_add, one_div, mul_inv, ← Real.exp_neg, ← Real.exp_neg]
    _ = _ := by rw [neg_mul]

end ReciprocalXi
