import ProofWorkspace.Final.XiDefinitionFull
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Tactic

/-!
# Actual real-axis xi bounds

These statements concern mathlib's actual zeta and Gamma functions, not a
surrogate model or an enclosure assumption. They supply analytic prerequisites
for control of the reciprocal transform on the real Fourier axis.
-/

noncomputable section
open MeasureTheory Set
namespace ReciprocalXi

def realZetaSeries (s : ℝ) : ℝ := ∑' n : ℕ, 1 / (n + 1 : ℝ) ^ s

theorem summable_realZetaSeries (s : ℝ) (hs : 1 < s) :
    Summable (fun n : ℕ => 1 / (n + 1 : ℝ) ^ s) := by
  have h := (Real.summable_one_div_nat_add_rpow 1 s).mpr hs
  have heq : (fun n : ℕ => 1 / |(n : ℝ) + 1| ^ s) =
      (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ s) := by
    funext n
    rw [abs_of_nonneg (by positivity)]
  exact heq ▸ h

theorem riemannZeta_ofReal_eq_realZetaSeries (s : ℝ) (hs : 1 < s) :
    riemannZeta (s : ℂ) = (realZetaSeries s : ℂ) := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using hs)]
  unfold realZetaSeries
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_cpow (by positivity)]
  norm_cast

theorem one_le_realZetaSeries (s : ℝ) (hs : 1 < s) : 1 ≤ realZetaSeries s := by
  have h := (summable_realZetaSeries s hs).le_tsum 0 (fun n _ => by positivity)
  simpa [realZetaSeries] using h

/-- The real Gamma-factor formula for actual xi on the convergent-series range. -/
theorem xi_ofReal_eq_of_one_lt (s : ℝ) (hs : 1 < s) :
    xi (s : ℂ) =
      ((s * (s - 1) * (Real.pi ^ (-s / 2) * Real.Gamma (s / 2) * realZetaSeries s) / 2 : ℝ) : ℂ) := by
  have h0 : (s : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_trans zero_lt_one hs))
  have h1 : (s : ℂ) ≠ 1 := by exact_mod_cast (ne_of_gt hs)
  have hg : Complex.Gammaℝ (s : ℂ) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by simpa using (lt_trans zero_lt_one hs))
  have hz := riemannZeta_def_of_ne_zero h0
  have hc : completedRiemannZeta (s : ℂ) =
      riemannZeta (s : ℂ) * Complex.Gammaℝ (s : ℂ) := (eq_div_iff hg).mp hz |>.symm
  rw [xi_eq_completed (s : ℂ) h0 h1, hc, riemannZeta_ofReal_eq_realZetaSeries s hs]
  rw [Complex.Gammaℝ_def]
  have hgamma : Complex.Gamma ((s : ℂ) / 2) = (Real.Gamma (s / 2) : ℂ) := by
    convert Complex.Gamma_ofReal (s / 2) using 1
    push_cast
    rfl
  have hpow : (Real.pi : ℂ) ^ (-(s : ℂ) / 2) = ((Real.pi ^ (-s / 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow Real.pi_pos.le]
    norm_cast
  rw [hgamma, hpow]
  push_cast
  ring

theorem xi_re_pos_of_one_lt (s : ℝ) (hs : 1 < s) : 0 < (xi (s : ℂ)).re := by
  rw [xi_ofReal_eq_of_one_lt s hs, Complex.ofReal_re]
  have hseries : 0 < realZetaSeries s := lt_of_lt_of_le zero_lt_one (one_le_realZetaSeries s hs)
  have hgamma : 0 < Real.Gamma (s / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hpow : 0 < Real.pi ^ (-s / 2) := Real.rpow_pos_of_pos Real.pi_pos _
  exact div_pos (mul_pos (mul_pos (by linarith) (by linarith))
    (mul_pos (mul_pos hpow hgamma) hseries)) (by norm_num)

theorem xi_ne_zero_of_one_lt (s : ℝ) (hs : 1 < s) : xi (s : ℂ) ≠ 0 := by
  intro h
  have hp := xi_re_pos_of_one_lt s hs
  rw [h, Complex.zero_re] at hp
  exact lt_irrefl 0 hp

/-- Drop all but the first positive Dirichlet-series term. -/
theorem xi_re_lower_bound_of_one_lt (s : ℝ) (hs : 1 < s) :
    s * (s - 1) * (Real.pi ^ (-s / 2) * Real.Gamma (s / 2)) / 2 ≤ (xi (s : ℂ)).re := by
  rw [xi_ofReal_eq_of_one_lt s hs, Complex.ofReal_re]
  have hseries := one_le_realZetaSeries s hs
  have hgamma := (Real.Gamma_pos_of_pos (by linarith : 0 < s / 2)).le
  have hpow := (Real.rpow_pos_of_pos Real.pi_pos (-s / 2)).le
  have hcoeff : 0 ≤ s * (s - 1) * (Real.pi ^ (-s / 2) * Real.Gamma (s / 2)) / 2 := by
    exact div_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith))
      (mul_nonneg hpow hgamma)) (by norm_num)
  have h := mul_le_mul_of_nonneg_left hseries hcoeff
  nlinarith

/-- A quantitative Euler-integral lower bound, obtained by integrating over
the unit interval [T,T+1]. No asymptotic or Gamma estimate is assumed. -/
theorem gamma_lower_bound_from_unit_interval (s T : ℝ) (hs : 1 ≤ s) (hT : 0 < T) :
    Real.exp (-(T + 1)) * T ^ (s - 1) ≤ Real.Gamma s := by
  have hfi := Real.GammaIntegral_convergent (lt_of_lt_of_le zero_lt_one hs)
  have hsub : Icc T (T + 1) ⊆ Ioi (0 : ℝ) := by
    intro t ht
    exact lt_of_lt_of_le hT ht.1
  have hpoint : ∀ t ∈ Icc T (T + 1),
      Real.exp (-(T + 1)) * T ^ (s - 1) ≤ Real.exp (-t) * t ^ (s - 1) := by
    intro t ht
    exact mul_le_mul (Real.exp_le_exp.mpr (by linarith [ht.2]))
      (Real.rpow_le_rpow hT.le ht.1 (by linarith))
      (Real.rpow_nonneg hT.le _) (Real.exp_pos _).le
  have hsmall := setIntegral_ge_of_const_le_real (μ := volume) measurableSet_Icc
    (by simp : volume (Icc T (T + 1)) ≠ ⊤) hpoint (hfi.mono_set hsub)
  have hvol : volume.real (Icc T (T + 1)) = 1 := by
    rw [Real.volume_real_Icc_of_le (by linarith)]
    ring
  rw [hvol, mul_one] at hsmall
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun t : ℝ => Real.exp (-t) * t ^ (s - 1)) := by
    apply (ae_restrict_iff' measurableSet_Ioi).mpr
    exact Filter.Eventually.of_forall fun t ht =>
      mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (le_of_lt ht) _)
  have hlarge := setIntegral_mono_set hfi hnonneg
    (Filter.Eventually.of_forall fun t ht => hsub ht)
  rw [Real.Gamma_eq_integral (lt_of_lt_of_le zero_lt_one hs)]
  exact hsmall.trans hlarge

/-- Explicit lower bound on actual xi, with freely chosen positive integration
location T. Varying T permits arbitrarily strong eventual exponential growth. -/
theorem xi_re_lower_bound_from_unit_interval (s T : ℝ) (hs : 2 ≤ s) (hT : 0 < T) :
    s * (s - 1) * (Real.pi ^ (-s / 2) *
      (Real.exp (-(T + 1)) * T ^ (s / 2 - 1))) / 2 ≤ (xi (s : ℂ)).re := by
  have hgamma := gamma_lower_bound_from_unit_interval (s / 2) T (by linarith) hT
  have hpi : 0 ≤ Real.pi ^ (-s / 2) := (Real.rpow_pos_of_pos Real.pi_pos _).le
  have hfactor : 0 ≤ s * (s - 1) := mul_nonneg (by linarith) (by linarith)
  apply le_trans _ (xi_re_lower_bound_of_one_lt s (by linarith))
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgamma hpi) hfactor)
    (by norm_num)

/-- Functional-equation reflection supplies positivity on the other outside
half-line as well. The central interval is not covered by this theorem. -/
theorem xi_re_pos_of_lt_zero (s : ℝ) (hs : s < 0) : 0 < (xi (s : ℂ)).re := by
  have h := xi_re_pos_of_one_lt (1 - s) (by linarith)
  have heq : xi ((1 - s : ℝ) : ℂ) = xi (s : ℂ) := by
    push_cast
    exact xi_one_sub (s : ℂ)
  rwa [heq] at h

/-- An explicit, positive growth constant; no asymptotic constants are hidden. -/
def xiGrowthConstant (r : ℝ) : ℝ :=
  Real.exp (-(Real.exp (2 * r + Real.log Real.pi) + 1) - (2 * r + Real.log Real.pi))

theorem xiGrowthConstant_pos (r : ℝ) : 0 < xiGrowthConstant r := Real.exp_pos _

/-- Actual xi eventually dominates an exponential of every chosen rate. This
is derived from Euler's integral, not from an assumed Stirling asymptotic. -/
theorem xi_re_ge_exponential (s r : ℝ) (hs : 2 ≤ s) :
    xiGrowthConstant r * Real.exp (r * s) ≤ (xi (s : ℂ)).re := by
  let T := Real.exp (2 * r + Real.log Real.pi)
  have hT : 0 < T := Real.exp_pos _
  have hbound := xi_re_lower_bound_from_unit_interval s T hs hT
  have hid : Real.pi ^ (-s / 2) * (Real.exp (-(T + 1)) * T ^ (s / 2 - 1)) =
      xiGrowthConstant r * Real.exp (r * s) := by
    rw [Real.rpow_def_of_pos Real.pi_pos, Real.rpow_def_of_pos hT]
    dsimp [T, xiGrowthConstant]
    rw [Real.log_exp, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [hid] at hbound
  have hcoeff : 1 ≤ s * (s - 1) / 2 := by nlinarith
  have hval : 0 ≤ xiGrowthConstant r * Real.exp (r * s) := by
    exact mul_nonneg (xiGrowthConstant_pos r).le (Real.exp_pos _).le
  have h := mul_le_mul_of_nonneg_right hcoeff hval
  nlinarith

def reciprocalTailConstant (r : ℝ) : ℝ :=
  4 * ‖F 0‖ / (xiGrowthConstant (2 * r) * Real.exp r)

theorem reciprocalTailConstant_nonneg (r : ℝ) : 0 ≤ reciprocalTailConstant r := by
  exact div_nonneg (mul_nonneg (by norm_num) (norm_nonneg _))
    (mul_pos (xiGrowthConstant_pos _) (Real.exp_pos _)).le

/-- A certified bound on the actual reciprocal transform, for every chosen
exponential rate, on the positive tail. -/
theorem reciprocalTransform_norm_le_exp_of_three_le (u r : ℝ) (hu : 3 ≤ u) :
    ‖reciprocalTransform u‖ ≤ reciprocalTailConstant r * Real.exp (-(r * u)) := by
  have h := xi_re_ge_exponential ((1 + u) / 2) (2 * r) (by linarith)
  have he : Real.exp (2 * r * ((1 + u) / 2)) = Real.exp r * Real.exp (r * u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at h
  have hcast : (((1 + u) / 2 : ℝ) : ℂ) = (1 + (u : ℂ)) / 2 := by push_cast; rfl
  rw [hcast] at h
  have hn : (xi ((1 + (u : ℂ)) / 2)).re ≤ ‖xi ((1 + (u : ℂ)) / 2)‖ :=
    (le_abs_self _).trans (Complex.abs_re_le_norm _)
  have hden : xiGrowthConstant (2 * r) * Real.exp r * Real.exp (r * u) / 4 ≤
      ‖F (Complex.I * (u : ℂ))‖ := by
    rw [F_imaginary_axis, norm_div]
    norm_num
    nlinarith
  have hp : 0 < xiGrowthConstant (2 * r) * Real.exp r * Real.exp (r * u) / 4 := by
    exact div_pos (mul_pos (mul_pos (xiGrowthConstant_pos _) (Real.exp_pos _))
      (Real.exp_pos _)) (by norm_num)
  rw [reciprocalTransform, norm_div]
  calc
    ‖F 0‖ / ‖F (Complex.I * (u : ℂ))‖ ≤
        ‖F 0‖ / (xiGrowthConstant (2 * r) * Real.exp r * Real.exp (r * u) / 4) :=
      div_le_div_of_nonneg_left (norm_nonneg _) hp hden
    _ = reciprocalTailConstant r * Real.exp (-(r * u)) := by
      rw [Real.exp_neg]
      dsimp [reciprocalTailConstant]
      field_simp

/-- Evenness extends the explicit reciprocal bound to both tails. The central
interval is deliberately not hidden inside this estimate. -/
theorem reciprocalTransform_norm_le_exp_of_abs_three_le (u r : ℝ) (hu : 3 ≤ |u|) :
    ‖reciprocalTransform u‖ ≤ reciprocalTailConstant r * Real.exp (-(r * |u|)) := by
  by_cases hsign : 0 ≤ u
  · rw [abs_of_nonneg hsign] at hu ⊢
    exact reciprocalTransform_norm_le_exp_of_three_le u r hu
  · rw [abs_of_neg (lt_of_not_ge hsign)] at hu ⊢
    simpa only [reciprocalTransform_even] using
      reciprocalTransform_norm_le_exp_of_three_le (-u) r hu

theorem continuous_F : Continuous F := by
  have hxi := differentiable_xi.continuous
  unfold F
  fun_prop

/-- Measurability uses the total inverse and does not assume central
nonvanishing. That assumption is needed for continuity, not this statement. -/
theorem measurable_reciprocalTransform : Measurable reciprocalTransform := by
  have hF := continuous_F.measurable
  unfold reciprocalTransform
  fun_prop

/-- Every exponential weight is integrable on the positive Fourier tail.
There is no remaining Xi-specific domination hypothesis in this theorem. -/
theorem integrableOn_weighted_reciprocalTransform_Ioi (q : ℝ) :
    IntegrableOn (fun u : ℝ => Real.exp (q * |u|) • reciprocalTransform u) (Ioi 3) := by
  have hmajor := (exp_neg_integrableOn_Ioi 3 (by norm_num : (0 : ℝ) < 1)).const_mul
    (reciprocalTailConstant (q + 1))
  apply hmajor.mono'
  · have hm := measurable_reciprocalTransform
    exact (by fun_prop : Measurable (fun u : ℝ =>
      Real.exp (q * |u|) • reciprocalTransform u)).aestronglyMeasurable
  · apply (ae_restrict_iff' measurableSet_Ioi).mpr
    apply Filter.Eventually.of_forall
    intro u hu
    change 3 < u at hu
    have habs : |u| = u := abs_of_pos (by linarith [hu] : 0 < u)
    have hb := reciprocalTransform_norm_le_exp_of_three_le u (q + 1) hu.le
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), habs]
    calc
      Real.exp (q * u) * ‖reciprocalTransform u‖ ≤
          Real.exp (q * u) * (reciprocalTailConstant (q + 1) *
            Real.exp (-((q + 1) * u))) :=
        mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
      _ = reciprocalTailConstant (q + 1) * Real.exp (-1 * u) := by
        rw [mul_left_comm, ← Real.exp_add]
        congr 2
        ring

/-- Reflection gives the corresponding negative-tail integrability. -/
theorem integrableOn_weighted_reciprocalTransform_Iio (q : ℝ) :
    IntegrableOn (fun u : ℝ => Real.exp (q * |u|) • reciprocalTransform u) (Iio (-3)) := by
  have h := ((Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
    (Homeomorph.neg ℝ).measurableEmbedding).2
    (integrableOn_weighted_reciprocalTransform_Ioi q)
  have hs : (fun x : ℝ => -x) ⁻¹' Ioi 3 = Iio (-3) := by
    ext x
    simp only [mem_preimage, mem_Ioi, mem_Iio]
    constructor <;> intro hx <;> linarith
  simpa only [hs, Function.comp_def, abs_neg, reciprocalTransform_even] using h

/-- Both noncompact tails are now controlled. Only the bounded central
interval remains for full reciprocal-transform integrability. -/
theorem integrableOn_weighted_reciprocalTransform_tails (q : ℝ) :
    IntegrableOn (fun u : ℝ => Real.exp (q * |u|) • reciprocalTransform u)
      (Iio (-3) ∪ Ioi 3) :=
  (integrableOn_weighted_reciprocalTransform_Iio q).union
    (integrableOn_weighted_reciprocalTransform_Ioi q)

end ReciprocalXi
