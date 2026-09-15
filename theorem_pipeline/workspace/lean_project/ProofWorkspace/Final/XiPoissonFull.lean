import ProofWorkspace.Final.ShiftedFourierFull
import ProofWorkspace.Final.ComplexDensityFull
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Poisson summation for the actual reciprocal-Xi quadrature

Both the sampled function and its Fourier transform have proved decay.
The resulting infinite trapezoid identity has no unproved summability or
quadrature hypotheses.
-/

noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped Topology FourierTransform
namespace ReciprocalXi

def quadratureInput (z : ℂ) (h x : ℝ) : ℂ :=
  reciprocalTransform (h * x) * Complex.exp (-Complex.I * z * (h * x : ℝ))

theorem continuous_quadratureInput (z : ℂ) (h : ℝ) :
    Continuous (quadratureInput z h) := by
  have hc := continuous_reciprocalTransform.comp
    (by fun_prop : Continuous (fun x : ℝ => h * x))
  exact hc.mul (by fun_prop)

theorem exponential_bound_isBigO_rpow {f : ℝ → ℂ} {C a : ℝ} (ha : 0 < a)
    (hf : ∀ᶠ x in cocompact ℝ, ‖f x‖ ≤ C * Real.exp (-a * |x|)) (b : ℝ) :
    f =O[cocompact ℝ] (fun x : ℝ => |x| ^ b) := by
  have h1 : f =O[cocompact ℝ] (fun x : ℝ => Real.exp (-a * |x|)) := by
    refine Asymptotics.IsBigO.of_bound C ?_
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hf
  have ht : Tendsto (fun x : ℝ => |x|) (cocompact ℝ) atTop := by
    simpa only [Real.norm_eq_abs] using (tendsto_norm_cocompact_atTop (E := ℝ))
  exact h1.trans ((isLittleO_exp_neg_mul_rpow_atTop ha b).isBigO.comp_tendsto ht)

theorem quadratureInput_isBigO_rpow (z : ℂ) (h : ℝ) (hh : 0 < h) (b : ℝ) :
    quadratureInput z h =O[cocompact ℝ] (fun x : ℝ => |x| ^ b) := by
  apply exponential_bound_isBigO_rpow (a := 1) (C :=
    5 * Real.exp |z.re| * reciprocalTailConstant (1 / h + |z.im|)) (by norm_num)
  have ht : Tendsto (fun x : ℝ => |x|) (cocompact ℝ) atTop := by
    simpa only [Real.norm_eq_abs] using (tendsto_norm_cocompact_atTop (E := ℝ))
  filter_upwards [ht.eventually (eventually_ge_atTop (3 / h))] with x hx
  have hx' : 3 ≤ |h * x| := by
    rw [abs_mul, abs_of_pos hh]
    exact (div_le_iff₀ hh).mp hx |>.trans_eq (mul_comm _ _)
  have he : (1 / h) * |h * x| = |x| := by
    rw [abs_mul, abs_of_pos hh]
    field_simp
  have hb := stripFourierKernel_norm_le_exp_tail z (h * x) 0 (1 / h) hx' (by norm_num)
  simpa only [stripFourierKernel, quadratureInput, Complex.ofReal_zero,
    zero_mul, add_zero, reciprocalExtension_ofReal, he, neg_one_mul] using hb

theorem fourier_quadratureInput (z : ℂ) (h y : ℝ) (hh : 0 < h) :
    𝓕 (quadratureInput z h) y = (h⁻¹ : ℝ) •
      ∫ u : ℝ, reciprocalTransform u *
        Complex.exp (-Complex.I * (z + ((2 * Real.pi * y / h : ℝ) : ℂ)) * (u : ℂ)) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  calc
    _ = ∫ x : ℝ, reciprocalTransform (h * x) *
        Complex.exp (-Complex.I * (z + ((2 * Real.pi * y / h : ℝ) : ℂ)) * (h * x : ℝ)) := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      simp only [quadratureInput, smul_eq_mul]
      rw [mul_comm _ (reciprocalTransform (h * x) * _), mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast
      have hhC : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
      field_simp [hhC]
      ring
    _ = _ := by
      have he := Measure.integral_comp_mul_left (fun u : ℝ => reciprocalTransform u *
        Complex.exp (-Complex.I * (z + ((2 * Real.pi * y / h : ℝ) : ℂ)) * (u : ℂ))) h
      simpa only [abs_of_pos hh, abs_inv] using he

theorem fourier_quadratureInput_norm_le (z : ℂ) (h y : ℝ) (hh : 0 < h) :
    ‖𝓕 (quadratureInput z h) y‖ ≤
      (h⁻¹ * 5 * Real.exp |z.re| *
        (∫ u : ℝ, Real.exp (|z.im| * |u|) * ‖reciprocalTransform u‖)) *
        Real.exp (-(2 * Real.pi / h) * |y|) := by
  let a : ℝ := 2 * Real.pi / h
  have ha : 0 < a := by dsimp [a]; positivity
  have he : -|z.re + 2 * Real.pi * y / h| ≤ |z.re| - a * |y| := by
    have ht := abs_add_le (z.re + a * y) (-z.re)
    have hid : z.re + a * y + -z.re = a * y := by ring
    rw [hid, abs_mul, abs_of_pos ha, abs_neg] at ht
    have hid' : 2 * Real.pi * y / h = a * y := by dsimp [a]; ring
    rw [hid']
    linarith
  have hJ : 0 ≤ ∫ u : ℝ, Real.exp (|z.im| * |u|) * ‖reciprocalTransform u‖ :=
    integral_nonneg (fun u => by positivity)
  rw [fourier_quadratureInput z h y hh, norm_smul,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hh)]
  have hb := inverseFourierIntegral_norm_le_exp (z + ((2 * Real.pi * y / h : ℝ) : ℂ))
  simp only [Complex.add_re, Complex.ofReal_re, Complex.add_im,
    Complex.ofReal_im, add_zero] at hb
  calc
    _ ≤ h⁻¹ * ((5 * Real.exp (-|z.re + 2 * Real.pi * y / h|)) *
        (∫ u : ℝ, Real.exp (|z.im| * |u|) * ‖reciprocalTransform u‖)) := by
      exact mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hh.le)
    _ ≤ h⁻¹ * ((5 * Real.exp (|z.re| - a * |y|)) *
        (∫ u : ℝ, Real.exp (|z.im| * |u|) * ‖reciprocalTransform u‖)) := by
      gcongr
    _ = _ := by rw [sub_eq_add_neg, Real.exp_add]; dsimp [a]; simp only [neg_mul]; ring

theorem fourier_quadratureInput_isBigO_rpow (z : ℂ) (h : ℝ) (hh : 0 < h) (b : ℝ) :
    (𝓕 (quadratureInput z h)) =O[cocompact ℝ] (fun x : ℝ => |x| ^ b) := by
  apply exponential_bound_isBigO_rpow (a := 2 * Real.pi / h) (C :=
    h⁻¹ * 5 * Real.exp |z.re| *
      (∫ u : ℝ, Real.exp (|z.im| * |u|) * ‖reciprocalTransform u‖))
    (by positivity)
  exact Filter.Eventually.of_forall (fun y => fourier_quadratureInput_norm_le z h y hh)

theorem poisson_quadratureInput (z : ℂ) (h : ℝ) (hh : 0 < h) :
    (∑' n : ℤ, quadratureInput z h n) =
      ∑' n : ℤ, (h⁻¹ : ℝ) •
        ∫ u : ℝ, reciprocalTransform u *
          Complex.exp (-Complex.I * (z + ((2 * Real.pi * (n : ℝ) / h : ℝ) : ℂ)) *
            (u : ℂ)) := by
  have hp := Real.tsum_eq_tsum_fourier_of_rpow_decay (continuous_quadratureInput z h)
    (by norm_num : (1 : ℝ) < 2) (quadratureInput_isBigO_rpow z h hh (-2))
    (fourier_quadratureInput_isBigO_rpow z h hh (-2)) 0
  simp_rw [fourier_quadratureInput z h _ hh] at hp
  simpa using hp

theorem summable_quadratureInput (z : ℂ) (h : ℝ) (hh : 0 < h) :
    Summable (fun n : ℤ => quadratureInput z h n) := by
  exact summable_of_isBigO (Real.summable_abs_int_rpow (by norm_num : (1 : ℝ) < 2))
    ((quadratureInput_isBigO_rpow z h hh (-2)).comp_tendsto Int.tendsto_coe_cofinite)

def infiniteTrapezoid (z : ℂ) (h : ℝ) : ℂ :=
  (h / (2 * Real.pi)) • ∑' n : ℤ, quadratureInput z h n

/-- Exact alias identity for the actual normalized infinite trapezoid rule.
All convergence and Poisson hypotheses have been discharged. -/
theorem infiniteTrapezoid_eq_tsum_complexDensity (z : ℂ) (h : ℝ) (hh : 0 < h) :
    infiniteTrapezoid z h =
      ∑' n : ℤ, complexDensity (z + ((2 * Real.pi / h : ℝ) : ℂ) * (n : ℂ)) := by
  rw [infiniteTrapezoid, poisson_quadratureInput z h hh, ← tsum_const_smul'']
  apply tsum_congr
  intro n
  have hs : (h / (2 * Real.pi)) * h⁻¹ = (2 * Real.pi)⁻¹ := by
    field_simp [hh.ne', Real.pi_ne_zero]
  have he : ((2 * Real.pi * (n : ℝ) / h : ℝ) : ℂ) =
      ((2 * Real.pi / h : ℝ) : ℂ) * (n : ℂ) := by
    push_cast
    ring
  rw [smul_smul, hs, Complex.real_smul, he, complexDensity]
  push_cast
  ring

end ReciprocalXi
