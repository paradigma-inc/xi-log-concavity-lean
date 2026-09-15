import ProofWorkspace.Final.ComplexDensityFull
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.TaylorSeries

/-!
# Actual disk bounds, Cauchy coefficients, and Taylor truncation errors

The boundary majorant is an integral of the actual exponentially weighted
reciprocal transform. No numerical coefficient enclosure is assumed here.
-/

noncomputable section
open MeasureTheory Filter Metric
open scoped BigOperators
namespace ReciprocalXi

def densityDiskMajorant (c : ℂ) (R : ℝ) : ℝ :=
  (∫ u : ℝ, Real.exp ((|c.im| + R) * |u|) * ‖reciprocalTransform u‖) /
    (2 * Real.pi)

theorem integrable_densityDiskMajorant_integrand (c : ℂ) (R : ℝ) :
    Integrable (fun u : ℝ => Real.exp ((|c.im| + R) * |u|) * ‖reciprocalTransform u‖) := by
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
    (integrable_weighted_reciprocalTransform (|c.im| + R)).norm

theorem densityDiskMajorant_nonneg (c : ℂ) (R : ℝ) : 0 ≤ densityDiskMajorant c R := by
  apply div_nonneg _ (by positivity)
  exact integral_nonneg (fun u => mul_nonneg (Real.exp_pos _).le (norm_nonneg _))

theorem densityDiskMajorant_ofReal (c R : ℝ) :
    densityDiskMajorant (c : ℂ) R = densityDiskMajorant 0 R := by
  simp only [densityDiskMajorant, Complex.ofReal_im, Complex.zero_im, abs_zero, zero_add]

theorem complexDensity_norm_le_diskMajorant (c z : ℂ) (R : ℝ)
    (hz : z ∈ closedBall c R) : ‖complexDensity z‖ ≤ densityDiskMajorant c R := by
  have hd : ‖z - c‖ ≤ R := by simpa only [mem_closedBall, dist_eq_norm] using hz
  have hi := (Complex.abs_im_le_norm (z - c)).trans hd
  simp only [Complex.sub_im] at hi
  have hzi : |z.im| ≤ |c.im| + R := by
    have h := abs_add_le (z.im - c.im) c.im
    rw [sub_add_cancel] at h
    linarith
  have hb : ‖∫ u : ℝ, reciprocalTransform u *
      Complex.exp (-Complex.I * z * (u : ℂ))‖ ≤
      ∫ u : ℝ, Real.exp ((|c.im| + R) * |u|) * ‖reciprocalTransform u‖ := by
    apply norm_integral_le_of_norm_le (integrable_densityDiskMajorant_integrand c R)
    apply Eventually.of_forall
    intro u
    have he : ‖Complex.exp (-Complex.I * z * (u : ℂ))‖ = Real.exp (z.im * u) := by
      rw [Complex.norm_exp]
      congr 1
      simp [Complex.mul_re, Complex.mul_im]
    have hh : z.im * u ≤ (|c.im| + R) * |u| := by
      calc
        _ ≤ |z.im * u| := le_abs_self _
        _ = |z.im| * |u| := abs_mul _ _
        _ ≤ _ := mul_le_mul_of_nonneg_right hzi (abs_nonneg _)
    rw [norm_mul, he, mul_comm]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hh) (norm_nonneg _)
  unfold complexDensity densityDiskMajorant
  rw [norm_div, norm_mul, Complex.norm_ofNat, Complex.norm_of_nonneg Real.pi_pos.le]
  exact div_le_div_of_nonneg_right hb (by positivity)

/-- An actual Cauchy bound, with its boundary majorant derived from the
reciprocal-Xi Fourier integral rather than supplied as an assumption. -/
theorem complexDensity_iteratedDeriv_norm_le (n : ℕ) (c : ℂ) (R : ℝ) (hR : 0 < R) :
    ‖iteratedDeriv n complexDensity c‖ ≤
      (n.factorial : ℝ) * densityDiskMajorant c R / R ^ n := by
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR
    differentiable_complexDensity.diffContOnCl
  intro z hz
  exact complexDensity_norm_le_diskMajorant c z R (sphere_subset_closedBall hz)

def densityTaylorCoefficient (c : ℂ) (n : ℕ) : ℂ :=
  (n.factorial : ℂ)⁻¹ * iteratedDeriv n complexDensity c

theorem densityTaylorCoefficient_norm_le (c : ℂ) (n : ℕ) (R : ℝ) (hR : 0 < R) :
    ‖densityTaylorCoefficient c n‖ ≤ densityDiskMajorant c R / R ^ n := by
  have hn : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  have h := mul_le_mul_of_nonneg_left (complexDensity_iteratedDeriv_norm_le n c R hR)
    (inv_nonneg.mpr hn.le)
  unfold densityTaylorCoefficient
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  convert h using 1
  field_simp

theorem hasSum_densityTaylor (c z : ℂ) :
    HasSum (fun n : ℕ => densityTaylorCoefficient c n * (z - c) ^ n) (complexDensity z) := by
  have h := Complex.hasSum_taylorSeries_of_entire differentiable_complexDensity c z
  convert h using 1
  funext n
  simp only [densityTaylorCoefficient, smul_eq_mul]
  ring

theorem densityTaylor_term_norm_le (c z : ℂ) (n : ℕ) (R : ℝ) (hR : 0 < R) :
    ‖densityTaylorCoefficient c n * (z - c) ^ n‖ ≤
      densityDiskMajorant c R * (‖z - c‖ / R) ^ n := by
  rw [norm_mul, norm_pow]
  have h := mul_le_mul_of_nonneg_right (densityTaylorCoefficient_norm_le c n R hR)
    (pow_nonneg (norm_nonneg (z - c)) n)
  convert h using 1
  rw [div_pow]
  ring

def densityTaylorPolynomial (c : ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  ∑ n ∈ Finset.range N, densityTaylorCoefficient c n * (z - c) ^ n

/-- The actual Taylor polynomial has a geometric truncation bound throughout
every strictly smaller disk. The coefficients are actual derivatives of G. -/
theorem complexDensity_taylor_remainder_le (c z : ℂ) (R : ℝ) (N : ℕ)
    (hR : 0 < R) (hz : ‖z - c‖ < R) :
    ‖complexDensity z - densityTaylorPolynomial c N z‖ ≤
      densityDiskMajorant c R * (‖z - c‖ / R) ^ N / (1 - ‖z - c‖ / R) := by
  let q : ℝ := ‖z - c‖ / R
  have hq0 : 0 ≤ q := div_nonneg (norm_nonneg _) hR.le
  have hq1 : q < 1 := (div_lt_one hR).mpr hz
  have ht := (hasSum_nat_add_iff' N).mpr (hasSum_densityTaylor c z)
  have hg := (hasSum_geometric_of_lt_one hq0 hq1).mul_left
    (densityDiskMajorant c R * q ^ N)
  have hbound : ∀ n : ℕ,
      ‖densityTaylorCoefficient c (n + N) * (z - c) ^ (n + N)‖ ≤
        densityDiskMajorant c R * q ^ N * q ^ n := by
    intro n
    have h := densityTaylor_term_norm_le c z (n + N) R hR
    change _ ≤ densityDiskMajorant c R * q ^ (n + N) at h
    convert h using 1
    rw [pow_add]
    ring
  have h := ht.norm_le_of_bounded hg hbound
  simpa only [densityTaylorPolynomial, q, div_eq_mul_inv] using h

end ReciprocalXi
