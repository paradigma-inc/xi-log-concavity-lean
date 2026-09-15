import ProofWorkspace.Final.XiFourierRealFull
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Entire extension of the actual inverse Fourier density

All integrability and differentiation hypotheses are discharged using the
proved actual exponentially weighted reciprocal-transform estimates.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace ReciprocalXi

def complexDensityIntegrand (n : ℕ) (z : ℂ) (u : ℝ) : ℂ :=
  (-Complex.I * (u : ℂ)) ^ n * reciprocalTransform u *
    Complex.exp (-Complex.I * z * (u : ℂ))

def entireDensityJet (n : ℕ) (z : ℂ) : ℂ :=
  (∫ u : ℝ, complexDensityIntegrand n z u) / (2 * (Real.pi : ℂ))

def complexDensity (z : ℂ) : ℂ :=
  (∫ u : ℝ, reciprocalTransform u * Complex.exp (-Complex.I * z * (u : ℂ))) /
    (2 * (Real.pi : ℂ))

theorem continuous_complexDensityIntegrand (n : ℕ) (z : ℂ) :
    Continuous (complexDensityIntegrand n z) := by
  have hc := continuous_reciprocalTransform
  unfold complexDensityIntegrand
  fun_prop

theorem norm_complexDensityIntegrand_le (n : ℕ) (z : ℂ) (u q : ℝ)
    (hz : ‖z‖ ≤ q) :
    ‖complexDensityIntegrand n z u‖ ≤
      (n.factorial : ℝ) * Real.exp ((q + 1) * |u|) * ‖reciprocalTransform u‖ := by
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  have hp := (div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp |u| (abs_nonneg _) n)
  have he : ‖Complex.exp (-Complex.I * z * (u : ℂ))‖ ≤ Real.exp (q * |u|) := by
    apply (Complex.norm_exp_le_exp_norm _).trans
    apply Real.exp_le_exp.mpr
    simpa only [norm_mul, norm_neg, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs] using
      mul_le_mul_of_nonneg_right hz (abs_nonneg u)
  simp only [complexDensityIntegrand, norm_mul, norm_pow, norm_neg,
    Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul]
  calc
    _ ≤ (Real.exp |u| * (n.factorial : ℝ)) * ‖reciprocalTransform u‖ *
        Real.exp (q * |u|) := by gcongr
    _ = _ := by
      rw [show (q + 1) * |u| = |u| + q * |u| by ring, Real.exp_add]
      ring

theorem integrable_complexDensity_bound (n : ℕ) (q : ℝ) :
    Integrable (fun u : ℝ =>
      (n.factorial : ℝ) * Real.exp ((q + 1) * |u|) * ‖reciprocalTransform u‖) := by
  have h := (integrable_weighted_reciprocalTransform (q + 1)).norm.const_mul
    (n.factorial : ℝ)
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_assoc] using h

/-- Every integral jet converges absolutely at every complex argument. -/
theorem integrable_complexDensityIntegrand (n : ℕ) (z : ℂ) :
    Integrable (complexDensityIntegrand n z) := by
  apply (integrable_complexDensity_bound n ‖z‖).mono'
  · exact (continuous_complexDensityIntegrand n z).aestronglyMeasurable
  · exact Eventually.of_forall (fun u => norm_complexDensityIntegrand_le n z u ‖z‖ le_rfl)

theorem integrable_complexDensity_integrand (z : ℂ) :
    Integrable (fun u : ℝ => reciprocalTransform u *
      Complex.exp (-Complex.I * z * (u : ℂ))) := by
  simpa only [complexDensityIntegrand, pow_zero, one_mul] using
    (show Integrable (fun u : ℝ => complexDensityIntegrand 0 z u) from
      integrable_complexDensityIntegrand 0 z)

theorem hasDerivAt_complexDensityIntegrand (n : ℕ) (z : ℂ) (u : ℝ) :
    HasDerivAt (fun w : ℂ => complexDensityIntegrand n w u)
      (complexDensityIntegrand (n + 1) z u) z := by
  have h := (((hasDerivAt_id z).const_mul (-Complex.I)).mul_const (u : ℂ)).cexp.const_mul
    ((-Complex.I * (u : ℂ)) ^ n * reciprocalTransform u)
  convert h using 1
  simp only [complexDensityIntegrand, pow_succ, mul_one, id_eq]
  ring

/-- Differentiation under the actual integral, locally dominated on a complex
unit ball by one of the already proved integrable exponential weights. -/
theorem hasDerivAt_entireDensityJet (n : ℕ) (z : ℂ) :
    HasDerivAt (entireDensityJet n) (entireDensityJet (n + 1) z) z := by
  have hh := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun w u => complexDensityIntegrand n w u)
    (F' := fun w u => complexDensityIntegrand (n + 1) w u)
    (bound := fun u : ℝ => ((n + 1).factorial : ℝ) *
      Real.exp (((‖z‖ + 1) + 1) * |u|) * ‖reciprocalTransform u‖)
    (s := Metric.ball z 1) (x₀ := z) (μ := volume)
    (Metric.ball_mem_nhds z (by norm_num : (0 : ℝ) < 1))
    (Eventually.of_forall (fun w =>
      (continuous_complexDensityIntegrand n w).aestronglyMeasurable))
    (integrable_complexDensityIntegrand n z)
    (continuous_complexDensityIntegrand (n + 1) z).aestronglyMeasurable
    (Eventually.of_forall (fun u => by
      intro w hw
      exact norm_complexDensityIntegrand_le (n + 1) w u (‖z‖ + 1)
        (norm_le_norm_add_const_of_dist_le (Metric.mem_ball.mp hw).le)))
    (integrable_complexDensity_bound (n + 1) (‖z‖ + 1))
    (Eventually.of_forall (fun u w _ => hasDerivAt_complexDensityIntegrand n w u))
  exact hh.2.div_const (2 * (Real.pi : ℂ))

theorem entireDensityJet_zero : entireDensityJet 0 = complexDensity := by
  funext z
  simp [entireDensityJet, complexDensityIntegrand, complexDensity]

/-- The complex definition agrees exactly with the actual real density. -/
theorem complexDensity_ofReal (x : ℝ) : complexDensity (x : ℂ) = (density x : ℂ) :=
  (density_eq_complex_integral x).symm

theorem hasDerivAt_complexDensity (z : ℂ) :
    HasDerivAt complexDensity
      ((∫ u : ℝ, (-Complex.I * (u : ℂ)) * reciprocalTransform u *
        Complex.exp (-Complex.I * z * (u : ℂ))) / (2 * (Real.pi : ℂ))) z := by
  have h := hasDerivAt_entireDensityJet 0 z
  simpa only [entireDensityJet_zero, entireDensityJet, complexDensityIntegrand,
    zero_add, pow_one] using h

/-- The actual inverse Fourier density extends to an entire function. -/
theorem differentiable_complexDensity : Differentiable ℂ complexDensity :=
  fun z => (hasDerivAt_complexDensity z).differentiableAt

theorem deriv_entireDensityJet (n : ℕ) :
    deriv (entireDensityJet n) = entireDensityJet (n + 1) := by
  funext z
  exact (hasDerivAt_entireDensityJet n z).deriv

theorem iterated_deriv_complexDensity_eq_entireDensityJet (n : ℕ) :
    deriv^[n] complexDensity = entireDensityJet n := by
  induction n with
  | zero => exact entireDensityJet_zero.symm
  | succ n ih => rw [Function.iterate_succ_apply', ih, deriv_entireDensityJet]

/-- All orders of complex differentiation have their actual integral formula. -/
theorem iterated_deriv_complexDensity_eq_integral (n : ℕ) (z : ℂ) :
    (deriv^[n] complexDensity) z =
      (∫ u : ℝ, (-Complex.I * (u : ℂ)) ^ n * reciprocalTransform u *
        Complex.exp (-Complex.I * z * (u : ℂ))) / (2 * (Real.pi : ℂ)) := by
  rw [iterated_deriv_complexDensity_eq_entireDensityJet]
  rfl

end ReciprocalXi
