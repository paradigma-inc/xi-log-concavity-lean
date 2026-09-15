import ProofWorkspace.Final.RealTaylorBridgeFull
import ProofWorkspace.Final.DensityConditionalFull

set_option autoImplicit false
noncomputable section
namespace ReciprocalXi

def sourcePanelCenter (i : Fin 318) : ℝ := (2*(i.val:ℝ)+1)/200

def sourcePanelPolynomial (v : ℕ → ℝ) (i : Fin 318) : Polynomial ℝ :=
  realSampledTaylorPolynomial (sourcePanelCenter i) sourcePiMidpoint v

theorem sourcePanelCenter_abs_le (i : Fin 318) : |sourcePanelCenter i| ≤ 318/100 := by
  have hi : (i.val:ℝ) ≤ 317 := by
    exact_mod_cast (show i.val ≤ 317 from Nat.le_pred_of_lt i.isLt)
  have hi0 : (0:ℝ) ≤ i.val := Nat.cast_nonneg _
  unfold sourcePanelCenter
  rw [abs_of_nonneg (by positivity)]
  linarith

theorem sourcePanelCenter_add_coordinate (i : Fin 318) (x : ℝ) :
    sourcePanelCenter i + (1/200:ℝ)*panelCoordinate i.val x = x := by
  unfold sourcePanelCenter panelCoordinate
  ring

/-- Actual density and its first two scaled derivatives are enclosed by the
source Taylor polynomial whenever all retained source samples are enclosed. -/
theorem sourcePanelPolynomial_derivative_errors (v : ℕ → ℝ)
    (hv : ∀ (k : ℕ), k ≤ 13600 →
      |(reciprocalTransform ((k:ℝ)/40)).re - v k| ≤ 2/(10:ℝ)^120)
    (i : Fin 318) (x : ℝ) (hx : |panelCoordinate i.val x| ≤ 1) :
    |density x - (sourcePanelPolynomial v i).eval (panelCoordinate i.val x)| ≤
        sourcePanelJetError ∧
    |(1/200:ℝ)*deriv density x -
        (sourcePanelPolynomial v i).derivative.eval (panelCoordinate i.val x)| ≤
        sourcePanelJetError ∧
    |(1/200:ℝ)^2*deriv (deriv density) x -
        (sourcePanelPolynomial v i).derivative.derivative.eval (panelCoordinate i.val x)| ≤
        sourcePanelJetError := by
  have h0 := normalizedComplexDensity_source_taylor_re_error_le
    (sourcePanelCenter i) (panelCoordinate i.val x) v 0 (sourcePanelCenter_abs_le i) hx
    (by norm_num) hv
  have h1 := normalizedComplexDensity_source_taylor_re_error_le
    (sourcePanelCenter i) (panelCoordinate i.val x) v 1 (sourcePanelCenter_abs_le i) hx
    (by norm_num) hv
  have h2 := normalizedComplexDensity_source_taylor_re_error_le
    (sourcePanelCenter i) (panelCoordinate i.val x) v 2 (sourcePanelCenter_abs_le i) hx
    (by norm_num) hv
  refine ⟨?_, ?_, ?_⟩
  · simpa only [iteratedDeriv_zero, normalizedComplexDensity_ofReal_re,
      sourcePanelCenter_add_coordinate, ← realSampledTaylorPolynomial_eval,
      sourcePanelPolynomial] using h0
  · simpa only [normalizedComplexDensity_deriv_re, sourcePanelCenter_add_coordinate,
      ← realSampledTaylorPolynomial_derivative_eval, sourcePanelPolynomial] using h1
  · simpa only [normalizedComplexDensity_second_deriv_re, sourcePanelCenter_add_coordinate,
      ← realSampledTaylorPolynomial_second_derivative_eval, sourcePanelPolynomial] using h2

/-- No derivative-enclosure hypothesis is needed: it is derived above. The
retained-node and three recorded coefficient-enclosure obligations remain explicit. -/
def densityCompactEnclosures_of_source_coefficients (v : ℕ → ℝ)
    (hv : ∀ (k : ℕ), k ≤ 13600 →
      |(reciprocalTransform ((k:ℝ)/40)).re - v k| ≤ 2/(10:ℝ)^120)
    (hconstant : ∀ i, recordedConstantLower i ≤
      (curvaturePolynomial (sourcePanelPolynomial v i)).coeff 0)
    (hoff : ∀ i, coefficientNorm
      ((curvaturePolynomial (sourcePanelPolynomial v i)).erase 0) ≤ recordedOffUpper i)
    (herr : ∀ i, polynomialCurvatureError (sourcePanelPolynomial v i) sourcePanelJetError ≤
      recordedErrorUpper i) : DensityCompactEnclosures where
  polynomial := sourcePanelPolynomial v
  error := fun _ => sourcePanelJetError
  error_nonneg := fun _ => sourcePanelJetError_nonneg
  derivative_errors := sourcePanelPolynomial_derivative_errors v hv
  constant_enclosure := hconstant
  nonconstant_enclosure := hoff
  curvature_error_enclosure := herr

end ReciprocalXi
