import ProofWorkspace.Final.CurvatureBoundsFull
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Whole-panel polynomial curvature bounds

The bounds below hold at every real point with |z| <= 1. They do not infer
analytic derivative errors from samples and do not certify the source JSON's
enclosure claims. Those are explicit inputs to the conditional theorems.
-/

noncomputable section
namespace ReciprocalXi

/-- Sum of absolute values of all nonzero coefficients. -/
def coefficientNorm (p : Polynomial ℝ) : ℝ :=
  ∑ i ∈ p.support, |p.coeff i|

theorem coefficientNorm_nonneg (p : Polynomial ℝ) : 0 ≤ coefficientNorm p := by
  exact Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- An evaluation bound for the entire normalized panel, not a sampling bound. -/
theorem abs_eval_le_coefficientNorm (p : Polynomial ℝ) (z : ℝ) (hz : |z| ≤ 1) :
    |p.eval z| ≤ coefficientNorm p := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  calc
    |∑ i ∈ p.support, p.coeff i * z ^ i| ≤
        ∑ i ∈ p.support, |p.coeff i * z ^ i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ coefficientNorm p := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_pow]
      exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (abs_nonneg z) hz)
        (abs_nonneg (p.coeff i))).trans_eq (mul_one _)

/-- The nonconstant coefficient norm has exactly the source certificate's form. -/
theorem coefficientNorm_erase_zero (p : Polynomial ℝ) :
    coefficientNorm (p.erase 0) = ∑ i ∈ p.support.erase 0, |p.coeff i| := by
  unfold coefficientNorm
  rw [Polynomial.support_erase]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Polynomial.erase_ne p 0 i (Finset.ne_of_mem_erase hi)]

theorem eval_eq_constant_add_erase (p : Polynomial ℝ) (z : ℝ) :
    p.eval z = p.coeff 0 + (p.erase 0).eval z := by
  have h := congrArg (Polynomial.eval z) (p.monomial_add_erase 0)
  simpa using h.symm

/-- Coefficient-wise control supplies a lower bound on every point of a panel. -/
theorem constant_sub_coefficientNorm_le_eval
    (p : Polynomial ℝ) (z : ℝ) (hz : |z| ≤ 1) :
    p.coeff 0 - coefficientNorm (p.erase 0) ≤ p.eval z := by
  have h := (abs_le.mp (abs_eval_le_coefficientNorm (p.erase 0) z hz)).1
  rw [eval_eq_constant_add_erase]
  linarith

def curvaturePolynomial (p : Polynomial ℝ) : Polynomial ℝ :=
  p.derivative ^ 2 - p * p.derivative.derivative

theorem curvaturePolynomial_eval (p : Polynomial ℝ) (z : ℝ) :
    (curvaturePolynomial p).eval z =
      curvatureJet (p.eval z) (p.derivative.eval z) (p.derivative.derivative.eval z) := by
  simp [curvaturePolynomial, curvatureJet]

/-- A sufficient positive coefficient margin implies positive true curvature,
provided each of the three normalized derivative errors is bounded by e. -/
theorem curvature_positive_of_polynomial_panel
    (p : Polynomial ℝ) (z g0 g1 g2 e : ℝ) (hz : |z| ≤ 1) (he : 0 ≤ e)
    (h0 : |g0 - p.eval z| ≤ e)
    (h1 : |g1 - p.derivative.eval z| ≤ e)
    (h2 : |g2 - p.derivative.derivative.eval z| ≤ e)
    (hmargin :
      e * (2 * coefficientNorm p.derivative + coefficientNorm p +
        coefficientNorm p.derivative.derivative) + 2 * e ^ 2 <
      (curvaturePolynomial p).coeff 0 -
        coefficientNorm ((curvaturePolynomial p).erase 0)) :
    0 < curvatureJet g0 g1 g2 := by
  have hpoly := constant_sub_coefficientNorm_le_eval (curvaturePolynomial p) z hz
  rw [curvaturePolynomial_eval] at hpoly
  have h := curvatureJet_positive_of_margin
    (p.eval z) (p.derivative.eval z) (p.derivative.derivative.eval z)
    (g0 - p.eval z) (g1 - p.derivative.eval z)
    (g2 - p.derivative.derivative.eval z) e
    (coefficientNorm p) (coefficientNorm p.derivative)
    (coefficientNorm p.derivative.derivative) he
    (coefficientNorm_nonneg _) (coefficientNorm_nonneg _) (coefficientNorm_nonneg _)
    (abs_eval_le_coefficientNorm _ z hz) (abs_eval_le_coefficientNorm _ z hz)
    (abs_eval_le_coefficientNorm _ z hz) h0 h1 h2 (hmargin.trans_le hpoly)
  simpa only [add_sub_cancel] using h

/-- This is the real quantity bounded above by a panel's error entry. -/
def polynomialCurvatureError (p : Polynomial ℝ) (e : ℝ) : ℝ :=
  e * (2 * coefficientNorm p.derivative + coefficientNorm p +
    coefficientNorm p.derivative.derivative) + 2 * e ^ 2

/-- A bridge from three certified bounds to the whole-panel theorem. Merely
recording q0/off/err in a JSON file does not discharge the enclosure hypotheses. -/
theorem curvature_positive_of_enclosed_panel
    (p : Polynomial ℝ) (z g0 g1 g2 e q0 off err : ℝ)
    (hz : |z| ≤ 1) (he : 0 ≤ e)
    (h0 : |g0 - p.eval z| ≤ e)
    (h1 : |g1 - p.derivative.eval z| ≤ e)
    (h2 : |g2 - p.derivative.derivative.eval z| ≤ e)
    (hq0 : q0 ≤ (curvaturePolynomial p).coeff 0)
    (hoff : coefficientNorm ((curvaturePolynomial p).erase 0) ≤ off)
    (herr : polynomialCurvatureError p e ≤ err)
    (hmargin : off + err < q0) :
    0 < curvatureJet g0 g1 g2 := by
  apply curvature_positive_of_polynomial_panel p z g0 g1 g2 e hz he h0 h1 h2
  unfold polynomialCurvatureError at herr
  linarith

/-- Normalizing x = c + delta*z scales curvature by delta squared. -/
theorem curvatureJet_scaled (g0 g1 g2 delta : ℝ) :
    curvatureJet g0 (delta * g1) (delta ^ 2 * g2) =
      delta ^ 2 * curvatureJet g0 g1 g2 := by
  unfold curvatureJet
  ring

theorem curvatureJet_positive_of_scaled
    (g0 g1 g2 delta : ℝ)
    (h : 0 < curvatureJet g0 (delta * g1) (delta ^ 2 * g2)) :
    0 < curvatureJet g0 g1 g2 := by
  rw [curvatureJet_scaled] at h
  exact pos_of_mul_pos_right h (sq_nonneg delta)

/-- The normalized coordinate for panels of radius 1/200. -/
def panelCoordinate (i : ℕ) (x : ℝ) : ℝ :=
  200 * x - (2 * (i : ℝ) + 1)

theorem panelCoordinate_eq_rescale (i : ℕ) (x : ℝ) :
    panelCoordinate i x = (x - (2 * (i : ℝ) + 1) / 200) / (1 / 200) := by
  unfold panelCoordinate
  ring

/-- Adjacent closed panels cover the whole interval, including both endpoints. -/
theorem uniformPanels_cover (n : ℕ) (x : ℝ) (hx0 : 0 ≤ x)
    (hx : x ≤ ((n + 1 : ℕ) : ℝ) / 100) :
    ∃ i : ℕ, i ≤ n ∧ |panelCoordinate i x| ≤ 1 := by
  induction n with
  | zero =>
    refine ⟨0, le_rfl, ?_⟩
    norm_num [panelCoordinate] at *
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  | succ n ih =>
    by_cases hleft : x ≤ ((n + 1 : ℕ) : ℝ) / 100
    · obtain ⟨i, hi, hzi⟩ := ih hleft
      exact ⟨i, Nat.le_trans hi (Nat.le_succ n), hzi⟩
    · refine ⟨n + 1, le_rfl, ?_⟩
      push_neg at hleft
      norm_num [panelCoordinate, Nat.cast_add, Nat.cast_one] at *
      exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Exact coverage of the 318 recorded panels, not a floating-point check. -/
theorem recordedPanels_cover (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ 318 / 100) :
    ∃ i : Fin 318, |panelCoordinate i.val x| ≤ 1 := by
  obtain ⟨i, hi, hzi⟩ := uniformPanels_cover 317 x hx0 (by norm_num at *; exact hx)
  exact ⟨⟨i, by omega⟩, hzi⟩

/-- Assemble all panel certificates into compact-interval curvature positivity.
The three errors refer to derivatives in the normalized coordinate; the output
uses physical-coordinate derivative data g1 and g2. -/
theorem compact_curvature_positive_of_panels
    (g0 g1 g2 : ℝ → ℝ) (p : Fin 318 → Polynomial ℝ) (e : Fin 318 → ℝ)
    (he : ∀ i, 0 ≤ e i)
    (herrors : ∀ i x, |panelCoordinate i.val x| ≤ 1 →
      |g0 x - (p i).eval (panelCoordinate i.val x)| ≤ e i ∧
      |(1 / 200) * g1 x - (p i).derivative.eval (panelCoordinate i.val x)| ≤ e i ∧
      |(1 / 200 : ℝ) ^ 2 * g2 x -
        (p i).derivative.derivative.eval (panelCoordinate i.val x)| ≤ e i)
    (hmargins : ∀ i, polynomialCurvatureError (p i) (e i) <
      (curvaturePolynomial (p i)).coeff 0 -
        coefficientNorm ((curvaturePolynomial (p i)).erase 0))
    (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ 318 / 100) :
    0 < curvatureJet (g0 x) (g1 x) (g2 x) := by
  obtain ⟨i, hzi⟩ := recordedPanels_cover x hx0 hx
  obtain ⟨h0, h1, h2⟩ := herrors i x hzi
  exact curvatureJet_positive_of_scaled _ _ _ (1 / 200)
    (curvature_positive_of_polynomial_panel (p i) (panelCoordinate i.val x)
      (g0 x) ((1 / 200) * g1 x) ((1 / 200 : ℝ) ^ 2 * g2 x) (e i)
      hzi (he i) h0 h1 h2 (hmargins i))

end ReciprocalXi
