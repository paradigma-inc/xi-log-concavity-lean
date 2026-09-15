import ProofWorkspace.Final.PolynomialBoundsFull
import ProofWorkspace.Final.RecordedMarginsFull

/-!
# From checked recorded margins to compact curvature, conditional on enclosures

The arithmetic facts are theorems. The analytic enclosures remain hypotheses.
No result here asserts those hypotheses for the reciprocal-Xi density.
-/

noncomputable section
namespace ReciprocalXi

def recordedMarginAt (i : Fin 318) : RecordedMargin :=
  recordedMargins.get ⟨i.val, by rw [recordedMargins_length]; exact i.isLt⟩

theorem recordedMarginAt_mem (i : Fin 318) : recordedMarginAt i ∈ recordedMargins :=
  List.get_mem recordedMargins _

def recordedConstantLower (i : Fin 318) : ℝ :=
  ((recordedMarginAt i).q0 : ℝ) / (10 : ℝ) ^ (recordedMarginAt i).scale

def recordedOffUpper (i : Fin 318) : ℝ :=
  ((recordedMarginAt i).off : ℝ) / (10 : ℝ) ^ (recordedMarginAt i).scale

def recordedErrorUpper (i : Fin 318) : ℝ :=
  ((recordedMarginAt i).err : ℝ) / (10 : ℝ) ^ (recordedMarginAt i).scale

/-- This strict margin is proved for every recorded panel, not assumed. -/
theorem recorded_bounds_strict_margin (i : Fin 318) :
    recordedOffUpper i + recordedErrorUpper i < recordedConstantLower i := by
  have h := recorded_margin_pos (recordedMarginAt i) (recordedMarginAt_mem i)
  change 0 < recordedConstantLower i - recordedOffUpper i - recordedErrorUpper i at h
  linarith

/-- Finite certificate arithmetic + actual enclosure hypotheses yield physical
curvature positivity on the complete compact interval. -/
theorem compact_curvature_positive_of_recorded_enclosures
    (g0 g1 g2 : ℝ → ℝ) (p : Fin 318 → Polynomial ℝ) (e : Fin 318 → ℝ)
    (he : ∀ i, 0 ≤ e i)
    (herrors : ∀ i x, |panelCoordinate i.val x| ≤ 1 →
      |g0 x - (p i).eval (panelCoordinate i.val x)| ≤ e i ∧
      |(1 / 200) * g1 x - (p i).derivative.eval (panelCoordinate i.val x)| ≤ e i ∧
      |(1 / 200 : ℝ) ^ 2 * g2 x -
        (p i).derivative.derivative.eval (panelCoordinate i.val x)| ≤ e i)
    (hconstant : ∀ i, recordedConstantLower i ≤ (curvaturePolynomial (p i)).coeff 0)
    (hoff : ∀ i, coefficientNorm ((curvaturePolynomial (p i)).erase 0) ≤ recordedOffUpper i)
    (herr : ∀ i, polynomialCurvatureError (p i) (e i) ≤ recordedErrorUpper i)
    (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ 318 / 100) :
    0 < curvatureJet (g0 x) (g1 x) (g2 x) := by
  apply compact_curvature_positive_of_panels g0 g1 g2 p e he herrors ?_ x hx0 hx
  intro i
  have hm := recorded_bounds_strict_margin i
  have hq := hconstant i
  have hn := hoff i
  have hr := herr i
  linarith

end ReciprocalXi
