import ProofWorkspace.Final.CertificateBridgeFull
import ProofWorkspace.Final.XiSymmetryFull
import ProofWorkspace.Final.TailBoundsFull
import ProofWorkspace.Final.GlobalReductionFull
import ProofWorkspace.Final.XiFourierFull

/-!
# Explicitly conditional assembly for the actual reciprocal-Xi density

The evidence structures below state the remaining analytic enclosure obligations.
NO inhabitant of either structure is constructed in this file. Their fields
are not axioms, and a successful build is NOT a proof of the full Xi theorem.
-/

noncomputable section
namespace ReciprocalXi

/-- Required analytic compact enclosures. The finite margin is not a field:
it has already been proved for all 318 recorded rows. -/
structure DensityCompactEnclosures where
  polynomial : Fin 318 → Polynomial ℝ
  error : Fin 318 → ℝ
  error_nonneg : ∀ i, 0 ≤ error i
  derivative_errors : ∀ i x, |panelCoordinate i.val x| ≤ 1 →
    |density x - (polynomial i).eval (panelCoordinate i.val x)| ≤ error i ∧
    |(1 / 200) * deriv density x -
      (polynomial i).derivative.eval (panelCoordinate i.val x)| ≤ error i ∧
    |(1 / 200 : ℝ) ^ 2 * deriv (deriv density) x -
      (polynomial i).derivative.derivative.eval (panelCoordinate i.val x)| ≤ error i
  constant_enclosure : ∀ i, recordedConstantLower i ≤
    (curvaturePolynomial (polynomial i)).coeff 0
  nonconstant_enclosure : ∀ i,
    coefficientNorm ((curvaturePolynomial (polynomial i)).erase 0) ≤ recordedOffUpper i
  curvature_error_enclosure : ∀ i,
    polynomialCurvatureError (polynomial i) (error i) ≤ recordedErrorUpper i

/-- Required analytic tail enclosures and overlap. In particular, this structure
does not assume the desired curvature inequality. -/
structure DensityTailEnclosures where
  A : ℝ
  B : ℝ
  C : ℝ
  a : ℝ
  b : ℝ
  R : ℝ
  D0 : ℝ
  D1 : ℝ
  D2 : ℝ
  C_pos : 0 < C
  a_pos : 0 < a
  a_lt_b : a < b
  b_lt_R : b < R
  A_lower : C * b ≤ A
  B_lower : C * a ≤ B
  D0_pos : 0 < D0
  D1_nonneg : 0 ≤ D1
  D2_pos : 0 < D2
  overlap : tailThreshold a b R (tailU1 C a b D0 D1 D2)
    (tailU2 C a b D0 D1 D2) (tailU3 C a b D0 D1 D2) ≤ 318 / 100
  derivative_errors : ∀ x,
    tailThreshold a b R (tailU1 C a b D0 D1 D2)
      (tailU2 C a b D0 D1 D2) (tailU3 C a b D0 D1 D2) ≤ x →
    |density x - (A * Real.exp (-a * x) - B * Real.exp (-b * x))| ≤
      D0 * Real.exp (-R * x) ∧
    |deriv density x - (-a * A * Real.exp (-a * x) + b * B * Real.exp (-b * x))| ≤
      D1 * Real.exp (-R * x) ∧
    |deriv (deriv density) x -
      (a ^ 2 * A * Real.exp (-a * x) - b ^ 2 * B * Real.exp (-b * x))| ≤
      D2 * Real.exp (-R * x)

/-- Conditional compact theorem: the explicit enclosure evidence is still needed. -/
theorem density_compact_curvature_positive_of_enclosures
    (h : DensityCompactEnclosures) (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ 318 / 100) :
    0 < curvatureJet (density x) (deriv density x) (deriv (deriv density) x) :=
  compact_curvature_positive_of_recorded_enclosures density (deriv density)
    (deriv (deriv density)) h.polynomial h.error h.error_nonneg h.derivative_errors
    h.constant_enclosure h.nonconstant_enclosure h.curvature_error_enclosure x hx0 hx

/-- Conditional tail theorem from the three analytic remainder estimates. -/
theorem density_tail_curvature_positive_of_enclosures
    (h : DensityTailEnclosures) (x : ℝ)
    (hx : tailThreshold h.a h.b h.R (tailU1 h.C h.a h.b h.D0 h.D1 h.D2)
      (tailU2 h.C h.a h.b h.D0 h.D1 h.D2) (tailU3 h.C h.a h.b h.D0 h.D1 h.D2) ≤ x) :
    0 < curvatureJet (density x) (deriv density x) (deriv (deriv density) x) := by
  obtain ⟨h0, h1, h2⟩ := h.derivative_errors x hx
  exact twoExponential_tail_curvature_positive_of_pole_bounds
    h.A h.B h.C h.a h.b h.R h.D0 h.D1 h.D2 x
    (density x) (deriv density x) (deriv (deriv density) x)
    h.C_pos h.a_pos h.a_lt_b h.b_lt_R h.A_lower h.B_lower
    h.D0_pos h.D1_nonneg h.D2_pos hx h0 h1 h2

/-- Assembly for the actual density. Compact and tail enclosure evidence remains
explicitly assumed; neither evidence structure has yet been constructed. -/
theorem density_curvature_positive_of_enclosures
    (hc : DensityCompactEnclosures) (ht : DensityTailEnclosures) :
    ∀ x, 0 < curvatureJet (density x) (deriv density x) (deriv (deriv density) x) := by
  exact positive_of_even_compact_tail
    (fun x => curvatureJet (density x) (deriv density x) (deriv (deriv density) x))
    (tailThreshold ht.a ht.b ht.R (tailU1 ht.C ht.a ht.b ht.D0 ht.D1 ht.D2)
      (tailU2 ht.C ht.a ht.b ht.D0 ht.D1 ht.D2)
      (tailU3 ht.C ht.a ht.b ht.D0 ht.D1 ht.D2)) (318 / 100)
    density_curvature_even ht.overlap
    (density_compact_curvature_positive_of_enclosures hc)
    (density_tail_curvature_positive_of_enclosures ht)

/-- Strict log concavity conditional on the still-unproved enclosures and
positivity. Actual density regularity is now proved in XiFourierFull. -/
theorem density_strictConcaveOn_log_of_enclosures
    (hc : DensityCompactEnclosures) (ht : DensityTailEnclosures)
    (hpos : ∀ x, 0 < density x) :
    StrictConcaveOn ℝ Set.univ (fun x => Real.log (density x)) := by
  exact strictConcaveOn_log_of_positive_curvature density (deriv density)
    (deriv (deriv density)) (fun x => (differentiable_density x).hasDerivAt)
    (fun x => (differentiable_deriv_density x).hasDerivAt) hpos
    (density_curvature_positive_of_enclosures hc ht)

/-- The corresponding strictly positive order-two translation determinant,
under the same explicit unproved analytic inputs. -/
theorem density_pf2_minor_pos_of_enclosures
    (hc : DensityCompactEnclosures) (ht : DensityTailEnclosures)
    (hpos : ∀ x, 0 < density x)
    (x1 x2 y1 y2 : ℝ) (hx : x1 < x2) (hy : y1 < y2) :
    0 < density (x1 - y1) * density (x2 - y2) -
      density (x1 - y2) * density (x2 - y1) := by
  exact pf2_minor_pos_of_positive_curvature density (deriv density)
    (deriv (deriv density)) (fun x => (differentiable_density x).hasDerivAt)
    (fun x => (differentiable_deriv_density x).hasDerivAt) hpos
    (density_curvature_positive_of_enclosures hc ht) x1 x2 y1 y2 hx hy

end ReciprocalXi
