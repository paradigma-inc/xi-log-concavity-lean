# Recorded margins and analytic panel enclosures

## Statement

Every one of the $318$ recorded rows satisfies
$q_{\mathrm{off}}/10^s+q_{\mathrm{err}}/10^s<q_0/10^s$ in Lean.
The theorem `compact_curvature_positive_of_recorded_enclosures` combines this
checked finite arithmetic with explicit polynomial-enclosure and derivative-error
hypotheses to conclude physical curvature positivity throughout $[0,3.18]$.

## Assumptions

For each panel, one must supply a real polynomial $P_i$, a nonnegative error
$e_i$, uniform bounds on the normalized value/first/second derivative errors,
and proofs that the recorded lower/upper bounds really enclose the constant
curvature coefficient, nonconstant coefficient norm, and curvature error.
These are hypotheses, not consequences of the JSON file or its hash.

## Proof Sketch

The length theorem gives a total lookup indexed by $\mathrm{Fin}(318)$; every
lookup belongs to the checked list. Its strict real margin follows from the
kernel-checked integer margin by division by the positive denominator $10^s$.
Monotonicity transfers this strict margin through the analytic enclosure
inequalities to the polynomial coefficient margin. The whole-panel theorem
then gives curvature positivity everywhere on each panel. The exact coverage
and coordinate-rescaling theorems give the result on the full compact interval.

## Lean Artifacts

File: `CertificateBridgeFull.lean` in `ProofWorkspace/Final`.

Theorems: `ReciprocalXi.recordedMarginAt_mem`,
`ReciprocalXi.recorded_bounds_strict_margin`, and
`ReciprocalXi.compact_curvature_positive_of_recorded_enclosures`.

## Scope

The numeric margin is discharged; the analytic meaning of the numbers is not.
This is a conditional bridge, not a completed reciprocal-Xi theorem.
