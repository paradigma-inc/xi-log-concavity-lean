# Soundness of the eighty-coefficient checks

## Statement

The finite rational validity predicate and its actual atom seed bound imply
that all eighty stored complex coefficients enclose the actual scaled
derivatives. Each error is bounded by the checked absolute radius, hence
by the fixed uniform cap $10^{-50}$.

## Assumptions

The seed hypothesis compares the stored value with the actual principal
power times Gaussian exponential. The rational predicate checks the
mode and geometry, eighty coefficient norms and radii, first-step and
seventy-eight recurrence residuals, and every propagated radius inequality.
No derivative enclosure or root statement is assumed.

## Proof Sketch

Convert rational transitions to their complex values and use the proved
pi-midpoint perturbation bounds. Establish the first two coefficient
errors, then apply the exact second-order error induction to the actual
power-exponential derivative recurrence. The coordinate absolute sum
bounds every stored norm, and the rational radius inequalities transfer
to real inequalities. Finally apply the checked uniform radius cap.

## Lean Artifacts

- File: `LowZeroCoefficientSoundnessFull.lean`
- Theorems: `ratLowZeroCoefficientsValid_error`,
  `ratLowZeroCoefficientsValid_uniform_error`.

