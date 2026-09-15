# Finite low-zero coefficient checks

## Statement

The rational first and second-order transitions agree exactly with the
actual power-exponential recurrence using the rational pi midpoint.
For each mode $k\le5$, replacing the actual pi by that midpoint changes
the transition by at most $10^{-140}$. The finite validity predicate
checks all eighty stored coefficient norms and error radii, all rounded
recurrences, and the common radius cap $10^{-50}$.

## Assumptions

The predicate states every finite numeric condition explicitly. Radius
values are interpreted by absolute value, so their global nonnegativity
is proved rather than assumed. The seed bound retains its relative
dependence on the stored seed magnitude.

## Proof Sketch

Exact rational-to-complex identities establish the transition formulas.
The original pi error multiplied by $k^2\le25$ gives the stated uniform
perturbation. The complex norm is bounded by the rational coordinate
absolute sum, which transfers the relative exponential seed estimate
to the rational seed-radius expression. The finite checks alone do not
yet certify actual derivatives; the soundness theorem performs that step.

## Lean Artifacts

- File: `LowZeroCoefficientChecksFull.lean`
- Theorems: `ratLowZeroFirst_value`, `ratLowZeroA_value`,
  `lowZeroLambda_midpoint_error`, `lowZeroCoefficientRadius_nonneg`,
  `lowZeroSeedRadius_sound`.

