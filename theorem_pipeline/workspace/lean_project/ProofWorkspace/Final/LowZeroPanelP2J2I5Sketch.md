# Actual low-zero panel: endpoint 2, panel (2,5)

## Statement

The exact stored rational sum encloses the actual eighty-term Taylor
panel integral with error at most $1600\cdot10^{-50}$.

## Assumptions

No numerical hypotheses. Nonzero atom modules independently certify
the original endpoint seed and all eighty actual scaled derivatives.
Eligible far atoms use the proved direct Cauchy bound with zero stored
coefficients; their exact geometry inequalities are checked by Lean.
This is one panel, not an endpoint sign or a zero certificate.

## Proof Sketch

Assemble the five atom functions by an exhaustive finite case split,
using the direct actual-derivative theorem where the stored atom is zero.
Lean checks the exact rational weighted sum. Apply the proved panel
error transfer to the five-by-eighty actual coefficient enclosures.
The analytic Taylor remainder is handled separately.

## Lean Artifacts

- File: `LowZeroPanelP2J2I5Full.lean`
- Theorems: `lowZeroPanelP2J2I5_coefficients_error`, `lowZeroPanelP2J2I5Value_eq`,
  `lowZeroPanelP2J2I5_panel_error`.
