# Actual low-zero panel: endpoint 0, panel (0,0)

## Statement

The exact stored rational sum encloses the actual eighty-term Taylor
panel integral with error at most $1600\cdot10^{-50}$.

## Assumptions

No numerical hypotheses. The five atom modules independently certify
the original endpoint seed and all eighty actual scaled derivatives.
This is one panel, not an endpoint sign or a zero certificate.

## Proof Sketch

Assemble the five atom functions by an exhaustive finite case split.
Lean checks the exact rational weighted sum. Apply the proved panel
error transfer to the five-by-eighty actual coefficient enclosures.
The analytic Taylor remainder is handled separately.

## Lean Artifacts

- File: `LowZeroPanelP0J0I0Full.lean`
- Theorems: `lowZeroPanelP0J0I0_coefficients_error`, `lowZeroPanelP0J0I0Value_eq`,
  `lowZeroPanelP0J0I0_panel_error`.
