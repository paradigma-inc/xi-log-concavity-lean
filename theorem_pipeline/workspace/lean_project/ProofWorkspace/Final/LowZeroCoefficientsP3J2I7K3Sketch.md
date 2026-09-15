# Eighty actual coefficients: endpoint 3, panel (2,7), atom 3

## Statement

All eighty stored scaled coefficients differ from the actual analytic
derivatives of this power-exponential atom by at most $10^{-50}$.

## Assumptions

No numerical coefficient assumptions. The initial value is exactly the
previously certified source-endpoint seed. The seed identity, all finite
recurrences and every outward-rounded radius inequality are kernel checked.

## Proof Sketch

The kernel verifies the exact seed identity, the first transition, all
seventy-eight subsequent rounded recurrence residuals, all stored-state
norm bounds and all propagated radius bounds. The generic second-order
error induction identifies these bounds with the actual scaled derivatives.
The common radius cap gives the stated uniform coefficient error.
This is one atom, not a complete panel, endpoint sign or zero certificate.

## Lean Artifacts

- File: `LowZeroCoefficientsP3J2I7K3Full.lean`
- Main theorem: `lowZeroCoefficientsP3J2I7K3_actual_coefficient_error`.
