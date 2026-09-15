# Error in a Taylor panel from coefficient errors

## Statement

For forty Taylor terms and four Gaussian atoms, error at most $\epsilon$ in every scaled atom coefficient contributes at most $320\epsilon$ to the exact Taylor panel integral.

## Assumptions

The center is positive; the half-width lies in $[0,1/2]$; all $160$ coefficient errors are bounded by the explicit nonnegative $\epsilon$. The analytic Taylor remainder is separate.

## Proof Sketch

Each integrated scaled Taylor weight has absolute value at most one. The finite theta integrand is twice the sum of four atoms, so each retained coefficient contributes at most $8\epsilon$. Sum the forty terms. All comparisons are against the actual Taylor coefficients, not an unidentified numerical recurrence.

## Lean Artifacts

`XiThetaPanelCoefficientErrorFull.lean`: theta48ScaledIntegralWeight_abs_le_one, theta48Panel_coefficient_error.
