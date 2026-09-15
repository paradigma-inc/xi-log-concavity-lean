# Exponential seeds for dyadic theta panel (3, 5)

## Statement

Four rational state sequences approximate complex exponentials at this panel's four atom inputs, each with absolute error at most $10^{-43}$.
The input identities connect the literals to the frozen pi midpoint and the certified dyadic logarithm midpoint. Forty rounded coefficient states per atom also pass the explicit rational recurrence/error-radius inequalities. Their rational weighted sum approximates the actual forty-term Taylor panel integral to within $320\cdot10^{-25}$; the analytic Taylor remainder is a separate, already proved bound.

## Assumptions

The finite checks have no numerical hypotheses. The actual atom-value theorem uses the previously proved pi and logarithm errors, giving an error at most $10^{-42}$. The actual coefficient error theorem uses the proved analytic recurrence and error transfer, giving error at most $10^{-25}$ for each of the forty scaled coefficients.

## Proof Sketch

Lean evaluates the exact forty-term rational complex Taylor series at the input divided by 1024, verifies the initial rounding error, and checks all ten rounded squarings and unit-norm bounds. The generic proved exponential certificate then gives the error. The coefficient states use the exact rational transition with rounding at each step; the fixed error-radius inequalities and state bounds are finite kernel checks. Python proposes witnesses only; every numerical comparison is checked by Lean's kernel.

## Lean Artifacts

- Full proof: `ThetaExpPanel3_5Full.lean`.
- For atoms 1 through 4: input identity, finite seed validity, and the exponential error theorem.
