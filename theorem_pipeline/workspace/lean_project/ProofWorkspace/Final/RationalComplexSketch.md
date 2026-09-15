# Exact rational complex arithmetic

## Statement

Rational coordinate pairs embed in the complex numbers compatibly with addition, multiplication and division by natural numbers. Coordinate absolute values bound the complex norm. The finite exact recurrence computes precisely the complex exponential Taylor polynomial.

## Assumptions

All identities are unconditional, including division by zero under Lean's field convention. The unit-norm corollary assumes the explicit squared-coordinate inequality.

## Proof Sketch

Coordinate calculations prove the ring identities and norm bounds. Induction identifies each exponential term with $z^n/n!$, and the accepted finite summation loop sums those exact terms. There is no floating-point computation or numerical oracle.

## Lean Artifacts

`RationalComplexFull.lean`: coordinate, ring, norm, exponential-term, and finite Taylor-sum theorems.
