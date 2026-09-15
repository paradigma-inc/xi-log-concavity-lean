# Stored quadrature for the original low-zero endpoints

## Statement

Five atoms with eighty coefficient enclosures of radius $10^{-50}$
give each actual Taylor panel integral an error at most
$1600\cdot10^{-50}$. Summing forty dyadic panels gives
$64000\cdot10^{-50}$. Together with the analytic truncation and Taylor
bounds, the stored expression approximates the actual real part of F
with absolute error at most $4\cdot10^{-39}$ for $|x|\le60$.

## Assumptions

Every stored coefficient or panel error is an explicit hypothesis.
These transfer results do not assert the finite numeric hypotheses,
an endpoint sign, root existence, or completeness.

## Proof Sketch

Expand the actual finite theta derivative as twice the sum of five
actual scaled atom derivatives. Integrate its Taylor monomials exactly.
Bound each scaled integral weight by two, each real coordinate error by
the complex norm error, and sum the 400 terms and forty panels.
The exact rational-to-real cast identifies the stored weighted sum.
Finally multiply by the F prefactor and add the already proved
$3\cdot10^{-39}$ analytic quadrature error.

## Lean Artifacts

- File: `XiLowZeroStoredQuadratureFull.lean`.
- Main theorems: `ratLowZeroPanel_error`,
  `lowZeroStoredQuadrature_error`, `F_lowZero_storedQuadrature_error`.

