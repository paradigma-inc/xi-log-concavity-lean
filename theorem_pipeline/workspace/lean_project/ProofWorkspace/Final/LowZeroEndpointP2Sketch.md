# Actual original endpoint 2

## Statement

The real part of the actual analytic function F is strictly negative
at original endpoint 2. The exact rational coordinate is
$ 210220396387715549926284795938869/5000000000000000000000000000000 $.

## Assumptions

No numerical hypotheses. All forty actual panel certificates are used,
including the original pi and logarithm bounds and the actual atom
derivative enclosures. The endpoint and predetermined sign are unchanged.

## Proof Sketch

The finite case split supplies all forty panel errors. Their exact
rational sum is checked by Lean and the proved stored-quadrature transfer
adds every analytic and coefficient error, giving the total radius
$4\cdot10^{-39}$. Exact arithmetic shows this entire interval has the
stated strict sign. Python proposes the sum only; it is not an oracle.

This result is an endpoint sign, not root simplicity or completeness.

## Lean Artifacts

- Full proof: LowZeroEndpointP2Full.lean
- Theorems: lowZeroEndpointP2_panel_error, lowZeroEndpointP2_quadrature_cast,
  lowZeroEndpointP2_quadrature_eq, lowZeroEndpointP2_error, lowZeroEndpointP2_sign.
