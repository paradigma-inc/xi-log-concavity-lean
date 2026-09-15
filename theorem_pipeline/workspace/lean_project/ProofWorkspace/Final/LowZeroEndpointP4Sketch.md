# Actual original endpoint 4

## Statement

The real part of the actual analytic function F is strictly positive
at original endpoint 4. The exact rational coordinate is
$ 31263571975182110954017238740691/625000000000000000000000000000 $.

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

- Full proof: LowZeroEndpointP4Full.lean
- Theorems: lowZeroEndpointP4_panel_error, lowZeroEndpointP4_quadrature_cast,
  lowZeroEndpointP4_quadrature_eq, lowZeroEndpointP4_error, lowZeroEndpointP4_sign.
