# Dyadic finite theta quadrature

## Statement

The thirty-two dyadic Taylor panels cover $[1,16]$ exactly. The exact forty-term polynomial integrals differ from the retained finite theta integral by at most $15\cdot10^{-22}$. Including both infinite tails, the resulting expression for $F(48)$ has error at most $2\cdot10^{-16}$.

## Assumptions

None beyond the definitions of the actual finite theta integrand and its derivative coefficients. The finite sum is not yet numerically evaluated.

## Proof Sketch

Split each interval $[2^j,2^{j+1}]$, for $j=0,1,2,3$, into eight equal intervals. Their centers and half-widths satisfy the proved Taylor bounds. Sum adjacent integrals exactly, then sum the length-weighted panel errors. Their lengths total fifteen. Finally combine with the previously proved finite-time and Gaussian-tail bounds using the exact factor $2305/32$.

## Lean Artifacts

- Full proof: `XiThetaDyadicIntegralFull.lean`
- Main theorems: `theta48Quadrature40_error`, `F48_theta48Quadrature40_error`.
