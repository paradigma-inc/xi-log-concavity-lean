# Finite theta Taylor integration on a panel

## Statement

The integral of the actual Taylor polynomial on $[c-h,c+h]$ equals the finite sum of its real coefficients times the exact monomial integrals. For $c\ge1$, $0\le h\le c/16$, replacing the real finite theta integrand by its forty-term Taylor polynomial has integral error at most $2h\,10^{-22}$.

## Assumptions

Only the center and half-width restrictions. Every polynomial coefficient is an actual derivative; no numerical enclosure is assumed.

## Proof Sketch

Take real parts of the complex polynomial and integrate each monomial using its elementary antiderivative. The actual integrand and polynomial are integrable on the panel by continuity. The complex Taylor remainder bounds the real-part error, and integrating the uniform bound over length $2h$ yields the claimed error.

## Lean Artifacts

- Full proof: `XiThetaPanelIntegralFull.lean`
- Theorems: `realTheta48TaylorPolynomial_eq_re`, `continuous_realTheta48TaylorPolynomial`, `integral_realTheta48TaylorPolynomial`, `realTheta48Taylor40_error`, `realTheta48Taylor40_panel_error`.
