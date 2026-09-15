# Fine-root exact quadrature

## Statement

For every real $|x|\le60$, the exact forty-panel, eighty-term Taylor sum
$Q(x)$ satisfies
$$
\left|F(x)-\frac{1-(1+x^2)Q(x)/4}{8}\right|\le3\cdot10^{-39}.
$$
The sum contains actual analytic derivatives, not trusted stored coefficients.

## Assumptions

Only $|x|\le60$. Individual panel lemmas additionally state their
center and half-width assumptions explicitly.

## Proof Sketch

The Taylor polynomial is integrated exactly on each panel. The forty
dyadic panels cover $[1,32]$ without gaps, so the pointwise remainder
$10^{-56}$ contributes at most $31\cdot10^{-56}$ to the integral.
Multiplication by $(1+x^2)/32\le3601/32$, followed by the already proved
actual theta truncation bound, gives the stated total error.
Stored numerical sums still require independent exact coefficient
certificates before any zero or endpoint sign can be inferred.

## Lean Artifacts

- File: `XiLowZeroIntegralFull.lean`
- Main theorem: `F_lowZeroThetaQuadrature80_error`.

