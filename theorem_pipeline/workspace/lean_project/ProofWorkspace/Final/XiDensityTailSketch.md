# Actual density derivatives and tail enclosures

## Statement and assumptions

Let two actual zero occurrences have real roots $0<a<b$, and assume the remaining heat trace is nonnegative. The derivatives of the actual reciprocal-Xi density through order two equal the corresponding kernel-jet integrals. If $b\le R<L$, all remaining roots have $\operatorname{Re}(z^2)>L^2$, and the actual finite-factor quotient at $R$ is bounded by $M$, then the source's three derivative remainders hold with $D_j=2CM(ba^j+ab^j)$ and $C=ab/[2(b^2-a^2)]$.

With $M>0$, $b<R$, and the explicit numerical overlap inequality, a `DensityTailEnclosures` witness exists. No derivative remainder or curvature assertion is assumed in its construction.

## Proof Sketch

The proved density/convolution identity transfers bounded-kernel differentiation under the integral to the actual density. The residual law's absolute exponential moment is finite and bounded by its proved Xi quotient, so the previously established convolution remainder theorem applies. Symmetry and probability mass give both leading one-sided moments at least one, supplying the pole lower bounds. These facts fill every analytic field of the tail-enclosure structure; only the original numerical quotient and overlap inputs remain explicit.

The finite low-zero certificate, root enclosures, moment cap, and compact certificate are not supplied by this module. Its conclusions remain conditional on the stated inputs.

## Lean artifacts

- `XiDensityTailFull.lean`
- `density_iterated_deriv_eq_twoLaplace`
- `density_twoLaplace_derivative_remainder`
- `density_tail_enclosures_nonempty`
