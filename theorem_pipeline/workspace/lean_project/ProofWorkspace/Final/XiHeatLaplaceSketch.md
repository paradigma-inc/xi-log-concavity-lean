# Actual heat-trace Laplace transform and reciprocal derivative

## Statement

For $x\ge0$, the integral $\int_0^\infty e^{-xt}H(t)\,dt$ equals the actual resolvent sum $\sum_a(a^2+x)^{-1}$. At every real $u$, the logarithmic derivative of the actual reciprocal extension is $-2u$ times that integral with $x=u^2$.

## Assumptions

Only the indicated real parameter range. No positivity assumption for $H$, RH, supplied zero list or conditional product identity.

## Proof Sketch

Multiplication by $e^{-xt}$ changes each decay rate from $a^2$ to $a^2+x$, still with positive real part. Its norm integral is exactly $(\operatorname{Re}(a^2)+x)^{-1}$, bounded by the already summable inverse real-square rates. This justifies exchanging sum and integral. A separate bounded-multiplier proof verifies integrability of the summed Laplace integrand. Finally substitute $w=iu$ in the actual paired-product logarithmic derivative, apply the reciprocal and chain rules, and use the already proved nonvanishing on the imaginary axis.

This proves the analytic identity, not the positivity or probability-law construction.

## Lean Artifacts

- `XiHeatLaplaceFull.lean`
- Main results: `F_zeroHeatTrace_laplace_eq`, `integrableOn_F_zeroHeatTrace_laplace`, `reciprocalExtension_logDeriv_heat`.
