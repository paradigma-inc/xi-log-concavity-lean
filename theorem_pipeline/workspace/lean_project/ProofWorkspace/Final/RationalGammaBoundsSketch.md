# Rational Gamma bounds

The target is the actual real Gamma function on $[1/2,3/2]$, not an assumed table of Gamma values. For rational $z$ with $|z|\le1/2$, the centered log-series theorem bounds $\log\Gamma(1+z)$ by

$$z\log\pi-2z\log2+\sum_{k<N}\frac{(-1)^k(z^{k+2}-2z\,2^{-(k+2)})}{k+2}\zeta(k+2)$$

with error at most $8\,2^{-(N+2)}$.

Replace each integer zeta value by its proved rational Euler lower endpoint. The absolute error in the sum is at most $2^{1-M}$ times the sum of the absolute rational coefficients. The proved Machin interval and logarithm interval theorem enclose $\log\pi$; the rational logarithm series encloses $\log2$. Triangle inequalities with the exact factors $|z|$ and $2|z|$ give `ratLogGamma_error`. Its center and radius, including every contribution, are rational.

`ratGamma_enclosure` applies the proved scaled exponential evaluator to the two rational log-Gamma endpoints. Gamma is positive throughout the domain, so $\exp(\log\Gamma(1+z))=\Gamma(1+z)$. The only extra conditions are the explicit rational range-reduction checks and positive exponential orders. No assumed real-valued enclosure, Stirling remainder, external numerical oracle, or source table is used.

This is a numerical primitive, not yet a certificate for all retained Xi nodes or for global density curvature.
