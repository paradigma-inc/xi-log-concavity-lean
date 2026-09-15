# Fully rounded logarithms and log pi

With $t=(q-1)/(q+1)$, the $k$th odd-series term is $t^{2k+1}/(2k+1)$.
The next term multiplies it by the nonnegative rational
$t^2(2k+1)/(2k+3)$. Rounding each product outward gives lower/upper term
intervals without accumulating exact powers of a large rational denominator.
Their doubled sums enclose the exact logarithm Taylor polynomial.

For $q>0$ and $|t|\le r<1$, the already proved analytic remainder is at most
$2r^{2n+1}/(1-r^2)$. This follows by monotonicity of the numerator powers
and the positive denominator. Including this error and rounding again proves
`ratLogFullyRounded_enclosure`. Monotonicity of the actual log supplies the
whole-input-interval variant.

The proved Machin endpoints both lie in $[1,4]$, where $|t|\le3/5$.
Applying the interval theorem to those endpoints encloses the actual $\log\pi$.
At $n=400$ and $B=10^{180}$, `piLogFullyRounded_certified` also proves by
kernel-checked finite arithmetic that the interval width is below $10^{-160}$.
No supplied decimal value, runtime-only check or assumed logarithm accuracy is
used. The retained Xi source table and the global curvature theorem are separate.
