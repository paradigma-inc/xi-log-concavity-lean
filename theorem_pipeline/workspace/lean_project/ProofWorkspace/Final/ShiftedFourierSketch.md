# Actual inverse-Fourier contour shifting

Write $\Phi(w)=F(0)/F(iw)$ and $K_z(w)=\Phi(w)e^{-izw}$.
For $w=u+iv$ with $|v|\le1$, the proved reciprocal strip estimate gives

$$|K_z(u+iv)|\le5e^{\operatorname{Re}(z)v}
 e^{|\operatorname{Im}(z)||u|}|\varphi(u)|.$$

The right-hand side is integrable in $u$ by the already-proved exponential
moments of the actual transform. This proves absolute convergence on every
horizontal line, and bounds the norm of its integral.

The denominator is nonzero throughout the closed strip, so the kernel is
complex differentiable at every point of each finite rectangle within it.
Cauchy's rectangle theorem gives the four-side identity. The actual tail
bound, with exponent increased by $|\operatorname{Im}(z)|$, bounds either
vertical side at real part $\pm R$ by a constant times $e^{-R}$.
Both vertical integrals therefore tend to zero. Absolute integrability makes
the two horizontal truncated integrals converge to their full integrals.
Taking the limit proves equality of the integrals at any two heights in
$[-1,1]$; no contour-shifting premise is assumed.

Choose height $-1$ for nonnegative real part of $z$ and height $1$ otherwise.
The resulting bound is

$$\left|\int_{\mathbb R}\varphi(u)e^{-izu}\,du\right|
 \le5e^{-|\operatorname{Re}(z)|}
 \int_{\mathbb R}e^{|\operatorname{Im}(z)||u|}|\varphi(u)|\,du.$$

This proves actual exponential decay and provides a prerequisite for the
quadrature argument. It does not certify the finite Xi values, the source's
quadrature constants, global density positivity or strict log-concavity.
