# Actual large-disc and Taylor-coefficient bounds

Use the explicit sample discrepancy hypotheses from `SampledQuadratureErrorFull`, together with $p\ge3$. For the resulting finite cosine function $A_{p,v}$, prove
$$|A_{p,v}(z)|<e^{66}\qquad (|\operatorname{Im}z|\le1/4).$$
No bound on the real part is needed.

For actual reciprocal-Xi samples, the previously proved quarter-rate decay cancels the cosine growth: $|\varphi(u)\cos(zu)|\le e^{16}\le3^{16}$ outside the central interval. The central interval satisfies an even smaller bound. A sample perturbation contributes at most $2\cdot10^{-120}e^{85}<1$ per term on the retained grid. Summing 13,600 terms and the half-weight zero term and using $1/(40p)\le1/120$ gives a concrete bound below $2^{66}<e^{66}$.

For any real center $c$, set $B_c(z)=A_{p,v}(c+z/200)$. It is entire. The radius-50 disk maps inside the preceding physical strip, so Cauchy's inequality gives
$$\left|\frac{B_c^{(n)}(0)}{n!}\right|\le e^{66}50^{-n}.$$
The module also proves the actual Taylor series sums to $B_c$ everywhere.

The finite sample errors remain explicit hypotheses. No recorded coefficient values, Taylor remainders, or source panel enclosures are silently assumed proved by these bounds.
