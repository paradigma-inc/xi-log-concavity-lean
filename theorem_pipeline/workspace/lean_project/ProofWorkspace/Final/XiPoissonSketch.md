# Actual Poisson quadrature identity

For $h>0$ and $z\in\mathbb C$, define
$f_{z,h}(x)=\varphi(hx)e^{-iz(hx)}$. This is the actual reciprocal-Xi
transform and exponential, not an independently specified approximant.

The proved reciprocal strip tail controls this function by a constant times
$e^{-|x|}$ outside a compact interval. Exponential decay implies every fixed
inverse-power bound at infinity. A real change of variable gives the exact
Fourier-transform formula

$$\widehat f_{z,h}(y)=\frac1h\int_{\mathbb R}\varphi(u)
 e^{-i(z+2\pi y/h)u}\,du.$$

The actual contour estimate bounds this by a constant times
$e^{-(2\pi/h)|y|}$, using the triangle inequality for the shifted real part.
Thus both functions satisfy mathlib's inverse-power-decay hypotheses for
Poisson summation. All integer sums converge; no convergence hypothesis is
left to the caller.

Poisson summation at zero, followed by the exact $1/(2\pi)$ normalization,
gives

$$\frac{h}{2\pi}\sum_{n\in\mathbb Z}\varphi(hn)e^{-izhn}
 =\sum_{n\in\mathbb Z}G\!\left(z+\frac{2\pi n}{h}\right).$$

The nonzero terms on the right are the alias error. This module proves the
identity for the actual functions. It does not yet evaluate finite Xi samples,
bound truncation of the left sum, or certify the recorded panel coefficients.
