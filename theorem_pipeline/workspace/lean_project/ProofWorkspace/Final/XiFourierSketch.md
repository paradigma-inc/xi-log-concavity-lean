# Whole-line reciprocal-Xi integrability and density smoothness

Real Xi positivity follows by combining the Gamma/Dirichlet-series argument on
$s>1$, its functional-equation reflection on $s<0$, and the actual theta/Mellin
bound on $0\le s\le1$. Thus $\xi(s)\ne0$ for every real $s$, and the exact
identity $F(iu)=\xi((1+u)/2)/4$ gives a nonzero Fourier denominator everywhere.
Continuity of the entire Xi function and division by this nonzero denominator
prove continuity of the actual reciprocal transform $\phi$.

For any real $q$, $e^{q|u|}\phi(u)$ is continuous and hence integrable on the
compact interval $[-3,3]$. The previously proved actual tail estimates give
integrability on the two complementary open tails. Their union is the whole
real line, proving global integrability for every exponential weight. The
case $q=0$ proves ordinary transform integrability.

The positive exponential series yields
$|u|^n/n!\le e^{|u|}$ for every natural $n$. Multiplying this inequality by
$|\phi(u)|$ and using weighted integrability proves all polynomial Fourier
moments. The same argument also explicitly records integrability on the tails.

The definition of the density is exactly
$g(x)=\operatorname{Re}(\mathcal F\phi)(x/(2\pi))/(2\pi)$ with mathlib's
Fourier convention. This identity is checked by simplifying the exponent
$-2\pi i u\,x/(2\pi)=-iux$, not by changing the original definition.
Mathlib's Fourier regularity theorem applies at every finite derivative order
because all the moments have been proved. Composition with the linear scaling
and real-part map gives $g\in C^\infty(\mathbb R)$. In particular, both $g$
and $g'$ are differentiable.

These conclusions have no remaining Xi-specific analytical assumptions.
Smoothness is not positivity or strict log concavity of $g$. The residual
positive-measure representation and the compact/tail curvature certificates
are still separate obligations for the full target.
