# Quantitative central reciprocal-Xi strip estimate

The actual theta/Mellin identity extends to $-1\le\Re s\le2$: both Mellin
exponents $s/2$ and $(1-s)/2$ still have real part at most one. Reusing the
proved actual theta tail bound gives
$$
|\Lambda_0(s)|\le\frac{4e^{-\pi}}{\pi}<\frac18.
$$
Here $\Lambda_0$ is mathlib's actual pole-removed completed zeta. The strict
numerical inequality follows from $\pi>3$ and
$e^3\ge(5/2)^3=125/8$, with $e\ge5/2$ proved by the exponential quadratic bound.

If also $|\Im s|\le1/2$, then
$$
|s(s-1)|\le\frac{|s|^2+|s-1|^2}{2}
=\Re s(\Re s-1)+\frac12+(\Im s)^2\le\frac{11}{4}.
$$
Consequently the defining identity
$\xi(s)=(s(s-1)\Lambda_0(s)+1)/2$ gives
$\Re\xi(s)\ge21/64$. On the real interval $[-1,2]$, the sharper
$|x(x-1)|\le2$ gives $|\xi(x)|\le5/8$. Together these yield
$$
|\xi(\Re s)|\le2|\xi(s)|.
$$

`reciprocalExtension_norm_le_two_central` translates this through
$s=(1+z)/2$ and the exact normalization to
$$
|\varphi(z)|\le2|\varphi(\Re z)|
\quad (|\Re z|\le3,\ |\Im z|\le1).
$$
The division is justified by actual Xi nonvanishing already proved. No zero
table, RH hypothesis, or numerical enclosure is assumed. This proves only the
central part of the desired full-strip estimate; the outer Gamma/zeta bounds
and subsequent contour/quadrature argument are separate obligations.
