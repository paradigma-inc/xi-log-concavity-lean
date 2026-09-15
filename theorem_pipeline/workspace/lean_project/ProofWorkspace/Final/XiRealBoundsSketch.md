# Actual real-axis Xi bounds and Fourier tails

This module concerns the actual function $\xi$ defined using mathlib's completed
Riemann zeta, and the actual reciprocal transform from `XiDefinitionFull`.
It does not assume an enclosure certificate, a product over zeros, or RH.

For real $s>1$, the convergent Dirichlet series is a sum of positive terms and
its first term is one. Casting the real sum to the complex numbers gives
$\xi(s)=s(s-1)\pi^{-s/2}\Gamma(s/2)\zeta(s)/2$. Thus $\xi(s)>0$ on this range;
the functional equation gives positivity also for $s<0$.

For $v\ge1$ and $T>0$, restrict Euler's Gamma integral to $[T,T+1]$.
Throughout that interval, $e^{-t}\ge e^{-(T+1)}$ and
$t^{v-1}\ge T^{v-1}$. The interval has length one, so
$\Gamma(v)\ge e^{-(T+1)}T^{v-1}$. Nonnegativity of the integrand justifies
passing from this interval to the whole positive half-line.

For an arbitrary real rate $r$, choose $T=\exp(2r+\log\pi)$ and set
$c_r=\exp(-(T+1)-(2r+\log\pi))>0$. The preceding lower bound simplifies to
$\xi(s)\ge c_r e^{rs}$ for $s\ge2$, since $s(s-1)/2\ge1$.
This is an explicit inequality, not an asymptotic statement with an unspecified
constant.

The exact identity $F(iu)=\xi((1+u)/2)/4$ then bounds the reciprocal transform
$\phi(u)=F(0)/F(iu)$ by $C_r e^{-r|u|}$ for $|u|\ge3$, where
$C_r=4|F(0)|/(c_{2r}e^r)$. The proof uses the norm's lower bound by the real
part and reflection symmetry. In particular, for any real weight $q$, use
rate $q+1$ to dominate $e^{q|u|}\phi(u)$ on the positive tail by an integrable
multiple of $e^{-u}$. The measure-preserving map $u\mapsto-u$ gives the
negative tail, and taking their union gives both tails.

The bounded interval $[-3,3]$ is explicitly excluded from these integrability
theorems. Positivity/nonvanishing there and whole-line Fourier regularity are
still separate obligations; no such conclusion is hidden in measurability or
in Lean's total inverse and integral definitions.
