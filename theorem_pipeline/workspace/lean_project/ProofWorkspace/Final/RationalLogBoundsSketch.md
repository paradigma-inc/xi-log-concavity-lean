# Exact rational logarithm enclosures

For a positive rational $q$, set $t=(q-1)/(q+1)$. Then $|t|<1$ and
$(1+t)/(1-t)=q$. Define the exact rational quantities
$$
L_n(q)=2\sum_{k=0}^{n-1}\frac{t^{2k+1}}{2k+1},\qquad
E_n(q)=\frac{2|t|^{2n+1}}{1-t^2}.
$$

`ratLogTaylor_error` proves $|\log q-L_n(q)|\le E_n(q)$ by applying mathlib's
proved finite logarithm-series remainder and the exact rational substitution.
`ratLog_enclosure` converts this to two ordered rational endpoints. The sole
input assumption is $q>0$; the proof also handles $q<1$ and every $n\ge0$.

`ratLog_interval_enclosure` uses monotonicity to enclose $\log x$ throughout
any interval $0<a\le x\le b$, not just at sample points.
`ratLog_dyadic_enclosure` proves range reduction for $2^m r$ with $m\in\mathbb N$
and $r>0$, using $\log(2^m r)=m\log2+\log r$ and nonnegative scaling of the
endpoint bounds. In particular, one can choose $1\le r\le2$ for large inputs.

`log_two_certified` checks the concrete witness
$$
\frac{69314718}{10^8}\le\log2\le\frac{69314719}{10^8}
$$
using $n=10$ and exact rational arithmetic. No externally computed decimal is
accepted as a premise, and no native unchecked decision procedure is used.

This is a sound elementary numerical primitive. It does **not** yet enclose
Gamma, Xi, Fourier quadrature errors, or the compact curvature certificate.
