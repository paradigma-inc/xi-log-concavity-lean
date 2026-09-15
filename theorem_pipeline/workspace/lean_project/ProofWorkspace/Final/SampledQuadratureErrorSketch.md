# Sample, normalization and derivative errors

Let $\varphi$ be the actual reciprocal-Xi transform, $G$ its entire Fourier density, and
$$A_{p,v}(z)=\frac{1}{40p}\left(\frac{v_0}{2}+\sum_{k=1}^{13600}v_k\cos(kz/40)\right).$$
The supplied $v_k$ are arbitrary real numbers. The theorem assumes, explicitly,
$$|\operatorname{Re}\varphi(k/40)-v_k|\le2\cdot10^{-120}\quad(0\le k\le13600),\qquad p\ge3,\quad |p-\pi|\le10^{-150}.$$
Under these hypotheses, for $|\operatorname{Re}z|\le4$ and $|\operatorname{Im}z|\le1/100$,
$$|A_{p,v}(z)-G(z)|<10^{-85}.$$

The complex cosine identity gives $|\cos z|\le e^{|\operatorname{Im}z|}$. On this grid the cosine factor is at most $e^{3.4}<81$. Summing all sample discrepancies costs less than $2\cdot10^{-116}$. The already proved actual finite-quadrature error costs less than $3/(4\cdot10^{85})$. A coarse actual reciprocal-transform bound $|\varphi(u)|\le3^{16}$ controls the sample amplitudes; the pi-normalization change costs less than $10^{-115}$. Exact rational comparisons leave the claimed total budget.

Both functions are entire. For $|c|\le3.18$, real $|x|\le1$, and $n=0,1,2$, apply Cauchy's inequality on the radius-$1/2$ circle around $x$ to
$$E_c(z)=G(c+z/200)-A_{p,v}(c+z/200).$$
That circle maps inside the proved complex rectangle. Therefore
$$|E_c^{(n)}(x)|\le n!\,2^n10^{-85}\le8\cdot10^{-85}.$$
This is an analytic derivative bound, not one inferred from real samples.

The numerical sample hypotheses remain unproved for the full recorded table. This module proves error propagation and does not certify the source's sample values, Taylor coefficients, or global curvature theorem.
