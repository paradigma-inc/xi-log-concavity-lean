# Concrete infinite-grid quadrature error

The central Xi rectangle bounds give $|\varphi(u)|\le2$ for $|u|\le3$.
On the two tails, the earlier Euler Gamma bound gives
$|\varphi(u)|\le C_{1/4}e^{-|u|/4}$, and its explicit constant satisfies
$C_{1/4}\le e^{16}$. This last inequality follows from $e<3$, $\pi<4$
and $\log\pi<2$; it is not an assumed numerical transform bound.

For $0\le q<1/4$, split the weighted integral into the central interval and
the two tails. Direct integration of $e^{-a|u|}$ gives

$$J(q):=\int_{\mathbb R}e^{q|u|}|\varphi(u)|\,du
\le12e^{3q}+\frac{2C_{1/4}}{1/4-q}.$$

In particular, $0\le q\le1/100$ gives $J(q)\le e^{20}$. For
$|\operatorname{Re}z|\le4$ and $|\operatorname{Im}z|\le1/100$, the actual
alias amplitude is therefore at most $e^{24}$.

The already-proved infinite trapezoid error is
$2A(z)/(e^{2\pi/h}-1)$. At $h=1/40$, use $\pi>3$ and
$e^{240}-1\ge e^{240}/2$ to bound it by $4e^{-216}$.
A rational Taylor witness proves $e^{2.31}\ge10$, hence
$10^{85}\le e^{200}$. Together with $e^{16}>16$, this yields

$$|T_{1/40}(z)-G(z)|<\frac1{4\cdot10^{85}}.$$

Thus the actual infinite quadrature error consumes less than one quarter
of the source's $10^{-85}$ budget throughout the stated complex rectangle.
The finite cutoff error and retained-node enclosure/rounding errors remain
separate; no coefficient enclosure or global positivity is inferred here.
