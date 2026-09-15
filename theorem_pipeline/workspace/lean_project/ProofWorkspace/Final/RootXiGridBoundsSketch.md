# Xi grid bounds from algebraic root certificates

For $s_k=(k+40)/80$, compose the actual factorization
$\xi(s_k)=(s_k/2)\Gamma(s_k/2)\pi^{-s_k/2}\eta(s_k)B(s_k)$.
The eta interval uses polynomial certificates for the positive 80th roots
$a^{-1/80}$ and rounded powers of order $k+40$. Its Euler error remains
$0\leq\eta(s_k)-E_N(s_k)\leq2^{-N}$.

The other factors retain their proved rounded Gamma, pi-power and dyadic
power bounds. The lower product clamps each factor to zero, using the
proved nonnegativity of the actual factors; the upper product uses their
positive upper bounds. Outward rounding preserves the interval. At
$k=40$, the removable value is handled exactly by $\xi(1)=1/2$.

Dividing the node-zero enclosure by the positive node-$k$ enclosure gives
the actual reciprocal transform $\xi(1/2)/\xi(s_k)$. All hypotheses are
explicit rational range, denominator or root-polynomial checks. This
module proves enclosure soundness; it does not by itself certify any
high-precision source-table sample.
