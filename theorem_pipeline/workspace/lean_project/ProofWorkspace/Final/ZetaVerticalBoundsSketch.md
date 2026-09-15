# Quantitative vertical zeta bounds

For $\Re s\ge2$ and coefficients $|a_n|\le1$, absolute convergence gives
$$
|L(a,s)|\le\sum_{n\ge1}\frac{|a_n|}{n^{\Re s}}
\le\sum_{n\ge1}\frac1{n^2}=\frac{\pi^2}{6}<2.
$$
The summability, term comparisons and Basel identity are proved library facts;
the numerical comparison uses the proved bound $\pi<3.15$.

Apply `norm_LSeries_le_two` first to the constant-one coefficients to get
$|\zeta(s)|\le2$, and then to the actual Möbius coefficients, whose absolute
values are at most one. The library's absolutely convergent Dirichlet-series
identity $\zeta(s)L(\mu,s)=1$ gives
$$
1=|\zeta(s)|\,|L(\mu,s)|\le2|\zeta(s)|,
$$
so `riemannZeta_norm_ge_half` proves $|\zeta(s)|\ge1/2$.

Combining this with the real-axis upper bound proves the source's ratio
estimate, in multiplication form:
$$
|\zeta(\Re s)|\le4|\zeta(s)|\qquad(\Re s\ge2).
$$
No Euler product, numerical zeta value, nonvanishing claim or zero table is
assumed. These are actual zeta bounds, but they alone do not establish the
full Xi strip estimate or its quadrature consequence.
