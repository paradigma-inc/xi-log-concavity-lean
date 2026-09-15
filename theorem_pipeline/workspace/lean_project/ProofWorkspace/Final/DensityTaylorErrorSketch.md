# Actual density-to-Taylor jet error

For a real center $c$, normalize the actual complex Fourier density as $D_c(z)=G(c+z/200)$. Let $A_c$ be the source cosine quadrature and $P_c$ its degree-64 Taylor polynomial. Both are entire, as is $D_c$.

Under the explicit retained-node discrepancy bounds $|\phi(k/40)-v_k|\le 2\cdot10^{-120}$, the checked quadrature and Cauchy estimate gives $|(D_c-A_c)^{(n)}(x)|\le 8\cdot10^{-85}$ for $|c|\le3.18$, $|x|\le1$, and $n\le2$. The checked Taylor remainder gives $|(A_c-P_c)^{(n)}(x)|\le\tau$, with the unchanged source $\tau=e^{66}50^{-65}66^2/(1-1/50)^3$.

Linearity of iterated differentiation and the triangle inequality therefore give $|D_c^{(n)}(x)-P_c^{(n)}(x)|\le8\cdot10^{-85}+\tau$. The source-pi corollary discharges the normalizer hypotheses using the already certified rounded midpoint. Taking real parts preserves the bound.

This proves the analytic propagation from the entire retained sample table to the actual density jets. It does not assert that the table-wide discrepancy hypothesis or the recorded polynomial coefficient enclosures have been certified.
