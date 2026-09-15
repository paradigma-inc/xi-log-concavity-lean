# Exact cosine form of the actual quadrature

For every $z\in\mathbb C$, real step $h$, and $K\in\mathbb N$, the actual symmetric reciprocal-Xi quadrature equals
$$T_{h,K}(z)=\frac{h}{2\pi}\left(1+2\sum_{j=0}^{K-1}\varphi(h(j+1))\cos(zh(j+1))\right).$$

Actual positivity of $\xi(1/2)$ gives $\varphi(0)=1$. Evenness of $\varphi$ pairs the positive and negative terms. The identity $2\cos w=e^{iw}+e^{-iw}$ turns each pair into its cosine term. Induction on $K$ and the exact closed-integer-interval sum identity finish the proof.

There are no numerical-certificate or zero-location hypotheses. This identity uses the actual reciprocal transform, not the recorded approximate samples. It does not yet identify or bound the source's rounded coefficients.
