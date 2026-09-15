# Actual Xi theta integral: rigorous finite truncation

## Statement and assumptions

For real $x$ and $T\ge1$, the finite theta-integral approximation to $\operatorname{Re}F(x)$ has error at most $(1+x^2)e^{-\pi T}/(8\pi)$. The theta kernel and $F$ are the actual functions already defined in the project; no numerical enclosure is assumed.

## Proof sketch

The actual theta-Mellin representation is converted to a real cosine integrand. Its absolute value is bounded by $4e^{-\pi t}$ for $t\ge1$, using the previously proved complex integrand bound. Integrating this majorant gives an explicit tail bound. Splitting the actual integral into $(1,T]$ and $(T,\infty)$ yields the stated error for the finite integral formula for $\operatorname{Re}F(x)$.

This proves an analytic truncation estimate, not a numerical evaluation of the finite integral. In particular the required lower bound for $F(48)$ remains open. No zero-location certificate or numerical quadrature result is assumed implicitly.

## Lean artifacts

`XiThetaTruncationFull.lean`: `realThetaCosineIntegrand_abs_le`, `realThetaCosineIntegral_tail_abs_le`, and `F_real_finite_theta_integral_error`.
