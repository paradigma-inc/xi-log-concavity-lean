# Finite actual theta integral with a proved total truncation error

## Statement and assumptions

For $T\ge1$ and $N\in\mathbb N$, replacing the actual theta integral by the first $N$ Gaussian terms integrated over $(1,T]$ has error at most
$$\frac{1+x^2}{8\pi}\left(e^{-\pi T}+\frac{e^{-\pi(N+1)^2}}{(N+1)^2}\right).$$
The real parameter $x$ is arbitrary. No finite integral value is assumed.

## Proof sketch

The finite Gaussian expression is continuous on the positive half-line and integrable on every compact interval in it. The actual-minus-finite integrand is bounded by the proved exponential majorant. Integrate that bound on $(1,T]$ and enlarge the nonnegative majorant integral to $(1,\infty)$, which has an explicit value. The triangle inequality combines this Gaussian-series error with the previously proved infinite-time tail. The normalization follows the actual Xi identity throughout.

This theorem removes both infinite tails, but the finite numerical quadrature and F(48) lower bound remain unproved.

## Lean artifacts

`XiThetaFiniteIntegralFull.lean`: `continuousOn_realThetaFiniteIntegrand`, `integrableOn_realThetaFiniteIntegrand`, `realThetaCosineIntegral_finite_sum_error`, `F_real_finite_theta_sum_integral_error`.

