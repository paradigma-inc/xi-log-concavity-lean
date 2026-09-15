# Finite Gaussian expansion of the actual theta kernel

## Statement and assumptions

For $N\in\mathbb N$ and $t\ge1$, truncating the actual theta kernel after its first $N$ positive Gaussian terms has error at most $4e^{-\pi(N+1)^2t}$. The same bound holds after multiplying by $t^{-3/4}\cos((x/4)\log t)$ for any real $x$.

## Proof sketch

Split the absolutely convergent actual Gaussian series into a finite initial sum and its shifted tail. The library's geometric majorant bounds the shifted tail by $e^{-\pi(N+1)^2t}/(1-e^{-\pi t})$. On $t\ge1$, the reciprocal denominator is at most two; the theta kernel's factor two gives the stated constant four. The real cosine multiplier has absolute value at most one, so it cannot increase the error.

No numerical approximation or finite-zero statement is assumed. Integrating and evaluating the finite expression remain separate tasks.

## Lean artifacts

`XiThetaFiniteSumFull.lean`: `cosKernel_zero_finite_sum_tail`, `cosKernel_zero_finite_sum_error`, `realThetaCosineIntegrand_finite_error`; definition `realThetaFiniteIntegrand`.

