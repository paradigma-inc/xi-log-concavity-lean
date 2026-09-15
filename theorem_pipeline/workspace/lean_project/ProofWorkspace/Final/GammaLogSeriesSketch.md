# A convergent numerical series for the actual log Gamma function

## Statement

For $|z|\le1/2$, put
$$c_k(z)=\frac{(-1)^k}{k+2}\left(z^{k+2}-2z\,2^{-(k+2)}\right)$$
and
$$A_N(z)=z\log\pi-2z\log2+\sum_{k<N}c_k(z)\operatorname{Re}\zeta(k+2).$$
Then
$$|\log\Gamma(1+z)-A_N(z)|\le8\,2^{-(N+2)}.$$
The exact bound at $N=440$ is less than $10^{-130}$.

## Assumptions

Only $|z|\le1/2$ and a natural truncation length are required. Gamma and zeta are the actual library functions. No asymptotic expansion, Stirling remainder, Euler-constant value, floating-point evaluation or infinite interchange is assumed.

## Proof Sketch

In the finite Bohr-Mollerup log-Gamma sequences, take the combination at $1+z$, $3/2$ and $1$ with coefficients $1$, $-2z$ and $-(1-2z)$. The elementary normalization terms cancel exactly. The remaining finite sum has summands
$$2z\log\left(1+\frac1{2(n+1)}\right)-\log\left(1+\frac z{n+1}\right).$$
Its proved limit is $\log\Gamma(1+z)-2z\log\Gamma(3/2)$. Expand each logarithm using the library's finite Taylor remainder. The linear coefficients cancel, and the higher coefficients give the displayed $c_k(z)/(n+1)^{k+2}$. Each summand's truncation error is bounded by $4\,2^{-(N+2)}/(n+1)^2$. The finite reciprocal-square sum is at most two, uniformly in its length. Taking limits in this uniform finite-sum bound, using the actual absolutely convergent zeta series for each of the finitely many remaining coefficients, gives the error estimate. Finally $\Gamma(3/2)=\sqrt\pi/2$ replaces the last Gamma constant by elementary logarithms. The numerical $N=440$ bound is exact power arithmetic.

This gives an analytic evaluator formula, not yet a rational evaluation of its zeta/log coefficients or a retained-Xi node certificate. It is a sound alternative to formalizing the source's high-order Stirling remainder; the target Gamma function and Xi samples are unchanged.

## Lean Artifacts

`GammaLogSeriesFull.lean`, namespace `ReciprocalXi`: `gammaLogCorrection_sum`, `tendsto_gammaLogCorrection_sum`, `gammaLogCorrection_sum_error_bound`, `logGamma_series_error_bound`, `logGamma_approx_error_bound`, `logGamma_approx_440_error`.
