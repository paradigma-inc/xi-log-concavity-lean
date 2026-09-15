# Euler-accelerated eta kernel

## Statement

Let $w_{N,j}=2^{-N}\sum_{j<k\le N}\binom Nk$ and $P_N(x)=\sum_{j<N}(-1)^j w_{N,j}x^{j+1}$. For $x\ne-1$,
$$P_N(x)=\frac{x}{1+x}\left(1-\left(\frac{1-x}{2}\right)^N\right).$$
For $0\le x\le1$, the polynomial is nonnegative and at most $x$, and
$$0\le\frac{x}{1+x}-P_N(x)\le2^{-N}x.$$
The exact bound $2^{-400}<10^{-120}$ is kernel checked. The weighted Euler kernel $t^{s-1}P_N(e^{-t})$ is integrable on the positive half-line for every $s>0$; its pointwise error is bounded by $2^{-N}t^{s-1}e^{-t}$.

## Assumptions

The algebraic identity only excludes $x=-1$. The pointwise inequalities use $x\in[0,1]$; weighted integrability uses $s>0$. No special-function approximation or numerical oracle is assumed.

## Proof Sketch

Exchanging the two finite sums expresses the polynomial as a binomially weighted sum of finite geometric sums. Evaluating those sums and applying the binomial theorem gives the identity. On the unit interval its remainder has the displayed positive product form, with ratio between zero and one half. Multiplication by the nonnegative weight $t^{s-1}$ transfers the estimates to the positive half-line; the actual Euler Gamma integrand supplies an integrable majorant. The numerical bound follows from $10^3<2^{10}$ by taking the fortieth power and reciprocals.

These are bounds on the exact finite kernel, not yet a certificate for Xi samples or the global density theorem. The separate acceleration module proves the finite power-sum integral identity and integrated error.

## Lean Artifacts

`EtaEulerFull.lean`, namespace `ReciprocalXi`: `etaEulerPolynomial_identity`, `etaEulerPolynomial_remainder_bounds`, `eta_euler_400_error_lt`, `integrableOn_etaEulerIntegrand`, `etaEulerIntegrand_remainder_bounds`.
