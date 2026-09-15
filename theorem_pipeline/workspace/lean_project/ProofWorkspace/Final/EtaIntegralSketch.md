# Actual eta integral and its absolutely convergent zeta identity

## Statement

The module defines the real eta integral by

$$
\eta_I(s)=\frac{1}{\Gamma(s)}\int_0^\infty
\frac{t^{s-1}e^{-t}}{1+e^{-t}}\,dt.
$$

`integrableOn_etaIntegrand` proves existence of this integral for every real $s>0$. For $s>0$ and $r>0$, `etaLaplaceIntegral` and `etaLaplaceIntegral_normalized` prove the exact identities

$$
\int_0^\infty t^{s-1}e^{-rt}\,dt=\frac{\Gamma(s)}{r^s},
\qquad
\frac{1}{\Gamma(s)}\int_0^\infty t^{s-1}e^{-rt}\,dt=r^{-s}.
$$

`integrableOn_etaLaplace` separately proves convergence of each Laplace integral. `etaLaplaceIntegral_nat` specializes the normalized identity to $r=n+1$.

For $s>1$, `hasSum_etaIntegral` proves the absolutely convergent series identity

$$
\eta_I(s)=\sum_{n=0}^\infty\frac{(-1)^n}{(n+1)^s}.
$$

Finally, `etaIntegral_eq_riemannZeta` proves, for the actual mathlib Riemann zeta function,

$$
\eta_I(s)=(1-2^{1-s})\operatorname{Re}\zeta(s),\qquad s>1.
$$

## Assumptions

The integral-existence and Laplace formulas require only the indicated positive real parameters. The zeta identity requires $s>1$. No eta formula, exchange of sum and integral, summability, or numerical approximation is assumed.

## Proof Sketch

On the positive half-line the eta integrand is nonnegative and bounded above by $t^{s-1}e^{-t}$. The latter is the convergent Euler Gamma integrand when $s>0$, and local continuity supplies measurability. The scaled Laplace identity follows from the actual Euler Gamma integral by its proved positive-real change of variable. The corresponding integrability is verified independently using the same scaling, and division by the proved positive value $\Gamma(s)$ gives the normalized formulas.

For $t>0$, the geometric series with ratio $-e^{-t}$ gives

$$
\frac{t^{s-1}e^{-t}}{1+e^{-t}}
=\sum_{n=0}^\infty(-1)^n t^{s-1}e^{-(n+1)t}.
$$

The integral of the absolute value of the $n$th term is exactly $\Gamma(s)/(n+1)^s$. These integrals form a summable positive series for $s>1$. The proved absolute-integrability interchange theorem therefore permits termwise integration, and the normalized Laplace identity gives the alternating Dirichlet series without assuming the interchange.

The actual zeta Dirichlet series in the half-plane of absolute convergence is converted from complex powers to positive real powers. Splitting its shifted real series into even and odd indices, the odd-index contribution is $2^{-s}$ times the full series. The alternating series is the full series minus twice that contribution, yielding the factor $1-2^{1-s}$.

## Scope

This module does not identify $\eta_I(s)$ with analytically continued zeta on $0<s\le1$. Integral existence is proved there, but the absolutely convergent series argument cannot be reused there. A separate analytic-continuation proof is required before these integral formulas can certify central-strip zeta samples. No finite Euler acceleration, numerical samples, density positivity, or curvature assertion is claimed here.

## Lean Artifacts

- Full proof: `ProofWorkspace/Final/EtaIntegralFull.lean`.
- Definitions: `etaIntegrand`, `etaIntegral`.
- Theorems: `integrableOn_etaIntegrand`, `etaLaplaceIntegral`, `integrableOn_etaLaplace`, `etaLaplaceIntegral_normalized`, `etaLaplaceIntegral_nat`, `hasSum_etaIntegrand_laplace`, `hasSum_etaIntegral`, `riemannZeta_re_eq_tsum_rpow`, `etaIntegral_eq_riemannZeta`.
- Namespace: `ReciprocalXi`.
- Source context: the existing reciprocal-Xi finite evaluation material and `theorem_pipeline/workspace/prompts/eta_evaluator.txt`.
- Tracked run: `20260909T184117Z_fe26`.
