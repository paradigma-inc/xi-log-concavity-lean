# Actual finite Euler-accelerated eta error

## Statement

Define the finite approximation
$$\eta_N(s)=\sum_{j<N}\frac{(-1)^j w_{N,j}}{(j+1)^s}.$$
For every real $s>0$, the proved eta integral satisfies
$$0\le\eta_{\mathrm{integral}}(s)-\eta_N(s)\le2^{-N}.$$
In particular $\eta_{400}(s)\le\eta_{\mathrm{integral}}(s)<\eta_{400}(s)+10^{-120}$. For $s>0$, $s\ne1$, this also bounds the actual regularized zeta value $(1-2^{1-s})\operatorname{Re}\zeta(s)$.

## Assumptions

Only $s>0$ is required for the integral and finite approximation bounds. The initial zeta corollary requires $s>1$; the stronger corollary uses the proved analytic continuation and only requires $s>0$, $s\ne1$. It makes no assertion about the product of totalized zeta with its vanishing factor at the pole.

## Proof Sketch

The finite Euler kernel is a finite linear combination of Laplace kernels. Each has a proved integrable majorant and its normalized integral equals $(j+1)^{-s}$ by the actual Gamma integral and change of variable. Thus the normalized finite-kernel integral is exactly $\eta_N(s)$, with no interchange assumption. The kernel remainder from `EtaEulerFull` is nonnegative and bounded by $2^{-N}$ times the Gamma integrand. Integrating this inequality and dividing by the positive value $\Gamma(s)$ gives the error estimate. The exact rational comparison for $N=400$ gives the stated numerical enclosure. The final zeta corollary substitutes the actual identity proved in `EtaIntegralFull` on $s>1$.

This does not certify Gamma numerical values, elementary rounding, retained Xi nodes, panel coefficients, or the global log-concavity theorem.

## Lean Artifacts

`EtaAccelerationFull.lean`, namespace `ReciprocalXi`: `integral_etaEulerIntegrand`, `etaIntegral_euler_error_bounds`, `etaIntegral_euler_400_error`, `etaIntegral_euler_400_enclosure`, `riemannZeta_euler_error_bounds`, `riemannZeta_euler_error_bounds_of_pos`.
