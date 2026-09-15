# Actual eta continuation through the positive half-plane

## Statement

The module defines the actual complex Mellin extension

$$
\eta_C(s)=\frac{1}{\Gamma(s)}\int_0^\infty
t^{s-1}\frac{e^{-t}}{1+e^{-t}}\,dt.
$$

The complex power is mathlib's standard principal power, evaluated on positive real $t$. The integral converges and $\eta_C$ is holomorphic for $\operatorname{Re}s>0$. Its restriction to the real axis is the real integral $\eta_I$ already defined in `EtaIntegralFull`.

`complexEtaIntegral_regularized` proves the actual identity throughout this entire half-plane, including $s=1$,

$$
(s-1)\eta_C(s)=
(1-2^{1-s})\frac{2\xi(s)}{s\Gamma_{\mathbb R}(s)}.
$$

Here $\xi$ is the previously defined actual entire completed Xi function and $\Gamma_{\mathbb R}$ is mathlib's completed-zeta Gamma factor. Consequently, `complexEtaIntegral_eq_riemannZeta` proves

$$
\eta_C(s)=(1-2^{1-s})\zeta(s)
\qquad (\operatorname{Re}s>0,\ s\ne1).
$$

For real $s>0$, $s\ne1$, `etaIntegral_eq_riemannZeta_of_pos` gives the evaluator's real identity

$$
\eta_I(s)=(1-2^{1-s})\operatorname{Re}\zeta(s).
$$

## Assumptions

The analytic identities require only the stated positive real part; division by $s-1$ additionally requires $s\ne1$. No analytic-continuation identity, unproved convergence, or regularity hypothesis is assumed. The real agreement theorem follows from equality of the defining integrands even outside the convergence region, where mathlib integrals are total; its analytic use here is restricted to the proved convergent region.

## Proof Sketch

For the actual kernel $k(t)=e^{-t}/(1+e^{-t})$, direct positivity estimates give $|k(t)|\le e^{-t}$ and $|k(t)|\le1$. The kernel is continuous. These estimates establish exponential decay at infinity, boundedness at the origin, and local integrability. Mathlib's proved Mellin-transform convergence and holomorphy theorems then give convergence and holomorphy on $\operatorname{Re}s>0$. The reciprocal Gamma function is entire, so normalization by it preserves holomorphy. On the real axis, positive-base complex powers agree exactly with real powers, and commuting the real embedding with the integral identifies $\eta_C$ with $\eta_I$.

For real $s>1$, the earlier absolutely convergent eta identity and the actual real-valued zeta Dirichlet series establish the displayed regularized identity. The ordinary Xi formula $2\xi(s)=s(s-1)\Gamma_{\mathbb R}(s)\zeta(s)$ is used only away from its removable points. Both sides of the regularized identity are analytic on the whole right half-plane: on the right, $1/s$ is holomorphic there, reciprocal $\Gamma_{\mathbb R}$ is entire, and the remaining Xi and constant-base power factors are entire. In particular, neither side has a puncture at $s=1$.

The right half-plane is convex and hence connected. The two analytic functions agree at the explicit sequence $2+1/(n+1)$, whose distinct points converge to the interior point $2$. The proved analytic identity principle extends their equality throughout the half-plane. Finally, for $s\ne1$, nonvanishing of $s$, $s-1$, and $\Gamma_{\mathbb R}(s)$ permits cancellation and yields the actual zeta identity. Taking real parts gives the real evaluator formula.

## Scope

This closes the eta-to-zeta identification on the evaluator's entire positive real domain except $s=1$. The removable Xi value at that point is independently known exactly as $\xi(1)=1/2$; no evaluation of $\eta(1)=\log2$ is needed or claimed. This module supplies no finite numerical enclosure by itself. Finite Euler acceleration and its certified arithmetic remain separate steps.

## Lean Artifacts

- Full proof: `ProofWorkspace/Final/EtaContinuationFull.lean`.
- Definitions: `etaKernel`, `complexEtaIntegral`, `etaRegularizedXi`.
- Main theorems: `mellinConvergent_etaKernel`, `differentiableAt_complexEtaIntegral`, `complexEtaIntegral_ofReal`, `complexEtaIntegral_regularized`, `complexEtaIntegral_eq_riemannZeta`, `etaIntegral_eq_riemannZeta_of_pos`.
- Supporting theorems: `continuous_etaKernel`, `etaKernel_norm_le_exp`, `etaKernel_norm_le_one`, `etaKernel_isBigO_exp`, `etaKernel_isBigO_zero`, `riemannZeta_ofReal_eq_re_of_one_lt`, `complexEtaIntegral_regularized_ofReal`, `differentiableAt_etaRegularizedXi`.
- Namespace: `ReciprocalXi`.
- Source: existing reciprocal-Xi finite evaluation material and `theorem_pipeline/workspace/prompts/eta_evaluator.txt`.
- Tracked run: `20260909T184117Z_fe26`.
