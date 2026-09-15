# Complex finite theta integrand

## Statement

The function $z^{-3/4+ix/4}2\sum_{n=1}^N e^{-\pi n^2z}$ is holomorphic for $\operatorname{Re}z>0$. Its real part at a positive real argument equals the finite real theta integrand. When $\operatorname{Re}z\ge1/2$, its norm is at most $4N e^{|x|\pi/8}$; at $x=48,N=4$, this is at most $10^{14}$.

## Assumptions

Only the stated half-plane bounds are required. There are no numerical or zero-location hypotheses.

## Proof Sketch

The principal complex power is holomorphic in the right half-plane. Its norm is controlled by the real power of the modulus and the argument, whose absolute value is at most $\pi/2$. Each Gaussian exponential has norm at most one. Summing gives the bound; elementary bounds on $\pi$ and $e$ give the concrete majorant. Expanding the real part on positive real inputs proves the exact real-integrand identity.

## Lean Artifacts

- Full proof: `XiThetaComplexFull.lean`
- Theorems: `complexThetaExponent_re`, `complexThetaExponent_im`, `complexThetaFiniteIntegrand_differentiableAt`, `complexThetaFiniteIntegrand_re`, `complexThetaFiniteIntegrand_norm_le`, `complexThetaFiniteIntegrand_48_norm_le`.
