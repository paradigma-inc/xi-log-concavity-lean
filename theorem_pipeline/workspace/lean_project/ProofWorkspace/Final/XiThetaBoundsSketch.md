# Actual theta bounds for the central Xi interval

The Gaussian-series identity in mathlib gives
$\theta(t)-1=2\sum_{n\ge0}\exp(-\pi(n+1)^2t)$, with
$\theta(t)=\operatorname{cosKernel}(0,t)$. The existing convergent Gaussian
tail estimate bounds the sum by $e^{-\pi t}/(1-e^{-\pi t})$.
For $t\ge1$, $\pi\ge2$ and $e^x\ge1+x$ imply $e^{-\pi t}\le1/2$.
Consequently $|\theta(t)-1|\le4e^{-\pi t}$ on that whole interval.

For complex $s$ with $\operatorname{Re}s\le1$, define
$J_s(t)=t^{s-1}(\theta(t)-1)$ on $t>1$. The complex-power norm identity
gives $|t^{s-1}|=t^{\operatorname{Re}s-1}\le1$.
Thus $|J_s(t)|\le4e^{-\pi t}$. Continuity on this half-line supplies
measurability, and domination by this exponential proves integrability.
Integrating the bound yields
$|\int_1^\infty J_s(t)\,dt|\le4e^{-\pi}/\pi<2$.

Every bound is attached to mathlib's actual theta kernel. No sampled values,
floating-point evaluator, zero-location assumption, or numerical certificate
is used. The separate Mellin-identity module must still connect the upper
integrals to the actual pole-removed completed zeta; this module does not
assume or claim that identity.
