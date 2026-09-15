# Actual reciprocal-Xi exponential integral

## Statement

The actual reciprocal transform satisfies $\varphi(u)=\exp D(u)$, where
$$D(u)=\int_0^\infty \frac{e^{-u^2t}-1}{t} H(t)\,dt$$
and $H(t)$ is the actual multiplicity-weighted zero heat trace.

## Assumptions

Only $u\in\mathbb R$; no low-zero reality certificate, RH, or positive measure is assumed. The trace is not asserted nonnegative.

## Proof Sketch

The real kernel has absolute value at most $u^2$, so the previously proved integrability of $H$ makes $D$ integrable. Its derivative has a locally uniform integrable bound $2(|u|+1)|H(t)|$. Differentiating under the integral identifies $D'$ with the actual reciprocal transform's logarithmic derivative. The derivative of $\varphi\exp(-D)$ vanishes, and its value at zero is one. This proves the exponential identity without assuming a probability-law representation.

## Lean Artifacts

- File: `XiHeatExponentFull.lean`
- Main theorem: `ReciprocalXi.reciprocalTransform_eq_exp_heatExponent`
- Supporting derivative theorem: `ReciprocalXi.F_heatExponent_hasDerivAt`
