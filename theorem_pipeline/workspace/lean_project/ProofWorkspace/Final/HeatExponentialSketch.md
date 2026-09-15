# Exponential moments of the actual heat-density law

## Statement

For integrable nonnegative $H$ on $(0,\infty)$ and $q\ge0$, suppose
$((e^{qt}-1)/t)H(t)$ is integrable. The actual law constructed from the positive Lévy density $H(t)/t$ then has an integrable exponential and
$$
\mathbb E e^{qS}=\exp\!\left(\int_0^\infty \frac{e^{qt}-1}{t}H(t)\,dt\right).
$$

## Assumptions

Integrability and nonnegativity of the original heat density, and integrability of its exponential kernel, are explicit. No exponential moment of the constructed law is assumed.

## Proof Sketch

The with-density integrability equivalence converts the heat-kernel assumption into integrability of $e^{qt}-1$ for the positive Lévy measure. The verified S-finite Lévy exponential theorem then establishes the law's exponential integrability and moment. Finally the exact with-density integral identity converts its exponent back to the stated heat integral.

## Lean Artifacts

- File: `ProofWorkspace/Final/HeatExponentialFull.lean`
- Theorems: `integrable_heatLevy_exponential_kernel`, `heatSubordinatorLaw_exponentialMoment`.
