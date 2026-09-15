# Gaussian variance mixture

## Statement and assumptions

Given a real probability law $\nu$, construct the law of $\sqrt{2S}Z$ on the actual product of $\nu$ and a standard Gaussian. This is a probability measure. If $\nu$ is supported on nonnegative values, its characteristic function is $L_\nu(u^2)$, the Laplace transform of $\nu$ at $u^2$.

## Proof Sketch

The product law is a probability measure and the scale map is measurable, so its pushforward is a probability measure. For each $s\ge0$, the library's Gaussian characteristic function and $(\sqrt{2s})^2=2s$ give $e^{-u^2s}$. The joint characteristic integrand has modulus one, so Fubini is justified. Integrating the conditional Gaussian formula against $\nu$ yields its Laplace transform.

No moment assumption beyond the stated support and probability hypotheses is needed for this bounded characteristic-function identity. Exponential moments are not asserted.

## Lean Artifacts

File: `GaussianVarianceMixtureFull.lean`. Theorems: `gaussianVarianceMixture_isProbability`, `integral_gaussian_scaled_character`, and `charFun_gaussianVarianceMixture`.
