# Exponential moments of a Gaussian variance mixture

## Statement

For a nonnegative mixing probability law $\nu$ and real $q$, integrability of $e^{q^2s}$ under $\nu$ implies integrability of $e^{qy}$ under the actual Gaussian mixture, and
$$
\mathbb E e^{qY}=\int e^{q^2s}\,d\nu(s).
$$

## Assumptions

The mixing measure is a probability measure supported almost everywhere on $[0,\infty)$, with the stated finite exponential moment. The mixture is the existing product-measure pushforward under $(s,z)\mapsto\sqrt{2s}\,z$.

## Proof Sketch

The standard Gaussian moment-generating formula evaluates the conditional exponential integral as $e^{q^2s}$. Each conditional exponential is integrable. Since the integrand is nonnegative, the assumed integrability of that conditional expectation verifies the product-integrability criterion. Only after establishing product integrability do Fubini and the pushforward integral formula give the asserted moment identity.

## Lean Artifacts

- File: `ProofWorkspace/Final/GaussianMixtureExponentialFull.lean`
- Theorems: `integrable_gaussian_scaled_exponential`, `integral_gaussian_scaled_exponential`, `integrable_exp_gaussianVarianceMixture`, `exponentialMoment_gaussianVarianceMixture`.
