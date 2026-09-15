# Symmetry and absolute exponential moments of the Gaussian mixture

## Statement

The constructed Gaussian variance mixture is preserved by negation. If its mixing law has finite moment at $q^2$, then the mixture has an integrable $e^{q|y|}$ and
$$
\int e^{q|y|}\,d\mu(y)\le 2\int e^{q^2s}\,d\nu(s).
$$

## Assumptions

The mixing law is a probability law supported almost everywhere on nonnegative reals, with the explicitly stated exponential integrability. General two-sided inequalities also hold for an arbitrary measure with both one-sided exponential integrals finite.

## Proof Sketch

Uniqueness of characteristic functions establishes symmetry because the verified mixture transform depends only on the square of the frequency. Pointwise, $e^{q|y|}\le e^{qy}+e^{-qy}$. The two integrable one-sided exponentials therefore dominate the absolute exponential, proving its integrability and its integral bound. Both one-sided Gaussian-mixture moments equal the mixing moment at $q^2$.

## Lean Artifacts

- File: `ProofWorkspace/Final/GaussianMixtureAbsoluteFull.lean`
- Theorems: `exp_mul_abs_le_two_sided`, `integrable_exp_abs_of_two_sided`, `integral_exp_abs_le_two_sided`, `gaussianVarianceMixture_even`, `gaussianVarianceMixture_absoluteMoment`.
