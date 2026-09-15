# Actual reciprocal-Xi density as a convolution

## Statement and assumptions

For two actual positive zero occurrences of $F$ with real roots $0<a<b$, suppose the remaining heat trace is nonnegative. The actual density is the convolution of the constructed residual probability law with
$$K(x)=\frac{ab}{2(b^2-a^2)}(b e^{-a|x|}-a e^{-b|x|}).$$
It is strictly positive on the real line. The last theorem replaces heat positivity by the explicit finite low-zero reality certificate and an eligible remaining root; this certificate is not proved in this module.

## Proof Sketch

The actual finite-deletion transform identity cancels the two rational Laplace factors exactly. Their inverse transform is the displayed kernel, and justified Fubini transfers multiplication by the residual characteristic function to convolution. The complex inverse integral is already known to be real, so it is precisely the density defined from reciprocal Xi. The kernel is everywhere positive and bounded, and the residual measure is a probability measure. Its integral is therefore strictly positive. The finite-certificate heat lower bound supplies the final corollary.

No density identity, residual measure existence, or Fourier inversion is assumed. The low-zero certificate remains an explicit mathematical obligation; global curvature positivity is not asserted.

## Lean artifacts

- `XiDensityConvolutionFull.lean`
- `reciprocalTransform_twoLaplace_residual`
- `density_eq_twoLaplace_convolution`
- `density_pos_of_two_real_roots`
- `density_pos_of_finite_zero_certificate`
