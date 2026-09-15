# Actual reciprocal-Xi density: integrability and unit mass

## Statement and assumptions

`density_probability_of_threeLowZeroCertificate` proves that the actual density is Lebesgue integrable and its integral equals one, assuming the previously defined certificate for the three original low zeros. `density_probability_of_original_signs` needs only the six original endpoint signs. These signs remain explicit until their numerical certificates are complete; neither theorem assumes RH or a compact-grid enclosure.

## Proof sketch

At frequency zero, the proved exact Fourier formula for the normalized two-Laplace kernel reduces to unit integral. The kernel is absolutely integrable. Fubini's theorem therefore shows that its convolution with any probability measure remains integrable and has integral one. The existing actual-density identity expresses the inverse Fourier density as precisely this kernel convolved with the residual probability law. The low-zero certificate supplies the already-proved nonnegative residual heat trace, hence that law is a probability measure. Substitution proves the two claims for the actual density. Combined with the independently proved positivity and evenness, these are the source's probability-density properties.

The normalization does not establish global curvature, strict log-concavity or PF2 on its own. The unchanged source-grid, compact-panel and endpoint certificates remain required by the full target.

## Lean artifacts

- `XiDensityNormalizationFull.lean`
- `integral_twoLaplace_normalized_kernel`
- `integrable_laplaceConvolution_kernel`
- `integral_laplaceConvolution_normalized_kernel`
- `density_probability_of_threeLowZeroCertificate`
- `density_probability_of_original_signs`

The Full file is copied unchanged from the first passing scratch proof. Cumulative acceptance remains separate from individual checks.
