# Fourier transform of the two-Laplace kernel

## Statement

For $0<a<b$, put $C=ab/(2(b^2-a^2))$. The existing real kernel
$K(x)=C(be^{-a|x|}-ae^{-b|x|})$ is integrable and has angular Fourier transform
$$
\int K(x)e^{iux}\,dx=
\frac{a^2}{a^2+u^2}\frac{b^2}{b^2+u^2}.
$$
The unnormalized formula for arbitrary real $C$ is also proved.

## Assumptions

Positivity and strict ordering of the real rates are explicit. This uses the exact kernel already present in the tail-remainder proof.

## Proof Sketch

Split the kernel transform into its two Laplace-atom transforms. Their established integrability justifies linearity of the integral. Substitute the verified atom formula, then simplify with the exact normalization. All denominators are nonzero by positivity and strict ordering. The zero-frequency integrability result also supplies integrability of the real kernel.

## Lean Artifacts

- File: `ProofWorkspace/Final/TwoLaplaceFourierFull.lean`
- Theorems: `twoLaplace_character_split`, `integrable_twoLaplace_character`, `integral_twoLaplace_character`, `integral_twoLaplace_normalized_character`, `integrable_twoLaplace_kernel`.
