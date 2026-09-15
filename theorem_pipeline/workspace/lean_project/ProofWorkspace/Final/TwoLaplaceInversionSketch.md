# Exact inversion of the two-Laplace multiplier

## Statement

For $0<a<b$, the rational multiplier
$$
m(u)=\frac{a^2}{a^2+u^2}\frac{b^2}{b^2+u^2}
$$
is integrable and its angular inverse is the existing two-Laplace kernel with $C=ab/(2(b^2-a^2))$.

## Assumptions

Both rates are real, positive and strictly ordered. No Fourier-inversion formula specific to the kernel is assumed.

## Proof Sketch

A rescaling of the integrable function $(1+u^2)^{-1}$ proves integrability of the first rational factor. The second factor lies between zero and one, proving integrability of their product. The kernel is continuous and integrable by its explicit two-exponential expression. Its previously verified Fourier transform is exactly the rational multiplier, so the verified angular Fourier inversion theorem applies at every point.

## Lean Artifacts

- File: `ProofWorkspace/Final/TwoLaplaceInversionFull.lean`
- Theorems: `integrable_laplace_multiplier`, `integrable_twoLaplaceMultiplier`, `angularFourier_twoLaplace`, `angularInverse_twoLaplaceMultiplier`.
