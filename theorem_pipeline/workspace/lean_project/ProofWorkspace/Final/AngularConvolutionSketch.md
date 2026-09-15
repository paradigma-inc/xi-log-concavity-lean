# Angular inverse transform of a characteristic-function product

## Statement

For an integrable complex function $f$ and a probability measure $\mu$,
$$
\mathcal I(f\,\widehat\mu)(x)=\int \mathcal I f(x-y)\,d\mu(y),
$$
with the exact angular-frequency inverse convention of the source.

## Assumptions

The frequency function is integrable and the measure is a probability law. No density, continuity or moment hypothesis is required.

## Proof Sketch

Expand the characteristic function as its defining integral. The two complex phases have modulus one, so the product integrand is dominated on the product space by the integrable function $|f(u)|$. Fubini therefore applies. Combining the two phases gives the inverse phase at $x-y$, and linearity preserves the exact $2\pi$ normalization.

## Lean Artifacts

- File: `ProofWorkspace/Final/AngularConvolutionFull.lean`
- Theorems: `integrable_angular_character_product`, `angularInverse_mul_charFun`.
