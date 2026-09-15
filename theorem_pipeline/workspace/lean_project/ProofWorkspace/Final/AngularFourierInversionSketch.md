# Fourier inversion with the source's angular-frequency convention

## Statement

Define $\widehat f(u)=\int f(x)e^{iux}\,dx$ and
$\mathcal I g(x)=(2\pi)^{-1}\int g(u)e^{-ixu}\,du$.
If $f$ and $\widehat f$ are integrable, then $\mathcal I\widehat f(x)=f(x)$ at every continuity point of $f$.

## Assumptions

Integrability of the function and its angular Fourier transform, and continuity at the evaluated point, are explicit.

## Proof Sketch

Relate the angular-frequency transform to mathlib's Fourier transform by the exact substitution $u=-2\pi v$. The same change of variables identifies the angular inverse, including its normalization, with mathlib's inverse Fourier transform of the rescaled function. Integrability is preserved by the nonzero scaling. The verified Fourier inversion theorem then gives the result.

## Lean Artifacts

- File: `ProofWorkspace/Final/AngularFourierInversionFull.lean`
- Theorems: `fourier_eq_angularFourier`, `angularInverse_eq_fourierInv`, `angularInverse_angularFourier_eq`.
