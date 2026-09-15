# Explicit Fourier integrals for every actual density derivative

Companion: `XiFourierJetsFull.lean`, namespace `ReciprocalXi`.

## Statement

Let $\varphi(u)=F(0)/F(iu)$ be the actual reciprocal transform and let
$g=\texttt{density}$ be the actual inverse Fourier density defined earlier.
For every natural $n$ and real $x$, the module proves

$$
g^{(n)}(x)=\frac{1}{2\pi}\Re\int_{\mathbb R}
(-iu)^n\varphi(u)e^{-ixu}\,du.
$$

Here $g^{(n)}$ is the actual $n$-fold iteration of Lean's derivative operator,
not a separately supplied jet. The integral on the right is absolutely
convergent. In particular,

$$
g'(x)=\frac{1}{2\pi}\Re\int_{\mathbb R}
(-iu)\varphi(u)e^{-ixu}\,du,
\qquad
g''(x)=\frac{1}{2\pi}\Re\int_{\mathbb R}
-u^2\varphi(u)e^{-ixu}\,du.
$$

There are no additional differentiability, moment, positivity, or
zero-free-region assumptions. The required actual moments and
integrability were proved in `XiFourierFull` from the real-axis Xi estimates.

## Proof Sketch

Define $w_n(u)=(-iu)^n\varphi(u)$ and
$J_n(x)=\mathcal F(w_n)(x/(2\pi))$, using mathlib's Fourier convention
$\mathcal F f(t)=\int e^{-2\pi iut}f(u)\,du$. The exact identity
$|w_n(u)|=|u|^n|\varphi(u)|$ and the already proved moment theorem imply
integrability of both $w_n$ and $u w_n$.

The library Fourier derivative theorem therefore applies without extra
analytic premises. Its multiplier is $-2\pi iu$, so differentiating
$\mathcal F(w_n)$ gives $2\pi\mathcal F(w_{n+1})$. The derivative of the
rescaling $x/(2\pi)$ cancels this factor exactly, yielding
$J_n'(x)=J_{n+1}(x)$. Applying the real-part linear map and division by
$2\pi$ produces the corresponding derivative recurrence for the real
jets. The zeroth jet equals the original density by the previously proved
Fourier normalization identity; induction now identifies every jet with
the actual iterated derivative of $g$.

Expanding the Fourier transform recovers the displayed integral, including
its negative sign and normalization. The exponential factor has unit norm
for real $x,u$, so each integrand has exactly the same integrable norm as
$w_n$. The second-order formula uses $(-iu)^2=-u^2$.

## Main declarations

- `integrable_densityJetWeight`
- `integrable_mul_densityJetWeight`
- `hasDerivAt_complexDensityJet`
- `hasDerivAt_densityJet`
- `iterated_deriv_density_eq_densityJet`
- `iterated_deriv_density_eq_integral`
- `deriv_density_eq_integral`
- `second_deriv_density_eq_integral`
- `integrable_densityJet_integrand`

## Scope

These formulas concern the actual density and can be used by a later
compact-interval quadrature certificate. They do not themselves establish
any numerical enclosure, positive curvature, positive density, contour
shift, or complex-strip decay bound. No such conclusion is assumed.

Source context:
`theorem_pipeline/workspace/contexts/reciprocal_xi_global_logconcavity.md`.
The Fourier derivative theorem is from the pinned mathlib
`Analysis.Fourier.FourierTransformDeriv` module.

No `sorry`, custom axiom, or `native_decide` is used.
