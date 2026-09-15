# Entire extension of the actual inverse Fourier density

Companion: `ComplexDensityFull.lean`, namespace `ReciprocalXi`.

## Statement

For the actual reciprocal transform $\varphi(u)=F(0)/F(iu)$, define

$$
G(z)=\frac1{2\pi}\int_{\mathbb R}\varphi(u)e^{-izu}\,du,
\qquad z\in\mathbb C.
$$

The defining integral is absolutely convergent at every complex $z$.
The module proves that $G$ is entire and, for every natural $n$,

$$
G^{(n)}(z)=\frac1{2\pi}\int_{\mathbb R}(-iu)^n\varphi(u)e^{-izu}\,du.
$$

Every integral in this formula is absolutely convergent, and the left-hand
side is the actual iterated complex derivative. On the real axis,
$G(x)=g(x)$, where $g=\texttt{density}$ is the original real inverse
Fourier density. This equality uses the previously proved fact that its
Fourier integral is real, not a newly assumed reality condition.

There are no further hypotheses. In particular, all exponential moment,
integrability, and differentiability inputs are proved for the actual
reciprocal transform.

## Proof Sketch

Write $J_n(z,u)=(-iu)^n\varphi(u)e^{-izu}$. The elementary exponential
series estimate $|u|^n\leq n!e^{|u|}$ and
$|e^{-izu}|\leq e^{|z||u|}$ give, whenever $|z|\leq q$,

$$
|J_n(z,u)|\leq n!e^{(q+1)|u|}|\varphi(u)|.
$$

The actual weighted transform $e^{a|u|}\varphi(u)$ was already proved
integrable for every real $a$ in `XiFourierFull`. Taking its norm and
multiplying by $n!$ therefore supplies an integrable majorant. Continuity
of the integrand as a function of real $u$ supplies its measurability, so
every integral jet exists absolutely at every complex argument.

For fixed $u$, direct differentiation of the complex exponential gives
$\partial_zJ_n(z,u)=J_{n+1}(z,u)$. On the unit ball around any fixed
$z_0$, the triangle inequality gives $|z|\leq|z_0|+1$, and hence the
derivative integrands admit the common integrable bound

$$
|J_{n+1}(z,u)|\leq(n+1)!e^{(|z_0|+2)|u|}|\varphi(u)|.
$$

The complex-scalar version of differentiation under a dominated
parameter integral now applies on that ball. Dividing by the constant
$2\pi$ gives the derivative recurrence between consecutive integral
jets. The zeroth jet is exactly the definition of $G$. This recurrence
first proves complex differentiability everywhere and then, by
induction, identifies every jet with the actual iterated derivative.

For real $x$, substituting $z=x$ in the definition of $G$ gives the
complex Fourier integral previously shown equal to the real density in
`XiFourierRealFull`. No real-part projection is discarded without proof.

## Main declarations

- `complexDensity`
- `integrable_complexDensityIntegrand`
- `integrable_complexDensity_integrand`
- `hasDerivAt_entireDensityJet`
- `complexDensity_ofReal`
- `hasDerivAt_complexDensity`
- `differentiable_complexDensity`
- `iterated_deriv_complexDensity_eq_entireDensityJet`
- `iterated_deriv_complexDensity_eq_integral`

## Scope

The result supplies an actual entire density with actual complex
derivative formulas. It does not establish positivity, positive
curvature, any contour-shift identity, or the numerical certificate's
analytic enclosures. Its proof uses exponential integrability on the
real Fourier axis, not an assumed complex-strip estimate.

Normalized source:
`theorem_pipeline/workspace/contexts/reciprocal_xi_global_logconcavity.md`.
The differentiation theorem is the pinned mathlib result
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` from
`Analysis.Calculus.ParametricIntegral`.

No `sorry`, custom axiom, or `native_decide` is used.
