# Actual Cauchy bounds and geometric Taylor errors

Companion: `DensityCauchyBoundsFull.lean`, namespace `ReciprocalXi`.

## Statement

Let $G$ be the actual entire inverse Fourier density and let
$\varphi(u)=F(0)/F(iu)$. Define the finite, nonnegative majorant

$$
M(c,R)=\frac1{2\pi}\int_{\mathbb R}
e^{(|\Im c|+R)|u|}|\varphi(u)|\,du.
$$

For $|z-c|\leq R$, the module proves $|G(z)|\leq M(c,R)$.
For every $R>0$ and natural $n$, it then proves the actual Cauchy estimate

$$
|G^{(n)}(c)|\leq\frac{n!M(c,R)}{R^n},
\qquad
|a_n(c)|\leq\frac{M(c,R)}{R^n},
\quad a_n(c)=\frac{G^{(n)}(c)}{n!}.
$$

The coefficients are defined from actual complex derivatives. Set
$P_N(c,z)=\sum_{n=0}^{N-1}a_n(c)(z-c)^n$.
For $R>0$ and $|z-c|<R$, write $q=|z-c|/R<1$. The certified error is

$$
|G(z)-P_N(c,z)|\leq\frac{M(c,R)q^N}{1-q}.
$$

All integrability, holomorphy, and boundary bounds are derived from the
actual reciprocal transform; they are not premises. For real centers,
$M(c,R)=M(0,R)$, so the same analytic majorant works across the real axis.

## Proof Sketch

If $|z-c|\leq R$, projection onto the imaginary coordinate and the
triangle inequality give $|\Im z|\leq|\Im c|+R$. The exact norm of the
Fourier exponential is
$|e^{-izu}|=e^{(\Im z)u}$, which is at most
$e^{(|\Im c|+R)|u|}$. Applying the integral norm inequality yields the
disk bound. The majorizing integrand is integrable because every
exponentially weighted actual reciprocal transform is already proved
integrable. Its nonnegativity proves $M(c,R)\geq0$.

The function $G$ was proved entire in `ComplexDensityFull`. Consequently
it is differentiable in every disk and continuous on the closure. Applying
mathlib's Cauchy derivative estimate to the boundary circle, with the
just-derived actual disk majorant, gives the derivative bound. Division
by the positive integer $n!$ gives the coefficient estimate.

The library's Taylor theorem for entire functions identifies the sum of
$a_n(c)(z-c)^n$ with $G(z)$. The coefficient bound yields the geometric
term estimate $|a_n(c)(z-c)^n|\leq M(c,R)q^n$.
Removing the first $N$ terms leaves a convergent series whose term norms
are bounded by $M(c,R)q^Nq^k$. Summing this geometric majorant proves the
displayed remainder estimate. This also handles $N=0$ without a separate
case.

## Main declarations

- `densityDiskMajorant`
- `integrable_densityDiskMajorant_integrand`
- `densityDiskMajorant_nonneg`
- `densityDiskMajorant_ofReal`
- `complexDensity_norm_le_diskMajorant`
- `complexDensity_iteratedDeriv_norm_le`
- `densityTaylorCoefficient_norm_le`
- `hasSum_densityTaylor`
- `densityTaylor_term_norm_le`
- `densityTaylorPolynomial`
- `complexDensity_taylor_remainder_le`

## Scope

These theorems provide the analytic meaning of actual Taylor
coefficients and truncation errors. They do not evaluate $M(c,R)$,
enclose the coefficients by the source's recorded rational intervals,
or identify the recorded polynomial certificate with this actual Taylor
polynomial. Those are separate numerical obligations. No density
positivity or curvature conclusion is assumed or proved here.

Normalized source:
`theorem_pipeline/workspace/contexts/reciprocal_xi_global_logconcavity.md`.
The library inputs are the pinned mathlib modules
`Analysis.Complex.Liouville` and `Analysis.Complex.TaylorSeries`.

No `sorry`, custom axiom, or `native_decide` is used.
