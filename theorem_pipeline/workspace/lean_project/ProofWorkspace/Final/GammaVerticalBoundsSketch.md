# A vertical lower bound for the actual Gamma function

Companion: `GammaVerticalBoundsFull.lean`, namespace `ReciprocalXi`.

## Statement

For every real $x\geq1$ and every real $t$, the module proves

$$
\Gamma(x)e^{-t^2}\leq |\Gamma(x+it)|.
$$

Equivalently, since the left-hand side is positive,

$$
\frac{\Gamma(x)}{|\Gamma(x+it)|}\leq e^{t^2}.
$$

Here the Gamma functions are mathlib's actual real and complex Gamma
functions. There is no assumed product identity, zero-free hypothesis,
or bound on $t$.

## Proof Sketch

For a positive real $s$, comparison of squared norms and the elementary
inequality $1+u\leq e^u$ give

$$
|s+it|=s\sqrt{1+t^2/s^2}
\leq s\exp\left(\frac{t^2}{2s^2}\right).
$$

The factor $1/2$ is retained by working with squared norms. For $x\geq1$,
termwise monotonicity of reciprocal squares, together with mathlib's
finite reciprocal-square estimate, gives

$$
\sum_{k=0}^{n-1}\frac1{(x+k)^2}
\leq\sum_{k=0}^{n-1}\frac1{(k+1)^2}\leq2.
$$

Multiplying the single-factor estimates and combining the exponentials
therefore proves the uniform finite denominator comparison

$$
\prod_{k=0}^{n-1}|x+k+it|
\leq e^{t^2}\prod_{k=0}^{n-1}(x+k).
$$

For each positive integer $n$, the Euler approximants used by the library are

$$
\Gamma_n(z)=\frac{n^z n!}{\prod_{k=0}^{n}(z+k)}.
$$

The numerator norms agree exactly between $z=x+it$ and $z=x$ because
$|n^{x+it}|=n^x$. Every denominator factor is nonzero: its real part is
$x+k>0$. Dividing the finite denominator comparison into the common
nonnegative numerator yields
$\Gamma_n(x)e^{-t^2}\leq|\Gamma_n(x+it)|$.

The library has already proved that these real and complex approximants
converge to their respective Gamma functions. Continuity of norm and
multiplication, followed by preservation of order under limits, proves
the displayed actual-Gamma inequality. Positivity of $\Gamma(x)$ then
justifies division and proves the ratio form.

## Main declarations

- `sum_shifted_inv_sq_le_two`
- `norm_vertical_factor_le`
- `prod_norm_vertical_factor_le`
- `norm_GammaSeq_vertical_eq`
- `GammaSeq_vertical_lower_bound`
- `gamma_vertical_lower_bound`
- `gamma_vertical_ratio_le_exp`

## Scope

This closes the vertical Gamma-factor estimate needed for the outer
complex-strip comparison. It does not itself establish a zeta-factor
bound, a complete reciprocal-Xi strip estimate, a contour shift, a
numerical enclosure, or positivity of the inverse Fourier density.

The proof uses the pinned mathlib modules
`Analysis.SpecialFunctions.Gamma.Beta` for the Euler approximants and their
limits, and `Analysis.PSeries` for the finite reciprocal-square bound.
It supplies an analytic ingredient for the normalized source
`theorem_pipeline/workspace/contexts/reciprocal_xi_global_logconcavity.md`.

No `sorry`, custom axiom, or `native_decide` is used.
