# Actual lattice aliases and infinite-trapezoid error

Companion: `DensityAliasBoundsFull.lean`, namespace `ReciprocalXi`.

## Statement

Let $G$ be the actual entire inverse Fourier density, and put

$$
A(z)=\frac{5e^{|\Re z|}}{2\pi}
\int_{\mathbb R}e^{|\Im z||u|}|\varphi(u)|\,du,
\qquad \varphi(u)=\frac{F(0)}{F(iu)}.
$$

The integral is finite by the previously proved actual weighted
integrability. For every complex $z$ and real $L>0$, the sequence
$G(z+Ln)$ is absolutely summable over all integers and

$$
\sum_{n\in\mathbb Z\setminus\{0\}}|G(z+Ln)|
\leq\frac{2A(z)}{e^L-1}.
$$

Consequently both the norm of the nonzero alias sum and
$\left|\sum_{n\in\mathbb Z}G(z+Ln)-G(z)\right|$ satisfy the same bound.

For the actual infinite trapezoid rule

$$
T_h(z)=\frac{h}{2\pi}\sum_{n\in\mathbb Z}
\varphi(hn)e^{-izhn},\qquad h>0,
$$

the proved Poisson identity gives the actual quadrature estimate

$$
|T_h(z)-G(z)|\leq\frac{2A(z)}{e^{2\pi/h}-1}.
$$

There are no additional assumptions on decay, convergence, real-valuedness,
or positivity of the density. The only geometric assumption is $L>0$
or, in the quadrature statement, $h>0$.

## Proof Sketch

The previously proved contour shift bounds the actual normalized density by

$$
|G(w)|\leq\frac{5e^{-|\Re w|}}{2\pi}
\int_{\mathbb R}e^{|\Im w||u|}|\varphi(u)|\,du.
$$

For $w=z+Ln$, the imaginary part is unchanged and the reverse triangle
inequality gives
$-|\Re z+Ln|\leq|\Re z|-L|n|$. Thus
$|G(z+Ln)|\leq A(z)e^{-L|n|}$.

Set $q=e^{-L}$, so $0<q<1$. The integer sequence $q^{|n|}$ is summable
by splitting it into its nonnegative and negative indices and applying
the ordinary geometric series theorem. Removing the zero index leaves
one copy of each positive power in each direction. Its exact sum is

$$
2\sum_{k=1}^{\infty}q^k=\frac{2q}{1-q}=\frac2{e^L-1}.
$$

The formal proof constructs this two-sided sum explicitly, rather than
assuming summability. Comparison with the derived pointwise density
bound proves absolute convergence and the sum-of-norms estimate. The
norm of the complex series is at most its sum of norms. Splitting the
absolutely convergent full series at $n=0$ then gives the lattice-minus-
central formulation.

Finally, `XiPoissonFull` already proves
$T_h(z)=\sum_{n\in\mathbb Z}G(z+(2\pi/h)n)$ with all Poisson hypotheses
discharged. Substitution of $L=2\pi/h>0$ yields the quadrature bound.

## Main declarations

- `densityAliasAmplitude`
- `complexDensity_norm_le_exp`
- `complexDensity_shift_norm_le`
- `summable_int_exp_abs`
- `hasSum_int_nonzero_exp_abs`
- `summable_norm_complexDensity_shifts`
- `summable_complexDensity_shifts`
- `tsum_norm_nonzero_complexDensity_shifts_le`
- `norm_tsum_nonzero_complexDensity_shifts_le`
- `complexDensity_lattice_error_le`
- `infiniteTrapezoid_error_le`

The nonzero integer sums in Lean are written as a sum over all integers
with the zero term replaced by zero.

## Scope

This proves the infinite-mesh discretization error for the actual Fourier
integral. It does not truncate the sampled sum to finitely many indices,
evaluate $A(z)$, or certify the individual sampled Xi values by rational
intervals. Those are separate finite numerical obligations. No density
positivity or curvature conclusion is assumed or claimed here.

Normalized source:
`theorem_pipeline/workspace/contexts/reciprocal_xi_global_logconcavity.md`.
The series argument uses pinned mathlib's two-sided integer-series
decomposition and geometric-series theorems.

No `sorry`, custom axiom, or `native_decide` is used.
