# A rational checker for the original compact-panel bounds

## Statement

`sourcePanelCheck i a` is a finite rational test of a 65-integer coefficient
vector against panel `i`'s original recorded constant, nonconstant, and
curvature-error bounds. With `a` equal to the proved integer source stream and
the retained sample errors bounded by the unchanged $2\cdot10^{-120}$,
success implies strictly positive actual density curvature on that panel.
Success for all 318 panels constructs `DensityCompactEnclosures` without
assuming any of its coefficient or derivative enclosures.

The sample-accuracy premise remains explicit. This module neither proves the
full retained-node table accurate nor executes any panel test.

## Proof Sketch

Write $A$ for the rational streamed polynomial, embedded in the reals, and
$P$ for the actual degree-64 source Taylor polynomial. Their individual
coefficient errors are at most the already proved rational budget
$$
\delta=13601\left(B^{-1}+2\frac{2^{65}}B+
 (43046722\,2^{64})\frac{18\cdot13600}B\right),\qquad B=10^{180}.
$$
This is the same explicit budget previously proved smaller than $10^{-140}$.
For the coefficient $\ell^1$ norm, triangle and product inequalities give
$$
\|P-A\|_1\le d_0=65\delta,\quad
\|P'-A'\|_1\le d_1=65\cdot64\delta,\quad
\|P''-A''\|_1\le d_2=65\cdot64\cdot63\delta.
$$
The derivative bounds use the actual polynomial derivative, including its
falling-factorial coefficients and vanishing low-degree terms.

For $C(P)=(P')^2-PP''$, the exact difference identity and the same norm
inequalities imply
$$
\|C(P)-C(A)\|_1\le D=
d_1(2\|A'\|_1+d_1)+d_0(\|A''\|_1+d_2)+\|A\|_1d_2.
$$
Consequently the actual constant coefficient is at least $C(A)_0-D$, and
the norm of its nonconstant coefficients is at most
$\|C(A)-C(A)_0\|_1+D$.

The source analytic jet error $e=\mathrm{sourcePanelJetError}$ is not enlarged
by coefficient rounding. A rational upper bound $\bar e\ge e$ is obtained
from the sound fully rounded exponential evaluator at 66, retaining the
source expression
$8\cdot10^{-85}+e^{66}(1/50)^{65}66^2/(1-1/50)^3$.
Monotonicity gives the rational curvature-error upper bound
$$
\bar e\,[2(\|A'\|_1+d_1)+(\|A\|_1+d_0)+(\|A''\|_1+d_2)]
 +2\bar e^2.
$$
The checker compares these three rational expressions directly with the
original recorded bounds. It does not assume that those records describe
the polynomial correctly. The previously kernel-checked strict margin of
the records then applies to the actual source polynomial. The actual
density derivative enclosures follow from the retained sample errors and
the proved Fourier/Taylor analysis; rescaling the first and second jets by
$1/200$ and $(1/200)^2$ yields the physical density-curvature conclusion.

## Executable inputs and remaining obligations

The checker accepts a list of 65 integers and a panel index. Polynomial
construction, differentiation, multiplication, absolute values, and all
comparisons are over exact rationals. Source centers and the three recorded
quantities have rational definitions with proved real-cast agreement.

An actual execution must first prove that its vector equals
`intSourceCoefficientStream (ratSourcePanelCenter i) sourcePiMidpoint v`,
then prove that the Boolean test returns true. No such execution is asserted
here. The sample vector may be supplied separately; no stored midpoint array
or unproved sample-accuracy certificate is imported.

## Lean artifacts

- Proof: `SourcePanelCheckerFull.lean`.
- Rational predicate and Boolean: `SourcePanelChecks`, `sourcePanelCheck`.
- Polynomial bounds from success: `sourcePanelCheck_enclosures`.
- Whole-panel actual curvature: `sourcePanelCheck_density_curvature_pos`.
- All-panel construction: `densityCompactEnclosures_of_stream_checks`.
