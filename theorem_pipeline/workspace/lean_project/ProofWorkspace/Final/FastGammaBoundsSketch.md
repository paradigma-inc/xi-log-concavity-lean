# Gamma and pi-power bounds with rounded logarithm inputs

## Statement

The module provides rational intervals for the actual quantities
$$
z\log\pi-2z\log2,\qquad \log\Gamma(1+z),\qquad
\Gamma(1+z),\qquad \Gamma((k+40)/160),\qquad \pi^q.
$$
Unlike the earlier rounded-coefficient variant, the logarithmic constants
are computed by rounded odd-power recurrences. The endpoints therefore do
not first form an exact, large-denominator Taylor sum at a Machin endpoint
of $\pi$. The earlier public evaluators are unchanged.

## Assumptions

The logarithmic Gamma theorem assumes only $z\in\mathbb Q$,
$|z|\le1/2$, natural truncation orders, and a positive integer rounding
scale $B$. The exponential variants additionally require positive
scaling factor $m$, positive exponential order $n$, and explicit rational
checks $|\ell/m|\le1$ and $|u/m|\le1$ for their logarithmic endpoints.
The Gamma-grid index is any natural number; its central-range reduction
and positive recurrence multiplier are proved. The pi-power exponent is
any rational number. No actual special-function enclosure is assumed.

## Proof Sketch

The accepted rounded logarithm theorem encloses $\log\pi$ using the
certified Machin interval. It also encloses $\log2$ by choosing the exact
odd-series argument $1/3$ as the uniform remainder parameter. For either
sign of a rational coefficient, the minimum and maximum of its products
with the two logarithmic endpoints enclose the corresponding true
product. Rounding those products outward again preserves the interval.
Adding the resulting intervals gives the constant
$z\log\pi-2z\log2$.

For $|z|\le1/2$, the already proved actual Gamma identity has the finite
approximation
$$
\log\Gamma(1+z)=z\log\pi-2z\log2+
\sum_{j<N}c_j(z)\operatorname{Re}\zeta(j+2)+\varepsilon_N,
\qquad |\varepsilon_N|\le8\,2^{-(N+2)}.
$$
Each signed coefficient term is enclosed by the accepted rounded
integer-zeta evaluator, which includes its analytic eta remainder. Sum
those term intervals, add the newly rounded constant, include the
displayed Gamma remainder in both directions, and round the result
outward. This proves the actual log-Gamma interval with no assumed series
identity or accuracy.

Monotonicity of the actual exponential and the fully rounded exponential
theorem then give the central Gamma bounds. Since $1+z\ge1/2$, Gamma is
positive, so exponentiation of its logarithm gives Gamma itself. The exact
Gamma recurrence multiplies this value by a proved positive rational
factor at each grid index; outward rounding of that multiplication gives
the full Gamma-grid interval. The same sign-aware logarithmic product and
exponential argument prove the pi-power interval via
$\pi^q=\exp(q\log\pi)$.

## Scope

The change removes exact logarithm-sum denominator growth from these
Gamma and pi-power evaluators. Rational coefficients and finite integer
powers remain exact before their existing per-term rounding. No runtime
bound, retained-node evaluation, final interval width, or curvature
certificate is asserted by these theorems. No custom axioms or unchecked
native computations are used.

## Lean Artifacts

- Proof: `ProofWorkspace/Final/FastGammaBoundsFull.lean`.
- `ratPiPowerLogFast_enclosure`.
- `ratGammaConstantFast_enclosure`.
- `ratLogGammaFast_enclosure`.
- `ratGammaFast_enclosure`.
- `ratGammaGridFast_enclosure`.
- `ratPiPowerFast_enclosure`.

Source: `theorem_pipeline/workspace/contexts/reciprocal_xi_global_logconcavity.md`,
with the previously proved actual centered Gamma series and rounded
logarithm modules. All six public proofs compile in the pinned Lean 4.28.0/mathlib project,
and their axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`.
