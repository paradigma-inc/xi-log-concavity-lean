# Rounded actual special-function enclosures

## Statement

The module connects the proved rounded exponential evaluator to actual
Gamma values, powers of $\pi$, and dyadic or positive-integer-base real
powers. It gives exact rational lower and upper endpoints for
$$
\Gamma(1+z),\qquad
\Gamma((k+40)/160),\qquad
\pi^r,\qquad (2^d a)^q,\qquad n^q.
$$
The Gamma-grid endpoints also round the final recurrence multiplication
outward onto the fixed grid.

## Assumptions

The central Gamma parameter $z$ is rational and satisfies $|z|\le1/2$.
The Gamma-grid index $k$ is any natural number; its reduction to this
central range is proved rather than assumed. Power exponents are rational,
the dyadic mantissa is positive, and integer bases are positive.

Each evaluator checks that the absolute value of each rational logarithmic
endpoint divided by the exponential scaling factor is at most $1$.
For Gamma, these are the outward-rounded log-Gamma endpoints, with rounding
scale $B$. The pi-power, dyadic-power, and integer-power logarithmic checks
are unchanged from their existing interfaces.
The exponential order, scaling factor, and rounding scale $B$ are positive
natural numbers. Logarithm and auxiliary truncation orders have their
existing unrestricted natural-number domains. No new real-valued interval
or special-function approximation is an input assumption.

## Proof Sketch

For the central Gamma interval, the previously proved outward-rounded
integer-zeta sums, sign-aware Gamma coefficient sums, and logarithmic
constants enclose $\log\Gamma(1+z)$. Their analytic truncation error is
included in those endpoints. Apply the fully rounded actual exponential
theorem to each endpoint. Its Taylor-term recurrence and subsequent integer
powers round intermediate products outward, and its remainder bound is
proved for the actual exponential. Monotonicity encloses the exponential
of the true logarithm. The central argument lies in $[1/2,3/2]$, so actual
Gamma is positive there and exponentiating its logarithm returns Gamma.

For the full Gamma grid, the established exact recurrence expresses
$\Gamma((k+40)/160)$ as a positive rational multiplier times the central
Gamma value. Multiplication by that positive factor preserves both
inequalities. The actual-real outward-rounding theorem then rounds the
two product endpoints onto the $B$-grid without losing the enclosed value.

For $\pi^r$, the proved sign-aware rational interval encloses $r\log\pi$.
Rounded exponential endpoints and the identity
$\pi^r=\exp(r\log\pi)$ give the result for either sign of $r$. The dyadic
power proof uses the already established interval for $q\log(2^d a)$ in
exactly the same way. Finally, positive integer bases are reduced by the
proved exact decomposition using $\operatorname{Nat.log2}$ and the
computed mantissa in $[1,2)$; substituting this identity yields the actual
integer-base real power theorem.

## Scope

All logarithmic enclosures and recurrence identities retain their proved
analytic meanings. Gamma uses the rounded log-Gamma evaluator; every
exponential uses rounded Taylor terms as well as rounded powers, and the
Gamma recurrence product is also rounded outward. Accepted earlier APIs
are not modified. No high-precision retained node, full finite table, or
curvature certificate is claimed to have been checked. The remaining
logarithm computations and rational coefficient formulas are exact; this
module does not assert a runtime bound. No new custom axioms or unchecked
native computations are used.

## Lean Artifacts

- `RoundedSpecialFunctionBoundsFull.lean`
- Central Gamma endpoints: `ratGammaRoundedLower`, `ratGammaRoundedUpper`.
- Gamma-grid endpoints: `ratGammaGridRoundedLower`, `ratGammaGridRoundedUpper`.
- Pi-power endpoints: `ratPiPowerRoundedLower`, `ratPiPowerRoundedUpper`.
- Dyadic-power endpoints: `ratPowerDyadicRoundedLower`, `ratPowerDyadicRoundedUpper`.
- Integer-power endpoints: `ratPowerNatRoundedLower`, `ratPowerNatRoundedUpper`.
- Theorems: `ratGammaRounded_enclosure`, `ratGammaGridRounded_enclosure`,
  `ratPiPowerRounded_enclosure`, `ratPowerDyadicRounded_enclosure`,
  `ratPowerNatRounded_enclosure`.

All five theorems compiled in the pinned Lean 4.28.0/mathlib project and
their axiom checks contained only `propext`, `Classical.choice`, and
`Quot.sound`.
