# Rounded integer-zeta and log-Gamma sums

## Statement

The module gives exact outward-rounded rational enclosures for the actual
values $\operatorname{Re}\zeta(k)$ at every integer $k\ge2$ and for
$\log\Gamma(1+z)$ at rational $z$ with $|z|\le1/2$. Each finite eta or
Gamma-series term is rounded to a fixed positive integer scale before
being added. The final zeta and log-Gamma endpoints are also rounded onto
that grid.

## Assumptions

The scale $B$ is a positive natural number. Integer-zeta evaluation assumes
$k\ge2$; the eta truncation order $M$ is any natural number. Log-Gamma
evaluation assumes rational $|z|\le1/2$; its Gamma-series order $N$, eta
order $M$, and logarithm order $L$ are arbitrary natural numbers. No actual
zeta values, real-valued enclosures, series identities, or numerical
accuracy bounds are assumed.

## Proof Sketch

For integer $k$, the exact rational eta summands are
$$
e_j=(-1)^j w_{M,j}(j+1)^{-k},\qquad
w_{M,j}=2^{-M}\sum_{j<n\le M}\binom Mn.
$$
Round each $e_j$ downward and upward before summing. The outward-rounding
theorem proves that these two sums enclose the same exact finite eta sum
used by the accepted actual integer-zeta theorem. Its multiplier
$2^k/(2^k-2)$ is positive for $k\ge2$. Multiplying preserves the finite-sum
inequalities. The accepted analytic zeta remainder is at most $2/2^M$,
obtained from eta's $2^{-M}$ remainder and a multiplier at most $2$.
Add this remainder only to the upper endpoint, then round the two zeta
endpoints outward. The computation never needs to form the unrounded
finite eta sum: it appears only in the symbolic proof connecting the
rounded computation to the actual zeta function.

For log Gamma, use the already proved actual approximation
$$
\log\Gamma(1+z)
=z\log\pi-2z\log2+
\sum_{k<N}c_k(z)\operatorname{Re}\zeta(k+2)+E_N(z),
\qquad |E_N(z)|\le8(1/2)^{N+2},
$$
where
$$
c_k(z)=\frac{(-1)^k}{k+2}
\left(z^{k+2}-2z(1/2)^{k+2}\right).
$$
For each signed coefficient, take the minimum and maximum of its products
with the rounded zeta endpoints. This preserves the interval whether the
coefficient is positive, negative, or zero. Round each resulting term
outward before summation, keeping the finite sum on the fixed grid.

The actual $z\log\pi$ interval comes from the certified Machin-pi and
logarithm bounds. The actual $-2z\log2$ interval is obtained by the same
sign-aware multiplication of the verified log-two endpoints. These two
constant contributions are also rounded before addition. Summing their
bounds with the coefficient bounds encloses the actual finite Gamma
approximation. Add the proved analytic remainder with opposite signs to
the lower and upper endpoints, then perform one final outward round.
This proves the actual log-Gamma enclosure while ensuring that its returned
endpoints, not merely its intermediate sums, lie on the fixed grid.

## Scope

Rounding error is carried by the explicit rational lower and upper
endpoints; it is not treated as zero or replaced by an assumed error
estimate. The integer powers within individual eta terms, the exact
Gamma coefficients, and the existing logarithm calculations remain exact
rational computations. The improvement prevents denominator growth across
the large finite sums. It does not assert that every retained Xi node or
the full curvature certificate has been numerically checked. No custom
axiom or unchecked native computation is used.

## Lean Artifacts

- `RoundedGammaLogBoundsFull.lean`
- Integer eta sum definitions: `ratEtaIntegerTerm`,
  `ratEtaIntegerRoundedLower`, `ratEtaIntegerRoundedUpper`.
- Zeta endpoints: `ratZetaNatRoundedLower`, `ratZetaNatRoundedUpper`.
- Gamma coefficient endpoints: `ratGammaCoefficientRoundedLower`,
  `ratGammaCoefficientRoundedUpper`.
- Gamma constant endpoints: `ratGammaConstantRoundedLower`,
  `ratGammaConstantRoundedUpper`.
- Log-Gamma endpoints: `ratLogGammaRoundedLower`, `ratLogGammaRoundedUpper`.
- Public theorems: `ratEtaIntegerRounded_enclosure`,
  `ratZetaNatRounded_enclosure`, `ratGammaCoefficientRounded_enclosure`,
  `ratGammaConstantRounded_enclosure`, `ratLogGammaRounded_enclosure`.

All five public theorems compiled in the pinned Lean 4.28.0/mathlib project,
with axiom checks containing only `propext`, `Classical.choice`, and
`Quot.sound`.
