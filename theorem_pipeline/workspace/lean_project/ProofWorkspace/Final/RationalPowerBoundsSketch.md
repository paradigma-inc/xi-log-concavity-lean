# Rational real-power enclosures

## Statement

The rational endpoints `ratPowerLower` and `ratPowerUpper` bound the actual
real power $a^r$ for every positive rational base $a$ and every rational
exponent $r$, including negative exponents. The computation uses only finite
rational arithmetic, the proved logarithm enclosure, and the proved
range-reduced exponential enclosure.

## Assumptions

The base satisfies $a>0$. The logarithm order $N$ is any natural number.
The exponential range-reduction factor $m$ and exponential order $n$ are
positive natural numbers. The two computed logarithmic-product endpoints
$u_-$ and $u_+$ satisfy $|u_-/m|\le 1$ and $|u_+/m|\le 1$.
These conditions concern exact rational expressions and do not assume the
accuracy of an external numerical result.

## Proof Sketch

Let $L_-$ and $L_+$ be the previously proved rational lower and upper bounds
for $\log a$. Set
$$
u_- = \min(rL_-,rL_+),\qquad
u_+ = \max(rL_-,rL_+).
$$
If $r\ge 0$, multiplication preserves the logarithm inequalities. If
$r\le 0$, it reverses them. In either case,
$u_-\le r\log a\le u_+$; the use of minimum and maximum handles both signs
without imposing a restriction on the exponent.

Apply the actual range-reduced exponential enclosure separately at $u_-$
and $u_+$. Its lower endpoint is the $m$th power of the nonnegative-clamped
Taylor lower endpoint at $u_-/m$, while its upper endpoint is the $m$th
power of the Taylor upper endpoint at $u_+/m$. The proved Taylor remainders
and the identity $\exp(u/m)^m=\exp(u)$ justify these rational endpoints.
Monotonicity of the real exponential then sandwiches $\exp(r\log a)$
between them. Since $a>0$, the definition of the actual real power gives
$a^r=\exp((\log a)r)$, completing the enclosure.

The concrete witness uses $a=3/2$, $r=-1/3$, logarithm order $4$, range
factor $1$, and exponential order $6$. Lean checks the resulting rational
arithmetic and proves
$$
\frac{87}{100} < (3/2)^{-1/3} < \frac{88}{100}.
$$
This witness explicitly exercises a negative noninteger exponent, rather
than reducing the real-power assertion to an integer-power calculation.

## Scope

This is a sound evaluator primitive for actual real powers, not a proof that
any retained Fourier grid node or source certificate entry has already
been enclosed. No floating-point result, desired power bound, custom axiom,
or unchecked native computation is used. The full reciprocal-Xi curvature
target remains separate.

## Lean Artifacts

- `RationalPowerBoundsFull.lean`
- Definitions: `ratPowerLogLower`, `ratPowerLogUpper`, `ratPowerLower`,
  `ratPowerUpper`.
- Theorems: `ratPower_log_enclosure`, `ratPower_enclosure`,
  `negative_third_power_certified`.

The proof uses the pinned Lean 4.28.0/mathlib project and imports the actual
logarithm and exponential evaluator modules. Before promotion, all three
theorems compiled and their kernel axiom checks contained only
`propext`, `Classical.choice`, and `Quot.sound`.
