# Rounded powers and scaled exponentials

## Statement

Starting from $L_0=U_0=1$, the recurrences
$$
L_{n+1}=\operatorname{roundDown}_B(L_n a),\qquad
U_{n+1}=\operatorname{roundUp}_B(U_n b)
$$
enclose the actual real power $x^n$ whenever $0\le a\le x\le b$.
Every stored iterate lies on the fixed $B$-grid. Applied to the verified
Taylor interval for $\exp(q/m)$, this gives fixed-grid rational endpoints
enclosing the actual value $\exp(q)$.

## Assumptions

For powers, $a,b$ are rational, $x$ is real, $0\le a\le x\le b$, and $B$
is a positive natural grid scale. The power exponent is any natural number.
For the exponential, $q$ is rational; the scaling factor $m$, Taylor order
$n$, and grid scale $B$ are positive natural numbers, and $|q/m|\le1$.
No rounded-value accuracy or transcendental approximation is assumed.

## Proof Sketch

Induct on the natural power exponent. The initial values equal $x^0$.
Assume the lower and upper iterates enclose $x^n$ and are nonnegative.
Multiplying by the nonnegative bounds $a\le x\le b$ gives
$L_n a\le x^{n+1}\le U_n b$. The proved outward-rounding theorem preserves
these inequalities when each product is returned to the $B$-grid. Floor
and ceiling preserve nonnegativity here, completing the induction.
Grid membership follows directly from the integer floor/ceiling witnesses
at every step; the initial value $1$ is also a grid point.

For the exponential, use the previously proved rational Taylor/error
enclosure at $q/m$. Clamp its lower endpoint to zero, which remains below
the positive exponential. Round both initial Taylor endpoints outward
onto the $B$-grid before starting the power recurrence. The initial bases
and all stored products are therefore on the same grid. The power theorem
encloses $\exp(q/m)^m$, and the exact identity
$\exp(q/m)^m=\exp(q)$ identifies the enclosed value with the actual
exponential.

## Scope

Rounding is performed after every powering multiplication and on the
initial Taylor endpoints. The Taylor sum itself still uses the existing
exact rational evaluator; this module does not claim a rounded Taylor-sum
algorithm or that a full retained Xi sample table has been evaluated.
The theorem proves enclosure soundness, not a uniform error width for an
arbitrary choice of grid scale. The final endpoints can be inspected by
exact rational arithmetic to establish any desired concrete width.
No custom axiom or unchecked native computation is used.

## Lean Artifacts

- `RoundedExpBoundsFull.lean`
- Definitions: `ratPowRoundLower`, `ratPowRoundUpper`,
  `ratExpRoundedLower`, `ratExpRoundedUpper`.
- Theorems: `ratPowRoundLower_nonneg`, `ratPowRoundUpper_nonneg`,
  `ratPowRound_enclosure`, `ratPowRound_mem_grid`,
  `ratExpRounded_enclosure`.

The proof uses the pinned Lean 4.28.0/mathlib project and the verified
rational rounding and exponential modules. All five theorem axiom checks
contained only `propext`, `Classical.choice`, and `Quot.sound`.
