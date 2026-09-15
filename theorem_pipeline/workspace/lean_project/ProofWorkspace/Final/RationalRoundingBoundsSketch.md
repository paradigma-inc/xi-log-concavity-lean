# Sound outward rational rounding

## Statement

For a rational $q$ and a positive natural scale $B$, define
$$
q^-_B=\frac{\lfloor Bq\rfloor}{B},\qquad
q^+_B=\frac{\lceil Bq\rceil}{B}.
$$
The endpoints enclose the actual real value of $q$, lie on the $B$-grid,
and satisfy
$$
0\le q^+_B-q^-_B\le\frac1B.
$$
Existing grid points are unchanged. Rounding the lower and upper endpoints
of an existing real interval outward preserves that interval's soundness.

## Assumptions

The grid scale $B$ is a positive natural number. The rational input may
have either sign. For interval preservation, the original rational
endpoints must already enclose the specified real value. The nonnegativity
lemmas require a nonnegative input and also hold at scale zero, where
the total rational division operation returns zero.

## Proof Sketch

The defining inequalities for floor and ceiling give
$\lfloor Bq\rfloor\le Bq\le\lceil Bq\rceil$. Division by the positive
scale proves the rational enclosure, and the order-preserving embedding
into the real numbers proves its actual-real version. Transitivity then
shows that replacing any existing interval's endpoints by their outward
rounded values cannot lose an enclosed real value.

The floor and ceiling of a single number differ by at most one integer.
After division by $B$, this gives the width bound $1/B$; nonnegativity of
the width follows from the enclosure. Multiplying the rounded endpoints
by $B$ cancels the denominator and produces the exact floor and ceiling
integers, proving grid membership. If the input already equals $k/B$,
then both integer operations act on the integer $k$ and return it, proving
exact preservation, including for negative grid points. Floor and ceiling
of a nonnegative number are nonnegative, so rounding preserves
nonnegativity where needed for subsequent interval products.

## Scope

This is a checked arithmetic primitive, not a new numerical receipt or
verification system. It permits fixed-denominator intermediate interval
arithmetic without making any assumption about the actual transcendental
values later enclosed. No custom axiom or unchecked native computation is
used.

## Lean Artifacts

- `RationalRoundingBoundsFull.lean`
- Definitions: `ratRoundLower`, `ratRoundUpper`.
- Theorems: `ratRound_enclosure`, `ratRound_real_enclosure`,
  `ratRound_interval_enclosure`, `ratRoundLower_nonneg`,
  `ratRoundUpper_nonneg`, `ratRound_width_le`, `ratRound_width_nonneg`,
  `ratRound_mem_grid`, `ratRound_grid_exact`.

The proof uses the pinned Lean 4.28.0/mathlib project. All nine theorem
axiom checks contained only `propext`, `Classical.choice`, and `Quot.sound`.
