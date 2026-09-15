# Fixed-grid coefficient rounding bound

## Statement and assumptions

The rational evaluator `ratSourceRoundedCoefficient c p v j` approximates the
actual coefficient of `realSampledTaylorPolynomial c p v`. Its assumptions are
rational inputs, $0\le c\le40$, $p\ge3$, $j\le64$, and
$|v_k|\le43046722$ for $0\le k\le13600$. No coefficient accuracy or numerical
table is assumed. With $B=10^{180}$, its error is at most
$$
13601\left(\frac1B+\frac{2^{66}}B+
 43046722\,2^{64}\frac{18\cdot13600}{B}\right)<10^{-140}.
$$
The requested $10^{-125}$ bound is a corollary; the sharper explicit budget
remains available for comparison with the unchanged source intervals.

## Proof Sketch

The source's exact degree-$j$ weight is advanced by the multiplier
$k/(8000(j+1))$, which lies between zero and two. Downward rounding to the
$1/B$ grid at initialization and at every step therefore gives weight error
at most $(2^{j+1}-1)/B$ by induction. The exact weight has magnitude at most
$43046722\,2^j$.

The degree-120 cosine and degree-121 sine polynomials at $q=c/40$ have actual
error at most $1/121!\le1/B$. Their grid-rounded seeds have error at most
$2/B$. Each coordinate of the rotation recurrence incurs at most $1/B$
additional rounding error. The previously proved norm-one rotation estimate
and strong induction establish that both approximate coordinates stay within
two in magnitude through index 13600; this is derived, not assumed from a
finite state certificate. Their error is then at most $18k/B$. The source's
parity and four-cycle signs preserve these estimates.

Each weight-times-trigonometric-factor product is rounded once more to the
grid, and these grid values are summed exactly as rationals. The identity
$\widetilde w\widetilde t-wt=(\widetilde w-w)\widetilde t+w(\widetilde t-t)$,
the termwise bounds, and the finite-sum triangle inequality give the displayed
budget. The exact source coefficient formula supplies the interpretation as
the actual polynomial coefficient, including the zero-frequency half-weight.
The final numerical comparisons are kernel-checked rational inequalities.

## Scope

This is a sound fixed-grid evaluator, not a bitwise-equivalence claim for the
original Python decimal-160 operations. The stored coefficient values,
curvature products, all 318 panel inequalities, and retained sample accuracy
still need their separate finite checks. No global log-concavity is concluded.

## Lean artifacts

- Proof: `SourceCoefficientErrorFull.lean`.
- Main exact-budget theorem: `ratSourceRoundedCoefficient_error_budget`.
- Numeric comparison: `sourceRoundedCoefficientBudget_lt`.
- Requested corollary: `ratSourceRoundedCoefficient_error`.
- Auxiliary theorems derive the weight, seed, recurrence, state, and product bounds.
