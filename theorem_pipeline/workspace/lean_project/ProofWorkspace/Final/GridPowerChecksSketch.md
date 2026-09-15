# Uniform initial range checks for the eta grid

## Statement

For every natural base $1\le a\le512$ and every natural logarithm
truncation order $L$, all four initial logarithmic range checks hold with
exponential scaling factor $16$:
`gridPowerChecks_512 a L` proves `GridPowerChecks a L 16`.
The exponents are $-1/2$ and $-1/80$, each with a lower and an upper
dyadic-logarithm endpoint. Thus the finite family of checks for any eta
sum of length $N\le512$ follows at once, independently of the retained-node
index.
The checks are monotone in a positive scaling factor: if they hold at
$m>0$, they also hold at every $n\ge m$. In particular, scale $16$
uniformly covers scale $256$.

## Assumptions

Only $a,L,N\in\mathbb N$, $1\le a\le512$, and, for the finite-family
corollary, $N\le512$ are required. In particular, $L=0$ is allowed.
There is no numerical sample, assumed special-function interval, or
enumeration of the integer bases.

## Proof Sketch

For a rational mantissa $1\le r\le2$, put $t=(r-1)/(r+1)$.
Then $0\le t\le1/3$. Every Taylor summand is nonnegative, and
$$
\frac{t^{2k+1}}{2k+1}\le(1/3)^{k+1}.
$$
The exact finite geometric-sum identity therefore gives
$0\le\operatorname{ratLogTaylor}(r,L)\le1$. Also,
$t^{2L+1}\le1/3$ and $1-t^2\ge8/9$ imply that the nonnegative
logarithm remainder is at most $1$. These bounds hold uniformly in $L$,
including the empty Taylor sum.

If $0\le d\le9$, substituting these bounds into the actual rational
definitions of the two dyadic logarithm endpoints places both in
$[-20,20]$. Multiplication by any rational $q$ with $|q|\le1/2$ places
both products in $[-10,10]$. Their sign-aware minimum and maximum remain
in that interval, so division by $16$ satisfies the required absolute
bound of $1$.

The accepted integer range reduction supplies
$a=2^{\lfloor\log_2a\rfloor}r$ with $1\le r<2$.
If $\operatorname{Nat.log2}(a)\ge10$, the proved inequality
$2^{\operatorname{Nat.log2}(a)}\le a$ would force
$1024\le a\le512$, a contradiction. Hence the preceding rational
argument applies to the two fixed exponents. For $j<N\le512$, the base
$j+1$ lies in the same range, which gives the finite-family corollary.

For the scale monotonicity theorem, $|x|\ge0$ and $0<m\le n$ imply
$|x|/n\le|x|/m$. Apply this inequality to each of the four fixed
logarithmic endpoints. Combining it with the scale-$16$ theorem proves
the entire finite family for any scaling factor at least $16$.

## Scope

This discharges only the four initial exponential range checks. It does
not assert endpoint precision, positivity of a final reciprocal interval,
or verification of retained-node values or curvature. The proof contains
no custom axioms or unchecked native computations.

## Lean Artifacts

- Proof: `ProofWorkspace/Final/GridPowerChecksFull.lean`.
- `ratLogArgument_mem_Icc_of_one_le`.
- `ratLogTaylor_bounds_unit_mantissa`.
- `ratLogError_bounds_unit_mantissa`.
- `ratLogDyadic_bounds_small`.
- `ratPowerDyadic_scaled_checks`.
- `gridPowerChecks_512`.
- `gridPowerChecks_range`.
- `gridPowerChecks_mono`.
- `gridPowerChecks_range_of_sixteen_le`.

Source context: `theorem_pipeline/workspace/contexts/reciprocal_xi_global_logconcavity.md`;
the concrete four-field contract is `GridPowerChecks` in the accepted
rounded eta-grid evaluator. All nine public proofs compile in the pinned Lean 4.28.0/mathlib environment;
the axiom audit contains only `propext`, `Classical.choice`, and `Quot.sound`.
