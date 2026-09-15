# Minimal quadratic growth of the actual paired product

## Statement

For the actual positive-half-plane zero occurrences $a$, with multiplicity, define
$$B(R)=\sum_a\log(1+R^2/|a|^2).$$
The series converges, is nonnegative, and bounds the paired product by $|P(z)|\le e^{B(R)}$ whenever $|z|\le R$. Moreover $B(R)/R^2\to0$ as $R\to\infty$.

## Assumptions

Only the actual zero product and its previously proved inverse-square summability. No product identity for $F$ and no growth hypothesis about its zero-free quotient is assumed.

## Proof Sketch

Every summand lies between zero and $R^2/|a|^2$. This proves summability and bounds finite products; passage to the established product limit gives the global upper bound. After division by $R^2$, each summand tends to zero and is dominated by $1/|a|^2$. Dominated convergence for series therefore proves the minimal quadratic growth assertion. This supplies a growth input for removing the exponential factor, but does not itself remove it.

## Lean Artifacts

- File: `XiProductGrowthFull.lean`
- Main theorems: `norm_F_pairedProduct_le_exp`, `F_pairLogMajorant_div_sq_tendsto`.
