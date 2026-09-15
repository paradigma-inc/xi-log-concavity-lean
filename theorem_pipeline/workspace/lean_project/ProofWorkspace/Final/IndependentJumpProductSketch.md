# Characteristic exponents of independent jump sums

## Statement and assumptions

For independent real coordinates with laws $\nu_n$, the characteristic function of the first $N$ coordinates' sum is $\prod_{n<N}\widehat\nu_n(u)$. For compound-Poisson coordinate laws with rates $r_n$, this equals $\exp\sum_{n<N}r_n(\widehat\nu_n(u)-1)$. If the absolute first moments are summable and the coordinate characteristic exponents $g_n$ are summable at a fixed frequency, the characteristic function of the infinite sum is $\exp\sum_n g_n$.

## Proof Sketch

The actual coordinate maps on the infinite product measure are independent. The exponential of a finite sum is the product of its exponentials, and independence factors their expectation. The explicit compound-Poisson characteristic function then gives the finite exponent formula. For the infinite sum, dominated convergence from `IndependentJumpSumFull` identifies one limit, while summability of the exponents and continuity of the exponential identify the other. Uniqueness of limits equates them.

The summability assumptions are explicit. No Xi-specific jump partition or positive residual-law conclusion is asserted here.

## Lean Artifacts

File: `IndependentJumpProductFull.lean`. Theorems: `charFun_finiteJumpSum`, `charFun_finiteCompoundPoissonSum`, `charFun_independentJumpSum_eq_exp`.
