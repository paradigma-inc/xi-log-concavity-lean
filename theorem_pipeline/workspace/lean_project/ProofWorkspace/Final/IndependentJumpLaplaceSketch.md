# Laplace transform of an independent nonnegative sum

## Statement and assumptions

The Laplace transform of a finite independent sum is the product of its coordinate Laplace transforms. Suppose the coordinate laws are nonnegative probability measures with summable absolute first moments. Then their finite-sum Laplace transforms converge to that of the actual infinite-sum law for every $x\ge0$. If the coordinate Laplace transforms equal $e^{g_n}$ and $\sum_n g_n$ converges absolutely, the limiting transform equals $e^{\sum_n g_n}$.

## Proof Sketch

Independence on the product probability space factors the exponential of each finite sum. Almost-everywhere nonnegative support bounds every finite-sum Laplace integrand by one; almost-everywhere convergence of the sums therefore permits dominated convergence. Continuity of the exponential identifies the limit of the finite exponent sums, and uniqueness of limits gives the formula.

All summability and support hypotheses are explicit. The module does not assume or claim a Xi-specific residual law.

## Lean Artifacts

File: `IndependentJumpLaplaceFull.lean`. Theorems: `nonnegativeLaplace_finiteJumpSum`, `tendsto_nonnegativeLaplace_finiteJumpSum`, `nonnegativeLaplace_independentJumpSum_eq_exp`.
