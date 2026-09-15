# Actual Xi logarithmic derivative

## Statement

At every point with $F(w)\ne0$, the actual logarithmic derivative equals the absolutely convergent sum $\sum_a2w/(w^2-a^2)$ over actual positive-half-plane zero occurrences, including multiplicities.

## Assumptions

Only nonvanishing at the evaluation point. There is no RH, zero-list or product-convergence assumption.

## Proof Sketch

Differentiate each quadratic factor explicitly. Actual inverse-square summability implies that all but finitely many factors are within one half of 1. Their logarithmic derivatives are bounded by $4|w|/|a|^2$, proving absolute summability; the finite exceptions cause no convergence issue. Apply the locally uniform infinite-product logarithmic derivative theorem to the already proved canonical product. The actual identity $F=F(0)P$ and $F(0)\ne0$ remove the constant normalization.

Convergence of this identity does not prove positivity of a heat trace or residual law.

## Lean Artifacts

- `XiLogDerivativeFull.lean`
- Main theorem: `F_logDeriv_eq_paired_sum`.
