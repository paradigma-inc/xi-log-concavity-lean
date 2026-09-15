# Subquadratic circle-average growth of the zero-free factor

## Statement

For the actual zero-free quotient $Q=F/P$ with removable values filled, and its normalized entire logarithm $g$, the circle averages of $\log^+|Q|$ and of $\max(0,\operatorname{Re}g)$, divided by $R^2$, tend to zero as $R\to\infty$.

## Assumptions

The established actual Xi growth, actual paired zero product, and exact entire quotient/logarithm. No assumption that $g$ is constant is used.

## Proof Sketch

The first main theorem, together with $P(0)=1$ and the absence of poles of $P$, bounds the average of $\log^+|P^{-1}|$ by that of $\log^+|P|$. Removing the discrete singular values of the raw quotient does not change a positive-radius circle average. The product inequality therefore bounds the quotient average by the sum of the averages for $F$ and $P$. Actual factorial growth bounds the first by $(R+3)\log(R+3)$, and the already proved logarithmic majorant bounds the second by $B(R)=o(R^2)$. Both divided by $R^2$ tend to zero. Finally, $\log|Q|=\log|F(0)|+\operatorname{Re}g$ transfers this result to the positive real part of $g$. An entire-function rigidity argument is still needed to conclude that $g$ vanishes identically.

## Lean Artifacts

- File: `XiQuotientGrowthFull.lean`
- Main theorems: `F_pairQuotient_proximity_bound`, `F_pairQuotient_proximity_div_sq_tendsto`, `F_quotientLogPositiveAverage_div_sq_tendsto`.
