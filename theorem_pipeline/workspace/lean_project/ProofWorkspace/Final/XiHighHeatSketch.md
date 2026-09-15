# Lower bound for the actual high-zero heat trace

## Statement

For $T\ge100$, $c\ge0$, $2c\le T$ and $t>0$, the real part of the actual trace over zero occurrences with $\operatorname{Re}a\ge T$ is at least $-(7/100)e^{-c^2t}$.

## Assumptions

Only these parameter bounds. No reality or simplicity assumption is made about the high zeros or any low zero.

## Proof Sketch

If a heat term has nonnegative real part, its individual lower bound is immediate. Otherwise its cosine angle has absolute value exceeding $\pi/2$. The actual strip bound $|\operatorname{Im}a|\le1$ then gives $t\operatorname{Re}a\ge3/4$. The parameter bounds imply $\operatorname{Re}(a^2)-c^2\ge(2/3)(\operatorname{Re}a)^2$. Combining these yields the individual lower bound $-e^{-c^2t}e^{-\operatorname{Re}a/2}$. Absolute convergence justifies summing real parts. The actual exponential high-zero budget bounds the sum by $7/100$.

This is the infinite high-zero contribution only. A positive remaining low-zero contribution and the finite low-zero reality certificate are still required for residual positivity.

## Lean Artifacts

- `XiHighHeatFull.lean`
- `high_zero_heat_lower`, `F_highHeatTrace_lower`.
