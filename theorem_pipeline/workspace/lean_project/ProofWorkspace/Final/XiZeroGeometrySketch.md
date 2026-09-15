# Actual Xi zero geometry and finite multiplicities

## Statement

Every zero $s$ of the actual Riemann Xi function satisfies $0<\operatorname{Re}s<1$. Every zero $z$ of the fixed normalization $F(z)=\xi(1/2+iz/2)/4$ satisfies $|\operatorname{Im}z|<1$ and $|\operatorname{Re}z|>1$. The zero set of $F$ is closed and discrete, is finite in each closed ball, and is countable. Every zero has finite positive analytic multiplicity.

## Assumptions

The pointwise zero-location and positive-multiplicity statements assume only $\xi(s)=0$ or $F(z)=0$ as displayed. The remaining statements are unconditional facts about the actual function. No RH, list of known zeros, zero-count estimate, product identity, or numerical certificate is assumed.

## Proof Sketch

On the closed half-plane $\operatorname{Re}s\ge1$, the library's zeta nonvanishing theorem, Gamma nonvanishing, and the exact completed-zeta formula show that Xi is nonzero. The removable value at $s=1$ is treated separately. The functional equation covers $\operatorname{Re}s\le0$. Transforming coordinates gives the strict imaginary-part bound for the zeros of $F$; the previously proved horizontal zero-free Xi strip gives the real-part lower bound. Since $F$ is entire and $F(0)\ne0$, the identity theorem and analytic-order theory show that its zeros are discrete and have finite order. Closedness and compactness then give finitely many zeros in each closed ball, and a countable exhaustion gives countability. Vanishing implies that each finite analytic order is positive.

## Remaining Scope

This does not isolate any of the first zeros, certify finite-height completeness or simplicity, bound the zero count, prove reciprocal-square summability, or establish a Hadamard product or the global density theorem.

## Lean Artifacts

- File: `XiZeroGeometryFull.lean`.
- Main theorems: `xi_zero_re_bounds`, `F_zero_im_bound`, `F_zero_abs_re_gt_one`, `F_zeros_closedBall_finite`, `F_zero_set_countable`, `F_analyticOrderAt_ne_top`, `F_zero_order_pos`.
