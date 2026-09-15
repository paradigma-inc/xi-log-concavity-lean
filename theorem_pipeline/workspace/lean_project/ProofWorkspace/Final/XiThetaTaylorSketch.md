# Certified finite theta Taylor remainder

## Statement

For $c\ge1$, the actual finite theta integrand at $x=48,N=4$ has Taylor coefficients bounded by $10^{14}/(c/2)^n$. At $|z-c|\le c/16$, the remainder after forty retained terms is at most $10^{-22}$.

## Assumptions

Only the stated center and distance restrictions. The coefficients are derivatives of the actual finite theta integrand, not a supplied numerical sequence.

## Proof Sketch

The disk of radius $c/2$ lies in the right half-plane and has real part at least $1/2$. Apply the already proved complex norm bound and Cauchy's derivative estimate. The Taylor series converges inside this disk. At the stated evaluation points the ratio of distances is at most $1/8$, so the tail is bounded by a geometric series. Exact rational arithmetic gives $10^{14}(1/8)^{40}/(1-1/8)\le10^{-22}$.

## Lean Artifacts

- Full proof: `XiThetaTaylorFull.lean`
- Main theorem: `theta48Taylor40_remainder_le`.
- Supporting theorems: `theta_disk_re_lower`, `theta48_diffContOnCl_disk`, `theta48TaylorCoefficient_norm_le`, `hasSum_theta48Taylor`, `theta48Taylor_term_le`, `theta48Taylor_remainder_le`.
