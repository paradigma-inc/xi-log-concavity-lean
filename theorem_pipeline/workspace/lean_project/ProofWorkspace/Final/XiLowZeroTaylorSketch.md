# Fine low-zero theta error budget

## Statement

For every real $|x|\le60$, truncating the actual theta integral at $T=32$
with five Gaussian terms changes $F(x)$ by at most $2\cdot10^{-39}$.
On each dyadic panel, the eighty-term Taylor polynomial for the actual
finite integrand has pointwise error at most $10^{-56}$.

## Assumptions

Only the explicit real-coordinate bound, positive panel centers and
panel-radius conditions are required. There are no numerical integral
values or zero-location hypotheses.

## Proof Sketch

The actual theta tail formula bounds the two omitted tails using
$\pi>3$ and a rational lower bound for $e^{96}$. The finite complex
integrand is bounded by $10^{16}$ in the right half-plane
$\Re t\ge1/2$. Cauchy's derivative estimates in the disk of radius $c/2$
give a geometric majorant with ratio at most $1/8$ on the panel.
Summing its tail after eighty terms gives the stated error. This bounds
an exact, unevaluated polynomial; it does not certify the root endpoints.

## Lean Artifacts

- File: `XiLowZeroTaylorFull.lean`
- Main theorems: `F_lowZero_finite_theta_truncation_error`,
  `lowZeroThetaTaylor80_remainder_le`.

