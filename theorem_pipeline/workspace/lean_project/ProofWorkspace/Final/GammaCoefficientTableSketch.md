# Reused integer-zeta coefficients for Gamma

Source: `workspace/contexts/reciprocal_xi_global_logconcavity.md`.
Run: `20260909T204310Z_e45f`.

Build the Euler weights once, and use the exactly equivalent integer-division
eta sums to form the intervals for $\zeta(k+2)$, $0\le k<N$. The entire list
is proved equal, entry for entry, to the accepted rational zeta endpoints.

For a Gamma offset $z$, map the signed coefficient
$(-1)^k(z^{k+2}-2z\,2^{-(k+2)})/(k+2)$ over this table, retaining min/max and
outward rounding. The resulting pair of sums is exactly the original pair.
Adding the same certified logarithmic constants and the same analytic tail
$8\,2^{-(N+2)}$ gives the identical log-Gamma endpoints. A table may therefore
be shared between offsets without changing any mathematical enclosure.

These are equality proofs for computation reuse; concrete high-precision
Gamma endpoints and source-node comparisons still require finite checking.

