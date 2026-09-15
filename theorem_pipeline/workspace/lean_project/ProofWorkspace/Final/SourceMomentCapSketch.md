# Source moment-cap arithmetic

## Statement and assumptions

The actual $F$ is real on the real axis, and the previously certified central-Xi interval implies $0\le F(0)\le0.124280194548$. If $a\ge28.26945028346$, $b\ge42.04407927754$, both below $48$, and $F(48)\ge529169286414/10^{18}$, then the source finite-factor quotient is at most $268341$.

## Proof Sketch

Conjugation symmetry makes the real-axis values real. The central value bound is checked against the existing exact rational Xi endpoints. Both factors $48^2/a^2-1$ and $48^2/b^2-1$ are nonnegative and decrease as the positive roots increase. Their rational upper endpoints, the certified central upper endpoint, and the positive lower endpoint for $F(48)$ give the claimed cap by exact arithmetic.

This module does not certify the root lower bounds or the actual $F(48)$ lower bound. It only discharges the moment-cap arithmetic once those source inputs are proved.

## Lean artifacts

- `SourceMomentCapFull.lean`
- `F_real_eq_ofReal_re`
- `F_zero_re_source_upper`
- `source_moment_cap_of_F48_lower`
