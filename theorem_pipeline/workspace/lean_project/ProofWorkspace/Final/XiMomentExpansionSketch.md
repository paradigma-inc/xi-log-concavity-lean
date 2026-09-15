# Actual finite reciprocal-zero moment expansion

## Statement

For the actual paired zero occurrences of $F(z)=\xi(1/2+iz/2)/4$, put
$M_m=\sum_a\Re(a^{-2m})$, $G(u)=-\log\Re q(u)$ and
$T_N(u)=\sum_{m=1}^N(-1)^{m+1}u^{2m}M_m/m$.
If every positive-half-plane occurrence has real part at least $d>0$,
$u^2<d^2$, and $\sum_a|a|^{-2}\le C$, then
$$|G(u)-T_N(u)|\le \frac{C u^2(u^2/d^2)^N}{(N+1)(1-u^2/d^2)}.$$

## Assumptions

The gap and mass bound are explicit hypotheses for this reusable estimate.
The function, reciprocal transform and multiplicity-counted paired zero
product are the actual previously defined objects. There is no RH
assumption, numerical oracle, root-list completeness or simplicity assumption.

## Proof Sketch

Absolute summability of inverse-square zero norms implies summability of
every positive even inverse power, using the established zero norm gap.
The actual paired product on the imaginary axis is the inverse reciprocal
transform. The sum of the factor logarithms exponentiates to this product.
Taking norms and real logarithms identifies its real part with $G(u)$,
using actual positivity of the reciprocal transform. This avoids any
unsupported identity for the principal logarithm of an infinite product.

Apply the finite complex logarithm Taylor remainder to each factor
$1+u^2/a^2$. Its norm parameter is at most $u^2/d^2<1$.
Retain one inverse-square factor and bound the other powers by the
uniform ratio. Sum this absolutely summable error bound over occurrences.
Only a finite Taylor sum is interchanged with the zero sum; the
index-zero summand vanishes because its denominator is zero.
Real parts of the remaining terms give exactly the displayed moments.
Finally apply the mass bound $C$.

## Lean Artifacts

- File: `XiMomentExpansionFull.lean`.
- Main theorem: `ReciprocalXi.F_momentTaylor_error_of_mass_bound`.
- Actual-mass version: `ReciprocalXi.F_momentTaylor_actual_error`.
- Product identity: `ReciprocalXi.F_momentLog_eq_sum_logarithm`.
- Definitions: `F_pairMoment`, `F_momentLog`, `F_momentTaylor`.
- All helper theorems are included in `AuditXiMomentExpansion.lean`.

This is an analytic component, not the completed finite-zero certificate
or the global density log-concavity theorem.
