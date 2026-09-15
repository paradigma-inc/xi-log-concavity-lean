# Integer arithmetic for identical rounded eta sums

Source: `workspace/contexts/reciprocal_xi_global_logconcavity.md`.
Run: `20260909T204310Z_e45f`.

For an integer $a$ and natural denominator $d$, fixed-grid lower rounding of
$a/d$ is exactly $\lfloor Ba/d\rfloor/B$, computed with Euclidean integer
division. Upper rounding is $-\lfloor-Ba/d\rfloor/B$. These identities hold
also for negative numerators; the library's total zero-denominator convention
is preserved, not used as a positivity argument.

Writing a rational Euler weight as its exact numerator divided by denominator
turns each signed eta term into one integer numerator and a positive integer
power denominator. Sum the integer lower/upper numerators first and divide by
$B$ only once. Exact equality to both previously proved rounded eta sums is
established, so their zeta enclosures and analytic errors remain unchanged.
No native computation, numeric oracle or source-node accuracy assumption is
used. This optimization alone is not a retained Xi node certificate.

