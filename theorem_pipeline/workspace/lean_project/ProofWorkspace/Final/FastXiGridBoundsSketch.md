# Fast actual Xi grid enclosures

Source: `workspace/contexts/reciprocal_xi_global_logconcavity.md`.
Run: `20260909T202146Z_731e`.

For $s_k=(k+40)/80$, combine the proved intervals for
$\Gamma(s_k/2)$, $\pi^{-s_k/2}$, the accelerated eta integral and
$|s_k-1|/|1-2^{1-s_k}|$. All four factors are positive. Clamp lower endpoints
at zero, multiply the intervals, and round outwards to the fixed rational grid.

The Gamma and pi factors use the fully rounded logarithm bounds, avoiding the
large exact intermediate fractions of the preceding evaluator. The analytic
Gamma, eta, logarithm and exponential remainders are retained. At $k=40$,
use the exact removable value $\xi(1)=1/2$.

The actual reciprocal value is $\xi(1/2)/\xi(s_k)$. A positive computed
denominator lower endpoint makes interval division sound; a final outward
round encloses the exact ratio.

`XiFastEvalChecks` contains only finite rational range, positivity and
parameter checks. It does not accept an actual Xi value or a claimed
transcendental enclosure as an assumption. This module proves the evaluator's
soundness, not the retained source-node comparisons or the global density theorem.

