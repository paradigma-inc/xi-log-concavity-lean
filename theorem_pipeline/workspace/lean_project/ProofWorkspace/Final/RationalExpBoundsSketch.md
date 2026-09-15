# Sound rational exponential enclosures

For rational $q$ and natural $n>0$, compute exactly
$P_n(q)=\sum_{k<n}q^k/k!$ and
$E_n(q)=|q|^n(n+1)/(n!n)$. Mathlib's finite exponential-series remainder theorem
proves $|e^q-P_n(q)|\le E_n(q)$ whenever $|q|\le1$.
The rational-to-real cast identities are proved explicitly. Therefore the
two rational endpoints $P_n(q)\pm E_n(q)$ enclose the actual real exponential,
not an external approximation to it.

Monotonicity extends endpoint enclosures to any real input between two rational
endpoints in the unit interval. For unrestricted rational arguments, choose a
positive natural $m$ with $|q/m|\le1$, bound $e^{q/m}$, and raise both endpoints
to $m$. Clamp the lower endpoint to zero before powering. This preserves the
inequality because the exponential is positive; the exact identity
$(e^{q/m})^m=e^q$ proves the scaled enclosure.

As a concrete kernel-checked witness, $n=12$ at $q=1/2$ gives
$1.64872127\le e^{1/2}\le1.64872128$. All finite arithmetic is rational and
checked by Lean. No floating-point oracle, new axiom, or unchecked native
decision procedure is used.

This is an exponential primitive, not a complete Xi evaluator or a verification
of the recorded Fourier quadrature nodes. Logarithm/Gamma/eta evaluation,
quadrature remainders, and the meaning of the compact coefficient witnesses
remain further work.
