# Rational Xi grid enclosure

For $s=(k+40)/80>0$, the proved actual factorization is

$$\xi(s)=\frac{s}{2}\Gamma(s/2)\pi^{-s/2}\eta(s)\frac{s-1}{1-2^{1-s}}.$$

Each factor has a proved rational evaluator. Gamma uses the exact grid recurrence. The pi factor uses the actual Machin/log-pi interval. Eta uses dyadic integer-base power intervals and the proved one-sided Euler remainder. The bracket is positive and equals $|s-1|/|1-2^{1-s}|$. Its two denominator endpoints use the proved sign on either side of $s=1$; division is permitted only after a positive rational lower bound is established. The removable grid point $k=40$ uses $\xi(1)=1/2$ exactly.

All actual factors are nonnegative, so lower endpoints can safely be clamped to zero before multiplication. `ratXiGrid_enclosure` bounds the actual entire Xi value, not a formal proxy. `XiEvalChecks` contains only explicit rational scale, exponential-range and denominator inequalities; it contains no real special-function enclosure assumptions.

The previously proved identity $\varphi(k/40)=\xi(1/2)/\xi((k+40)/80)$ then gives `ratReciprocalGrid_enclosure`, with an additional positive rational Xi lower-endpoint check. No numerical oracle is used.

These theorems establish evaluator soundness. They do not assert that the checks have been executed at every retained node, that the source decimal midpoints are certified, or that the density has globally positive curvature. Those remain separate obligations.
