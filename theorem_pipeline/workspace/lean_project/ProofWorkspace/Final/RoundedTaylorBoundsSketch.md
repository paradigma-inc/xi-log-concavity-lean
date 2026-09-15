# Fully rounded exponential evaluation

For a positive integer grid scale $B$, the recursive term interval encloses
$q^k/k!$. The recurrence multiplies by $q/(k+1)$, selects the lower/upper
product according to its sign, and rounds outward. Thus it works for negative
as well as positive $q$. Summing these intervals encloses the Taylor polynomial.

For $|q|\le1$ and $n>0$, the accepted analytic Taylor error is at most
$(n+1)/(n!n)$, since $|q|^n\le1$. This uniform bound avoids forming a large
exact rational power in the error itself. Adding/subtracting it produces an
interval for the actual $\exp(q)$.

For $m,n,B>0$ and $|q/m|\le1$, clamp the lower Taylor endpoint to zero,
round the endpoints and use the proved rounded power iteration. The identity
$\exp(q/m)^m=\exp(q)$ gives `ratExpFullyRounded_enclosure`.
Every Taylor-term update and power-product update is rounded to the fixed grid.
The concrete theorem `exp_half_fullyRounded_certified` additionally executes
kernel-checked arithmetic at $q=1/2$, $m=1$, $n=128$, $B=10^{180}$ and proves
the actual exponential is enclosed in an interval of width less than $10^{-160}$.
No runtime-only decision or supplied decimal value is used. This witnesses the
arithmetic precision of this primitive, not the complete retained Xi table.
