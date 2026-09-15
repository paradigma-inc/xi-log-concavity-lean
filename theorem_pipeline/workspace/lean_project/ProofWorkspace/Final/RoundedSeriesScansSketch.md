# Single-pass rounded series sums

Source: `workspace/contexts/reciprocal_xi_global_logconcavity.md`.
Run: `20260909T204310Z_e45f`.

For a pair-valued recurrence $t_{j+1}=S(j,t_j)$, a loop carrying the next term
and an accumulator is proved to return $a+\sum_{i<n}t_{j+i}$.
The proof is induction on the number of remaining terms; it does not depend
on execution outside the kernel.

Apply this equality to the signed rounded exponential recurrence and the
rounded odd-logarithm recurrence. The resulting scans have exactly the same
lower and upper sums as the accepted definitions, while computing every
recurrence step only once. In particular, min/max sign handling, term rounding,
analytic truncation errors and final scaled powers are not weakened.

This is an exact computational equivalence, not certification of the retained
Xi samples or completion of the density theorem.

