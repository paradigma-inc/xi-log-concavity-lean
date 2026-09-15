# Exact Euler-weight tables

Source: `workspace/contexts/reciprocal_xi_global_logconcavity.md`.
Run: `20260909T204310Z_e45f`.

Let $T_j=\sum_{n\ge j}\binom{M}{n}$. The finite binomial identity gives
$T_0=2^M$ and $T_{j+1}=T_j-\binom Mj$. The next coefficient is
$\binom M{j+1}=\binom Mj(M-j)/(j+1)$, including the zero values beyond $M$.
Carry the coefficient and tail once through the list. Its $j$th entry is
$T_{j+1}/2^M$, exactly the Euler weight used by the accepted evaluator.

A length and indexed-lookup proof identifies the complete table, not a sample
of entries. Mapping an indexed summand over this table and summing is proved
equal to the original finite sum. This gives exact replacement formulas for
rounded integer-eta sums (used by zeta) and rounded noninteger eta-grid sums.
All errors and outward rounding are unchanged. No numerical Xi comparison or
global density claim is established by this optimization.

