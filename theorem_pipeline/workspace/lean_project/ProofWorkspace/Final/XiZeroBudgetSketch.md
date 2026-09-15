# A numerical budget for all actual zero occurrences

## Statement

The inverse squared norms of all actual Xi zero occurrences sum to at most 70. The same bound holds for positive-half-plane occurrences.

## Assumptions

None beyond the actual definitions; no finite-zero certification or RH assumption.

## Proof Sketch

The established central Xi bounds give $1/16\le|F(0)|\le1$, hence the Jensen constant $|\log|F(0)||/\log2\le4$. Sum the proved dyadic shell majorants exactly using geometric and arithmetico-geometric series: their total is $64+4C/3<70$. The actual multiplicity-weighted zero sum is bounded by this total using finite shell grouping. Reindex by each zero's finite analytic multiplicity to obtain the occurrence sum; restricting to positive-half-plane occurrences can only decrease this nonnegative sum.

## Lean Artifacts

- `XiZeroBudgetFull.lean`
- Main results: `F_zeroOccurrence_inv_norm_sq_tsum_le_seventy`, `F_pairRoot_inv_norm_sq_tsum_le_seventy`.
