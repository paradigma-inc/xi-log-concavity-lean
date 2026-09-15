# Actual reciprocal-Xi source bounds through index 10367

## Statement

`sourceRoundedMidpoint_first10368_bound` proves the unchanged $2\cdot10^{-120}$ source-midpoint error for every $0\le k<10368$.

## Assumptions

Only the index-range hypothesis remains. Each eta block, Gamma factor, power identity, positive Xi lower endpoint and reciprocal comparison is proved rather than supplied as numerical evidence.

## Proof Sketch

The shared analytic assembly encloses actual Xi using the certified eta block and power tables. Kernel checks establish denominator positivity and containment of the outward reciprocal interval within the fixed source error band. Exact lookup identities identify the midpoint with the frozen source array. Splitting the index range at $10336$ combines this block with the previous cumulative theorem. All arithmetic, rounding, and error allowances are unchanged from the first accepted block.

## Lean Artifacts

- File: `SourceBlock10336Full.lean`.
- Theorems: `sourceBlock10336Xi_enclosure`, `sourceBlock10336Xi_positive_checked`, `sourceBlock10336Reciprocal_check`, `sourceRoundedMidpoint_block10336_bound`, `sourceRoundedMidpoint_first10368_bound`.
