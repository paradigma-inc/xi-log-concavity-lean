# Actual reciprocal-Xi source bounds through index 383

## Statement

`sourceRoundedMidpoint_first384_bound` proves the unchanged $2\cdot10^{-120}$ source-midpoint error for every $0\le k<384$.

## Assumptions

Only the index-range hypothesis remains. Each eta block, Gamma factor, power identity, positive Xi lower endpoint and reciprocal comparison is proved rather than supplied as numerical evidence.

## Proof Sketch

The shared analytic assembly encloses actual Xi using the certified eta block and power tables. Kernel checks establish denominator positivity and containment of the outward reciprocal interval within the fixed source error band. Exact lookup identities identify the midpoint with the frozen source array. Splitting the index range at $352$ combines this block with the previous cumulative theorem. All arithmetic, rounding, and error allowances are unchanged from the first accepted block.

## Lean Artifacts

- File: `SourceBlock352Full.lean`.
- Theorems: `sourceBlock352Xi_enclosure`, `sourceBlock352Xi_positive_checked`, `sourceBlock352Reciprocal_check`, `sourceRoundedMidpoint_block352_bound`, `sourceRoundedMidpoint_first384_bound`.
