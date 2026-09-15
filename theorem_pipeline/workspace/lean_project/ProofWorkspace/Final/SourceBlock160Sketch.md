# Actual reciprocal-Xi source bounds through index 191

## Statement

`sourceRoundedMidpoint_first192_bound` proves the unchanged $2\cdot10^{-120}$ source-midpoint error for every $0\le k<192$.

## Assumptions

Only the finite index-range hypothesis remains. The eta, Gamma, power, reciprocal and source-lookup checks are proved, not supplied as numerical assumptions. The global density theorem is not asserted.

## Proof Sketch

For indices $160$ through $191$, the certified eta block and exact power-table identities feed the shared Xi-factor theorem. A finite check proves the Xi lower endpoint positive, and another places its outward reciprocal enclosure within the source midpoint's fixed error band. The analytic assembly theorem identifies that enclosed value with the actual reciprocal-Xi transform. The source-array identity gives the required frozen midpoint. Splitting at index $160$ combines these new bounds with the previously proved first block.

## Lean Artifacts

- File: `SourceBlock160Full.lean`.
- Theorems: `sourceBlock160Xi_enclosure`, `sourceBlock160Xi_positive_checked`, `sourceBlock160Reciprocal_check`, `sourceRoundedMidpoint_block160_bound`, `sourceRoundedMidpoint_first192_bound`.
