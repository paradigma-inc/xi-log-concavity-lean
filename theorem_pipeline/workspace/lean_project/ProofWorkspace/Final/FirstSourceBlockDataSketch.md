# First 160 source midpoints and elementary factor tables

## Statement

The stored pi-power and base-two-power endpoint pairs equal the accepted outward-rounded evaluators for every $0\le k<160$. The source-midpoint list has $160$ positive values, each at most $1$.

## Assumptions

No arithmetic hypotheses remain in these finite checks. The source values are the exact results of replaying the source script's $160$-significant-digit round-half-even midpoint operation. Their approximation to actual reciprocal Xi is not asserted in this module.

## Proof Sketch

The previously proved root bounds supply the pi and base-two power evaluators. Lean's kernel checks each rational table equality, so the tables can be substituted into the established actual-factor enclosure theorems without recomputing powers. The source midpoints are carried as exact rational values, with a finite positivity and range check. Full Xi meaning additionally requires Gamma and eta enclosures and the final ratio containment test.

## Source

The retained source is reproduction/results/reciprocal_xi_fourier_nodes.jsonl.gz, SHA-256 f37fe959487881151234e89d44745e8fca746203f0f151e460e1494323114724. The first $160$ records are normalized by GammaChecks/RetainedGrid/generate_retained_grid_data.py with the original midpoint rounding mode.

## Lean Artifacts

- File: ProofWorkspace/Final/FirstSourceBlockDataFull.lean
- Theorems: sourceFirstPiPairs_eq, sourceFirstTwoPairs_eq, sourceFirstMidpoints_length, sourceFirstMidpoints_bounded.

