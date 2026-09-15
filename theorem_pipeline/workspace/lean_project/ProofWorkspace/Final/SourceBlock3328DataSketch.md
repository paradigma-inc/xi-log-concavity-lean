# Frozen source data and power intervals for indices 3328–3359

## Statement

The stored pi and base-two power pairs equal the existing outward-rounded retained-grid evaluators at all $32$ indices. The stored midpoints equal the corresponding entries of the frozen full source table.

## Assumptions

No numerical hypotheses are supplied to the finite identity theorems. The generator reads the unchanged source with SHA-256 `f37fe959487881151234e89d44745e8fca746203f0f151e460e1494323114724` and proposes values only.

## Proof Sketch

The established pi and base-two roots are advanced by the same directed integer rounding used by the retained-grid evaluators. Lean's kernel checks every proposed endpoint identity and every source-array lookup. The analytic meaning of these power intervals is supplied by the previously proved retained-grid enclosure theorems, and their use in an actual reciprocal-Xi bound is separate.

The power identities reuse the preceding block's certified final entry and check every adjacent transition. The generic induction theorem proves exact equality to the unchanged original evaluator; no accumulated rounding term is dropped.

## Lean Artifacts

- File: `SourceBlock3328DataFull.lean`.
- Theorems: `sourceBlock3328PiPairs_eq`, `sourceBlock3328TwoPairs_eq`, `sourceBlock3328Midpoints_eq_array`.
