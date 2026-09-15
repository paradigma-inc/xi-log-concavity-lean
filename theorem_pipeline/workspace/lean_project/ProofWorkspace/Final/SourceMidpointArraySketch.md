# Frozen rounded source-midpoint array

## Statement

The source array has exactly $13{,}601$ rational values. Every value is positive and at most $1$. Its zero-default indexed accessor is therefore nonnegative and at most $1$ at every natural index, and its real absolute value is at most $43{,}046{,}722$.

## Assumptions

No hypotheses remain for these finite size and range checks. Approximation to the actual reciprocal-Xi transform is a separate obligation and is not claimed here.

## Proof Sketch

The source normalizer replays the original $160$-significant-digit round-half-even midpoint calculation and exports its finite decimals exactly as rational literals. The identical entries are stored in blocks of at most $256$ and concatenated in source order; this bounds the size of each literal that Lean must elaborate. Lean's kernel checks the array size and the conjunction of all range comparisons. The range check uses the proved equality between array-wide and underlying-list-wide conjunction, avoiding repeated indexed traversal. Array membership transfers those comparisons to any in-range indexed value; the out-of-range default is zero. Casting to the real numbers gives the bound required by the coefficient evaluator.

## Source

Source: reproduction/results/reciprocal_xi_fourier_nodes.jsonl.gz.
SHA-256: f37fe959487881151234e89d44745e8fca746203f0f151e460e1494323114724.
Normalizer: GammaChecks/RetainedGrid/generate_retained_grid_data.py.
Literal emitter: GammaChecks/RetainedGrid/generate_source_midpoint_literals.py.
Neither generator is a trusted proof oracle.

## Lean Artifacts

- File: ProofWorkspace/Final/SourceMidpointArrayFull.lean
- Theorems: sourceMidpointArray_size, sourceMidpointArray_bounds_checked, sourceRoundedMidpoint_bounds, sourceRoundedMidpoint_abs_bound.
