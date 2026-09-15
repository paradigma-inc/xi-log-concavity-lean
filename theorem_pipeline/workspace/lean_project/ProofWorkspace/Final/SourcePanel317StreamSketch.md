# Exact source coefficient stream for panel 317

## Statement

`sourcePanel317Candidate_stream` states that the original integer coefficient evaluator, at center $635/200$ and using every one of the $13{,}601$ frozen source midpoints and the original pi midpoint, returns exactly the displayed $65$-coefficient vector. `sourcePanel317_stream_passes` connects that equality to the already checked original recorded inequalities.

## Assumptions and scope

The finite stream identity and inequalities have no hypotheses. They do not assert that all source midpoints approximate the actual Xi transform; the separate $2\cdot10^{-120}$ accuracy bounds for the complete source table are still needed before a statement about the actual Fourier density follows.

## Proof Sketch

The proved direct-list traversal identity replaces indexed sample lookups without changing the weight sequence, trigonometric recurrence, floor divisions, or accumulation order. Lean's kernel checks $54$ successive blocks separately, including both the rotated state and all $65$ accumulated coefficients at every boundary. The proved split identity composes these exact transitions into the original full calculation. Substitution into `sourcePanel317Candidate_passes` establishes the recorded inequalities for the exact source stream. The source generator and external integer proposal supply literals only; they are not trusted proof oracles.

## Lean Artifacts

- File: `SourcePanel317StreamFull.lean`.
- Theorems: `sourcePanel317Candidate_stream`, `sourcePanel317_stream_passes`.
