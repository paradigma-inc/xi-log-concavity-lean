# Original compact-panel checkpoint composition

## Statement and assumptions

For any original center indexed by $j<318$, `sourcePanelStream_eq_checkpoint` identifies the complete original integer coefficient stream with the final proposed checkpoint, provided the exact seed, initial state and all 54 consecutive block transitions are proved. Every transition uses the unchanged full source table, exact floor arithmetic, 65 coefficients, and blocks of at most 256 entries covering all 13601 samples. No finite check or actual source-sample approximation is assumed to have already passed merely by defining the transition predicate.

## Proof sketch

Splitting the original coefficient recurrence at a list boundary preserves both the rotation state and the accumulated coefficient vector. Apply that identity to the next source block and its remaining suffix. The checked transition identifies both states at the boundary, so the computation remaining before the block equals that remaining after it. Induction over all 54 blocks gives equality from the true initial state to the final state; at offset 13601 the remaining source list is empty. The previously proved array-to-stream identity then gives exactly the original stream, without omitting nodes, coefficients or rounding operations.

## Lean artifacts

- `SourcePanelCheckpointCompositionFull.lean`
- `sourcePanelRemaining_step`, `sourcePanelRemaining_all`, `sourcePanelRemaining_final`
- `sourcePanelValues_eq_checkpoint`, `sourcePanelStream_eq_checkpoint`
- Named decidability instance: `sourcePanelChunkCheck_decidable`

This generalizes the already checked panel-317 composition without editing that accepted proof. This Full file is unchanged from the passing scratch proof; individual build and axiom audit are distinct from cumulative acceptance.
