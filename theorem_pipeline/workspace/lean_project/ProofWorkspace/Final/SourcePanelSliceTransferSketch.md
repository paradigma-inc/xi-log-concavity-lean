# Exact source-slice reuse in a coefficient transition

## Statement and assumptions

`sourcePanelChunkCheck_of_slice` proves the original transition check from an
exactly equal literal source slice and the corresponding exact recurrence
calculation. The assumptions retain the original offset $256i$, block length
$\min(256,13601-256i)$, all 65 coefficients, rotation state, and accumulator.

## Proof sketch

Unfold the definition of the original transition and substitute the certified
slice equality into the recurrence calculation. Equality substitution changes
only the expression used to calculate the values, not the values, recurrence,
indices or target state. Concrete source-slice and recurrence equalities remain
separate kernel-checked numerical obligations.

## Lean artifact

- File: `SourcePanelSliceTransferFull.lean`.
- Theorem: `ReciprocalXi.sourcePanelChunkCheck_of_slice`.
- This helper alone does not certify a concrete source slice or panel.
