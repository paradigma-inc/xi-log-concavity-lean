# Exact composition of the source coefficient blocks

## Statement

Splitting the source stream preserves its rotation state and coefficient accumulator. For panel $317$, the $54$ block transition identities imply that the full source calculation returns the displayed coefficient vector.

## Assumptions and scope

The split identity is generic and has no hypotheses. The panel composition assumes the exact trigonometric seed equality and all $54$ transition equalities. Those finite equalities are supplied separately by kernel checks; no actual Xi sample-accuracy claim is made here.

## Proof Sketch

Induction on the first list proves that processing a concatenation equals processing its two parts successively, carrying the rotated state and accumulated coefficients. At block $i$, the processed prefix has length $\min(256i,13601)$. The checked transition identifies both values passed to the remaining suffix. Induction over the $54$ blocks therefore preserves the final output. At the last boundary the suffix is empty, and the stored final vector equals the previously checked coefficient proposal. The initial boundary has the original seed, zero accumulator, and all source entries in their original order.

## Lean Artifacts

- File: `SourcePanelCompositionFull.lean`.
- Theorems: `intSourceCoefficientValuesFrom_append`, `sourcePanel317Remaining_step`, `sourcePanel317Remaining_all`, `sourcePanel317Remaining_final`, `sourcePanel317Values_eq_candidate`.
