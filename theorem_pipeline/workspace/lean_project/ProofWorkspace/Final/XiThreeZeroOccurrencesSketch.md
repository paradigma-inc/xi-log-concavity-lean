# From simple root values to zero occurrences

## Statement

At a root of analytic order one, two actual positive zero occurrences
with the same complex value are equal. Hence completeness for three
simple root values below real coordinate $60$ implies that every other
positive occurrence has real part at least $60$.

## Assumptions

The analytic orders of the three specified roots are one. Every actual
zero with positive real part below $60$ has one of their three values.
Both simplicity and completeness remain explicit hypotheses; this module
does not certify a zero list.

## Proof Sketch

The already constructed root-fiber equivalence identifies occurrences
at a fixed root with the finite type whose cardinality is its analytic
order. When the order is one, any two fiber elements are equal.
Applying this fact to each of the three alternatives converts value
completeness into occurrence completeness. An occurrence distinct from
all three therefore cannot have real part below $60$. This explicitly
rules out unnoticed multiplicity copies.

## Lean Artifacts

- File: `XiThreeZeroOccurrencesFull.lean`.
- Theorems: `F_pairRoot_injective_at_simple`, `F_threeZero_values_to_occurrences`, `F_threeZero_other_occurrence_ge_sixty`.

