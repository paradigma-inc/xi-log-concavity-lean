# Incremental retained-power table verification

## Statement

`retainedPiPair_succ` and `retainedTwoPair_succ` identify one step of the existing outward-rounded power evaluators. `sourcePowerTable_sound` proves that a finite table with a checked initial value and checked adjacent transitions equals the original evaluator at every covered index.

## Assumptions

The generic table theorem requires explicit initial-value and transition equalities; these must be kernel-checked for each concrete table. The two retained-power step identities have no numerical assumptions.

## Proof Sketch

The two power identities follow from the defining rounded-power recurrence. Induction on the table index transports the initial equality through the checked transitions. This reuses a previously certified boundary value instead of repeatedly calculating the whole prefix. It changes no interval endpoint, rounding direction, or actual function bound.

## Lean Artifacts

- File: `SourcePowerTableFull.lean`.
- Theorems: `retainedPiPair_succ`, `retainedTwoPair_succ`, `sourcePowerTable_sound`.
