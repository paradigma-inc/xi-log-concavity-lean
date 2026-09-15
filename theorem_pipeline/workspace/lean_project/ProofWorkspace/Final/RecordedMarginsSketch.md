# Recorded compact curvature margins

## Statement

`ReciprocalXi.recordedMargins` contains all 318 rows from the reviewed compact
certificate, in source order.  Each row stores integer values
$(q_0, q_\mathrm{off}, q_\mathrm{err}, s)$ representing the exact rational
quantities $q_0/10^s$, $q_\mathrm{off}/10^s$, and
$q_\mathrm{err}/10^s$.

## Assumptions

The source JSON supplies the three decimal columns.  The generator checks the
panel indices and expected centers $0.005 + 0.01i$, and checks
$q_\mathrm{off} + q_\mathrm{err} < q_0$ while constructing the table.

## Proof Sketch

The theorem `all_recorded_margins_valid` rechecks every integer inequality with
Lean's kernel reduction through `decide`; it does not use an unchecked native
evaluator or an external computation.  `marginValue_pos_of_valid` casts one valid
integer inequality to $ℝ$, observes that $10^s>0$, and rewrites the common
denominator to obtain a strictly positive real margin.  The theorem
`recorded_margin_pos` applies that generic implication to any member of the
recorded list.  The center theorem independently checks that source order was
preserved.

This is only an arithmetic audit of reported finite data.  It does not prove
that the source values are genuine analytic enclosures for the Xi function, nor
does it prove global positivity, strict log-concavity, or PF2.

## Lean Artifacts

- File: `ProofWorkspace/Final/RecordedMarginsFull.lean`
- Theorems: `recordedMargins_length`, `recordedMargins_panels`,
  `all_recorded_margins_valid`,
  `all_recorded_centers_valid`, `marginValue_pos_of_valid`,
  `recorded_margin_pos`, `recorded_margin_lt_of_equalities`
- Source JSON SHA-256: `a761b1106436158fc4426c1d25bbca9c5fdb0b19775e53f2de1d86ecbb7ae7cd`
