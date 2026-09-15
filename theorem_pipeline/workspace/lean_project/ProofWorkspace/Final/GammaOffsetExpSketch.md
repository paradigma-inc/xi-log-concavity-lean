# Actual Gamma enclosures for all 160 shared offsets

## Statement

For every $0\le r<160$, the stored exponential pair encloses $\Gamma(1+(r-80)/160)$.

## Assumptions

No Gamma-value or numerical-certificate hypotheses remain. The theorem combines separately kernel-checked Gamma-log and exponential endpoint tables with the established analytic Gamma-series and exponential remainder bounds.

## Proof Sketch

Each logarithmic table entry is identified with its individually certified Gamma-series endpoint pair. The checked exponential-table equality and the exact scan-evaluator identity then identify its exponential pair with the accepted Gamma evaluator. The residue lies in $[-1/2,1/2]$, and the already checked range-reduction inequalities discharge the evaluator's remaining applicability conditions. Its analytic soundness theorem yields the actual Gamma enclosure. Positive recurrence multipliers can reuse these $160$ values at every retained grid argument.

## Lean Artifacts

- File: ProofWorkspace/Final/GammaOffsetExpFull.lean
- Theorems: sourceGammaLogPairs_eq, sourceGammaExpPairs_eq_fast, gammaOffsetResidue_bound, sourceGammaExp_actual_enclosure.

