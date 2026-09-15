# Exact reusable Gamma exponential endpoints

## Statement

All $160$ stored exponential endpoint pairs equal the established outward-rounded exponential evaluator applied to the stored Gamma-log endpoint pairs. The exponential range-reduction checks hold, and the resulting pairs are positive with width below $10^{-125}$.

## Assumptions

The arithmetic theorems have no hypotheses. Identification of the log table with actual Gamma logarithms is a separate imported-table bridge; these arithmetic equalities alone do not assert a Gamma enclosure.

## Proof Sketch

Each logarithmic endpoint is divided by $256$, evaluated using $128$ outward-rounded Taylor terms with the proved uniform remainder, then raised to the $256$th power by the established integer rounding recurrence. The rational output literals are proposals only until Lean's kernel checks all $160$ exact equalities, in separate declarations to bound reduction memory. Separate finite kernel checks establish applicability and widths. Reusing these certified endpoints avoids recomputing the exponential for each retained Fourier grid point.

## Lean Artifacts

- File: ProofWorkspace/Final/GammaOffsetExpKernelFull.lean
- Theorems: sourceGammaLogPairs_length, sourceGammaExpPairs_length, sourceGammaExpPairs_checked, sourceGammaLogPairs_exp_applicable, sourceGammaExpPairs_positive_narrow.
