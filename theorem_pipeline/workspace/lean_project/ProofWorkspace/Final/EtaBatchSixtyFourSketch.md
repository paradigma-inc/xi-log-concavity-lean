# Certified eta values at indices 64–159

## Statement

For every $0\le k<96$, the rational endpoints enclose the actual eta integral at $s=(104+k)/80$, with width below $10^{-120}$. The ending checkpoint equals the canonical root-power state for grid index $160$.

## Assumptions

No numerical or analytic hypotheses remain. Previously proved root intervals, the checkpoint at index $64$, and the Euler remainder are reused.

## Proof Sketch

The same shared-state evaluator used for the first two batches computes $96$ additional lower and upper integer sums while advancing $400$ root powers. A kernel check verifies the integer sums and ending state. The generic batch identities identify these exact values with the canonical accelerated eta sums, and the analytic remainder $2^{-400}$ gives the actual eta enclosures. A finite kernel check establishes their widths. This extends eta certification only; Gamma and the remaining factors are still needed for full reciprocal-Xi samples.

## Lean Artifacts

- File: ProofWorkspace/Final/EtaBatchSixtyFourFull.lean
- Theorems: sourceEtaBatch64_checked, sourceEtaRootStates160_eq, sourceEtaBatch64_entry, sourceEtaBatch64_actual_enclosure, sourceEtaBatch64_width.

