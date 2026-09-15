# Certified eta values at indices 32–63

## Statement

For every $0\le k<32$, the rational endpoints in this module enclose the actual accelerated eta integral at $s=(72+k)/80$, with width below $10^{-120}$. The final shared root-power state is exactly the canonical state for grid index $64$.

## Assumptions

There are no numerical certificate hypotheses. The input checkpoint at index $32$, signed Euler weights, root intervals, and analytic eta remainder are imported from previously verified modules.

## Proof Sketch

The established shared-state recurrence advances all $400$ rounded root powers and accumulates outward-rounded signed sums. Lean's kernel checks the exact integer output for the next $32$ grid points and the ending checkpoint. The generic recurrence theorem identifies each checked pair with the canonical eta lower and upper sums. Adding the proved Euler remainder $2^{-400}$ and outward rounding therefore gives enclosures of the actual eta integral. A second finite kernel check proves that every enclosure has width below $10^{-120}$. These are eta certificates, not full reciprocal-Xi source-sample certificates.

## Lean Artifacts

- File: ProofWorkspace/Final/EtaBatchThirtyTwoFull.lean
- Theorems: sourceEtaBatch32_checked, sourceEtaRootStates64_eq, sourceEtaBatch32_entry, sourceEtaBatch32_actual_enclosure, sourceEtaBatch32_width.

