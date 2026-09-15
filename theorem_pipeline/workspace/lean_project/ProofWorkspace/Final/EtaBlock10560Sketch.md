# Actual eta enclosures for source indices 10560–10591

## Statement

The stored endpoint pairs enclose the actual eta integral at every grid index $10560\le k<10592$, with width below $10^{-120}$. The output root state is exactly the canonical state at $10592$.

## Assumptions

Only the displayed finite index-range hypothesis remains. The initial root state and all signed Euler weights were previously certified. Generated literals are proposals, not assumptions.

## Proof Sketch

The kernel checks the exact $32$-step batch using all $400$ signed Euler weights and both outward-rounded root-power components. Projection of that equality and the generic canonical-state theorem identify the final state and each output pair. The established eta remainder theorem then encloses the actual integral, including the positive $2^{-400}$ remainder. A finite comparison verifies the stated width. This is an eta-factor certificate; the full reciprocal-Xi source comparison is established separately.

## Lean Artifacts

- File: `EtaBlock10560Full.lean`.
- Theorems: `sourceEtaBatch10560_checked`, `sourceEtaRootStates10592_eq`, `sourceEtaBatch10560_entry`, `sourceEtaBatch10560_actual_enclosure`, `sourceEtaBatch10560_width`.
