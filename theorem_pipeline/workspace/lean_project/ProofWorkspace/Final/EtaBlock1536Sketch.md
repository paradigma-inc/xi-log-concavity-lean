# Actual eta enclosures for source indices 1536–1567

## Statement

The stored endpoint pairs enclose the actual eta integral at every grid index $1536\le k<1568$, with width below $10^{-120}$. The output root state is exactly the canonical state at $1568$.

## Assumptions

Only the displayed finite index-range hypothesis remains. The initial root state and all signed Euler weights were previously certified. Generated literals are proposals, not assumptions.

## Proof Sketch

The kernel checks the exact $32$-step batch using all $400$ signed Euler weights and both outward-rounded root-power components. Projection of that equality and the generic canonical-state theorem identify the final state and each output pair. The established eta remainder theorem then encloses the actual integral, including the positive $2^{-400}$ remainder. A finite comparison verifies the stated width. This is an eta-factor certificate; the full reciprocal-Xi source comparison is established separately.

## Lean Artifacts

- File: `EtaBlock1536Full.lean`.
- Theorems: `sourceEtaBatch1536_checked`, `sourceEtaRootStates1568_eq`, `sourceEtaBatch1536_entry`, `sourceEtaBatch1536_actual_enclosure`, `sourceEtaBatch1536_width`.
