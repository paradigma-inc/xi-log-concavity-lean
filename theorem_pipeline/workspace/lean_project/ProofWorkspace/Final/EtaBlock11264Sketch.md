# Actual eta enclosures for source indices 11264–11295

## Statement

The stored endpoint pairs enclose the actual eta integral at every grid index $11264\le k<11296$, with width below $10^{-120}$. The output root state is exactly the canonical state at $11296$.

## Assumptions

Only the displayed finite index-range hypothesis remains. The initial root state and all signed Euler weights were previously certified. Generated literals are proposals, not assumptions.

## Proof Sketch

The kernel checks the exact $32$-step batch using all $400$ signed Euler weights and both outward-rounded root-power components. Projection of that equality and the generic canonical-state theorem identify the final state and each output pair. The established eta remainder theorem then encloses the actual integral, including the positive $2^{-400}$ remainder. A finite comparison verifies the stated width. This is an eta-factor certificate; the full reciprocal-Xi source comparison is established separately.

## Lean Artifacts

- File: `EtaBlock11264Full.lean`.
- Theorems: `sourceEtaBatch11264_checked`, `sourceEtaRootStates11296_eq`, `sourceEtaBatch11264_entry`, `sourceEtaBatch11264_actual_enclosure`, `sourceEtaBatch11264_width`.
