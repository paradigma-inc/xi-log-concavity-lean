# Actual eta enclosures for source indices 2336–2367

## Statement

The stored endpoint pairs enclose the actual eta integral at every grid index $2336\le k<2368$, with width below $10^{-120}$. The output root state is exactly the canonical state at $2368$.

## Assumptions

Only the displayed finite index-range hypothesis remains. The initial root state and all signed Euler weights were previously certified. Generated literals are proposals, not assumptions.

## Proof Sketch

The kernel checks the exact $32$-step batch using all $400$ signed Euler weights and both outward-rounded root-power components. Projection of that equality and the generic canonical-state theorem identify the final state and each output pair. The established eta remainder theorem then encloses the actual integral, including the positive $2^{-400}$ remainder. A finite comparison verifies the stated width. This is an eta-factor certificate; the full reciprocal-Xi source comparison is established separately.

## Lean Artifacts

- File: `EtaBlock2336Full.lean`.
- Theorems: `sourceEtaBatch2336_checked`, `sourceEtaRootStates2368_eq`, `sourceEtaBatch2336_entry`, `sourceEtaBatch2336_actual_enclosure`, `sourceEtaBatch2336_width`.
