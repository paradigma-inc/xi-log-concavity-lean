# Actual eta enclosures for source indices 6880–6911

## Statement

The stored endpoint pairs enclose the actual eta integral at every grid index $6880\le k<6912$, with width below $10^{-120}$. The output root state is exactly the canonical state at $6912$.

## Assumptions

Only the displayed finite index-range hypothesis remains. The initial root state and all signed Euler weights were previously certified. Generated literals are proposals, not assumptions.

## Proof Sketch

The kernel checks the exact $32$-step batch using all $400$ signed Euler weights and both outward-rounded root-power components. Projection of that equality and the generic canonical-state theorem identify the final state and each output pair. The established eta remainder theorem then encloses the actual integral, including the positive $2^{-400}$ remainder. A finite comparison verifies the stated width. This is an eta-factor certificate; the full reciprocal-Xi source comparison is established separately.

## Lean Artifacts

- File: `EtaBlock6880Full.lean`.
- Theorems: `sourceEtaBatch6880_checked`, `sourceEtaRootStates6912_eq`, `sourceEtaBatch6880_entry`, `sourceEtaBatch6880_actual_enclosure`, `sourceEtaBatch6880_width`.
