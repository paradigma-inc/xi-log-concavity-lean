# Actual eta enclosures for source indices 8288–8319

## Statement

The stored endpoint pairs enclose the actual eta integral at every grid index $8288\le k<8320$, with width below $10^{-120}$. The output root state is exactly the canonical state at $8320$.

## Assumptions

Only the displayed finite index-range hypothesis remains. The initial root state and all signed Euler weights were previously certified. Generated literals are proposals, not assumptions.

## Proof Sketch

The kernel checks the exact $32$-step batch using all $400$ signed Euler weights and both outward-rounded root-power components. Projection of that equality and the generic canonical-state theorem identify the final state and each output pair. The established eta remainder theorem then encloses the actual integral, including the positive $2^{-400}$ remainder. A finite comparison verifies the stated width. This is an eta-factor certificate; the full reciprocal-Xi source comparison is established separately.

## Lean Artifacts

- File: `EtaBlock8288Full.lean`.
- Theorems: `sourceEtaBatch8288_checked`, `sourceEtaRootStates8320_eq`, `sourceEtaBatch8288_entry`, `sourceEtaBatch8288_actual_enclosure`, `sourceEtaBatch8288_width`.
