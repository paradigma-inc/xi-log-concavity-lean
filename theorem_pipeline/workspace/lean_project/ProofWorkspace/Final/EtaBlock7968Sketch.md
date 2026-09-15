# Actual eta enclosures for source indices 7968–7999

## Statement

The stored endpoint pairs enclose the actual eta integral at every grid index $7968\le k<8000$, with width below $10^{-120}$. The output root state is exactly the canonical state at $8000$.

## Assumptions

Only the displayed finite index-range hypothesis remains. The initial root state and all signed Euler weights were previously certified. Generated literals are proposals, not assumptions.

## Proof Sketch

The kernel checks the exact $32$-step batch using all $400$ signed Euler weights and both outward-rounded root-power components. Projection of that equality and the generic canonical-state theorem identify the final state and each output pair. The established eta remainder theorem then encloses the actual integral, including the positive $2^{-400}$ remainder. A finite comparison verifies the stated width. This is an eta-factor certificate; the full reciprocal-Xi source comparison is established separately.

## Lean Artifacts

- File: `EtaBlock7968Full.lean`.
- Theorems: `sourceEtaBatch7968_checked`, `sourceEtaRootStates8000_eq`, `sourceEtaBatch7968_entry`, `sourceEtaBatch7968_actual_enclosure`, `sourceEtaBatch7968_width`.
