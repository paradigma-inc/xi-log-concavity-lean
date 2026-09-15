# Actual eta enclosures for source indices 12320–12351

## Statement

The stored endpoint pairs enclose the actual eta integral at every grid index $12320\le k<12352$, with width below $10^{-120}$. The output root state is exactly the canonical state at $12352$.

## Assumptions

Only the displayed finite index-range hypothesis remains. The initial root state and all signed Euler weights were previously certified. Generated literals are proposals, not assumptions.

## Proof Sketch

The kernel checks the exact $32$-step batch using all $400$ signed Euler weights and both outward-rounded root-power components. Projection of that equality and the generic canonical-state theorem identify the final state and each output pair. The established eta remainder theorem then encloses the actual integral, including the positive $2^{-400}$ remainder. A finite comparison verifies the stated width. This is an eta-factor certificate; the full reciprocal-Xi source comparison is established separately.

## Lean Artifacts

- File: `EtaBlock12320Full.lean`.
- Theorems: `sourceEtaBatch12320_checked`, `sourceEtaRootStates12352_eq`, `sourceEtaBatch12320_entry`, `sourceEtaBatch12320_actual_enclosure`, `sourceEtaBatch12320_width`.
