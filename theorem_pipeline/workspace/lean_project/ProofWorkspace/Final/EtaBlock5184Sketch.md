# Actual eta enclosures for source indices 5184–5215

## Statement

The stored endpoint pairs enclose the actual eta integral at every grid index $5184\le k<5216$, with width below $10^{-120}$. The output root state is exactly the canonical state at $5216$.

## Assumptions

Only the displayed finite index-range hypothesis remains. The initial root state and all signed Euler weights were previously certified. Generated literals are proposals, not assumptions.

## Proof Sketch

The kernel checks the exact $32$-step batch using all $400$ signed Euler weights and both outward-rounded root-power components. Projection of that equality and the generic canonical-state theorem identify the final state and each output pair. The established eta remainder theorem then encloses the actual integral, including the positive $2^{-400}$ remainder. A finite comparison verifies the stated width. This is an eta-factor certificate; the full reciprocal-Xi source comparison is established separately.

## Lean Artifacts

- File: `EtaBlock5184Full.lean`.
- Theorems: `sourceEtaBatch5184_checked`, `sourceEtaRootStates5216_eq`, `sourceEtaBatch5184_entry`, `sourceEtaBatch5184_actual_enclosure`, `sourceEtaBatch5184_width`.
