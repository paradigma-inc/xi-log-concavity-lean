# Actual eta enclosures for source indices 1216–1247

## Statement

The stored endpoint pairs enclose the actual eta integral at every grid index $1216\le k<1248$, with width below $10^{-120}$. The output root state is exactly the canonical state at $1248$.

## Assumptions

Only the displayed finite index-range hypothesis remains. The initial root state and all signed Euler weights were previously certified. Generated literals are proposals, not assumptions.

## Proof Sketch

The kernel checks the exact $32$-step batch using all $400$ signed Euler weights and both outward-rounded root-power components. Projection of that equality and the generic canonical-state theorem identify the final state and each output pair. The established eta remainder theorem then encloses the actual integral, including the positive $2^{-400}$ remainder. A finite comparison verifies the stated width. This is an eta-factor certificate; the full reciprocal-Xi source comparison is established separately.

## Lean Artifacts

- File: `EtaBlock1216Full.lean`.
- Theorems: `sourceEtaBatch1216_checked`, `sourceEtaRootStates1248_eq`, `sourceEtaBatch1216_entry`, `sourceEtaBatch1216_actual_enclosure`, `sourceEtaBatch1216_width`.
