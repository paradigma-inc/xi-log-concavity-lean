# Certified logarithms of dyadic panel centers

## Statement

Nine stored eighty-decimal rational values approximate $\log2$ and $\log((17+2i)/16)$ for $i=0,\ldots,7$, each with absolute error at most $10^{-70}$.

## Assumptions

None. Every rational endpoint comparison is checked by Lean.

## Proof Sketch

Apply the previously proved logarithm enclosure with eighty terms of the expansion in $(q-1)/(q+1)$. Evaluate both rational endpoints exactly, and compare the stored rational value against that interval. The midpoint values were generated from rational series calculations, but the proof depends only on Lean's exact checks of their enclosures.

## Lean Artifacts

- Full proof: `XiThetaLogSeedsFull.lean`
- Theorems: `thetaLogTwoSeed_error` and `thetaLogBase0Seed_error` through `thetaLogBase7Seed_error`.
