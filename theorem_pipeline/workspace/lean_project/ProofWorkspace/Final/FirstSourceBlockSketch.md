# Actual reciprocal-Xi bounds for the first 160 source samples

## Statement

For every integer $0\le k<160$, the actual reciprocal-Xi transform at $k/40$ differs from the frozen, source-rounded midpoint by at most $2\cdot10^{-120}$.

## Assumptions and scope

The final bound has only the index-range hypothesis. It uses the actual eta, Gamma, pi-power, and base-two-power enclosures, not assumed numerical evaluations. This certifies the first $160$ source samples only, not the full $13{,}601$-sample table or the global strict log-concavity theorem.

## Proof Sketch

The reusable Gamma residue table and exact positive recurrence multiplier enclose the Gamma factor at the requested grid point. Certified pi and base-two powers, the eta interval, and the nonzero denominator bound assemble an actual Xi interval; the removable point is treated by the exact value $\xi(1)=1/2$. A finite check proves each lower endpoint positive. Dividing the certified central-Xi interval by this positive interval and rounding outwards encloses the actual reciprocal transform. A second finite comparison places each resulting interval inside the source midpoint's allowed error band. Exact prefix identities identify these local midpoints with the unchanged full source table.

## Lean Artifacts

- File: `FirstSourceBlockFull.lean`.
- Main theorem: `sourceRoundedMidpoint_first160_bound`.
- Intermediate theorems: `sourceFirstGamma_eq_retained`, `sourceFirstGamma_enclosure`, `sourceFirstBracket_enclosure`, `sourceFirstXi_enclosure`, `sourceFirstXi_positive_checked`, `sourceFirstReciprocal_enclosure`, `sourceFirstMidpoint_check`, `sourceFirstMidpoint_actual_bound`, `sourceFirstMidpoints_eq_array`.
