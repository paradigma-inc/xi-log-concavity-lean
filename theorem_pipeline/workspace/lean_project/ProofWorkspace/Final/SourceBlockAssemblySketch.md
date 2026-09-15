# Shared actual Xi and reciprocal interval assembly

## Statement

Exact pi/base-two power endpoints and an actual eta enclosure combine with the reusable Gamma table to enclose Xi. A positive lower Xi endpoint then gives an actual reciprocal-transform enclosure, and containment in a midpoint error band gives the actual source-sample error bound.

## Assumptions

The generic theorems state all required finite identities, eta enclosure, Xi positivity, and interval containment explicitly. Concrete source-block modules discharge those hypotheses by kernel checks. No global compact or tail claim is asserted here.

## Proof Sketch

The established sign-aware Xi factor formula combines the actual positive factors; the removable grid point uses the exact value $\xi(1)=1/2$. The root-based bracket is sound by the already proved denominator positivity. Monotonicity of division by positive denominators encloses the central-Xi ratio, with directed rounding at scale $10^{180}$. Finally, transitivity of the real endpoint bounds and the absolute-value interval characterization produce the $2\cdot10^{-120}$ midpoint bound. This shares the analytic proof across bounded finite packets without changing any evaluator or error allowance.

## Lean Artifacts

- File: `SourceBlockAssemblyFull.lean`.
- Theorems: `sourceGridXi_enclosure`, `sourceGridReciprocal_enclosure`, `sourceGridMidpoint_actual_bound`.
