# Finite rational exponential seed certificate

## Statement

A rational coordinate-pair trace satisfying `ratComplexExpSeedValid` approximates its actual complex exponential to absolute error at most $10^{-43}$.

## Assumptions

The input has nonpositive real part and unit-norm after division by 1024. The initial state differs from the exact 40-term Taylor sum by coordinate error at most $2\cdot10^{-60}$; all ten pre-squaring states have norm at most one; and every rounded square has coordinate error at most $2\cdot10^{-60}$. All conditions are explicit finite rational comparisons. No particular trace has been certified in this generic module.

## Proof Sketch

Embed each rational pair into the complex numbers using the proved arithmetic identities. Coordinate error bounds dominate complex norm errors. Apply the previously proved degree-39 Taylor remainder and ten-step rounded-squaring estimate; exact rational arithmetic bounds the total by $10^{-43}$.

## Lean Artifacts

`RationalComplexExpSeedFull.lean`: ratComplexValue_distance_le, ratComplexExpSeedValid_error.
