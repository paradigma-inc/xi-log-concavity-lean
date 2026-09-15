# Rational forms of the theta coefficient transitions

## Statement

The rational coordinate formulas for the first, A, and B transitions embed exactly into the complex normalized transitions at exponent $-3/4+12i$.

## Assumptions

These algebraic identities are unconditional under Lean's field convention. Using them for actual derivatives still requires the previously proved positive-center analytic identities.

## Proof Sketch

Unfold the rational pairs, push the field embeddings through arithmetic, and use ring identities. Subtraction is compatible with the same embedding.

## Lean Artifacts

`RationalThetaTransitionFull.lean`: ratComplexValue_sub, ratThetaFirst_value, ratThetaA_value, ratThetaB_value.
