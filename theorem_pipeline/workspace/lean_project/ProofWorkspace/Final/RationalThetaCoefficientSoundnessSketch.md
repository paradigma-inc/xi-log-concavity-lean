# Soundness of the finite theta-coefficient certificate

## Statement

Any forty-term rational trace satisfying `ratThetaCoefficientsValid` at the original pi midpoint, with a certified actual atom seed error at most $10^{-42}$, approximates every actual scaled Taylor coefficient within the fixed radius $E_n=40^n/(n!10^{42})$.

## Assumptions

The finite validity certificate and the explicit actual seed error are required. The center/half-width/index bounds are inside the certificate. Actual derivative recurrences and the original pi error are proved imports, not hypotheses supplied by the generator.

## Proof Sketch

Use the original pi certificate to bound perturbations of the normalized transition coefficients by $10^{-140}$. The stored-state norm bounds convert these perturbations and each rounding residual into a transition error. The first-step certificate propagates the initial seed error. Strong induction using the proved two-step error theorem then bounds every retained actual coefficient by its certified radius. Rational inequalities are transported into the reals through the order-preserving field embedding.

## Lean Artifacts

`RationalThetaCoefficientSoundnessFull.lean`: ratThetaCoefficientsValid_error.
