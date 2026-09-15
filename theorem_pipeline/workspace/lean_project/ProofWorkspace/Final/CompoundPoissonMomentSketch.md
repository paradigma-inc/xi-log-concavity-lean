# Compound-Poisson support and absolute first moment

## Statement

If a probability jump law is supported on nonnegative real numbers, its compound-Poisson law is also supported there. For an integrable jump law, the compound-Poisson absolute first moment is at most $r\int |y|\,d\nu$, and hence is finite.

## Assumptions

The input is a genuine probability measure; its identity function is integrable for the moment results. Nonnegative support is needed only for support preservation. No infinite sum is assumed to converge.

## Proof Sketch

Addition preserves nonnegativity under product measures and pushforwards, so induction gives support preservation for finite convolution powers. Countable positive measure mixtures preserve this property. The triangle inequality bounds a convolution's absolute first moment by the sum of the two input moments, giving an $n$-fold bound by induction. The actual Poisson first-moment series sums to $r$, proved by shifting its factorial series. Tonelli and positive scalar multiplication transfer the finite-power moment bounds through the mixture and prove integrability.

## Lean Artifacts

- File: `CompoundPoissonMomentFull.lean`
- Main results: `ReciprocalXi.ae_nonneg_compoundPoissonLaw`, `ReciprocalXi.lintegral_norm_compoundPoissonLaw_le`, `ReciprocalXi.integrable_id_compoundPoissonLaw`.
