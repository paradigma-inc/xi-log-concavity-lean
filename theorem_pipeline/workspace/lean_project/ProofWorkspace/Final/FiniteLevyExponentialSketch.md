# Exponential moments of a finite Lévy law

## Statement

For a finite positive measure $\mu$ and any real $q$, if $e^{qy}$ is integrable for $\mu$, it is integrable for the constructed finite Lévy law and
$$
\mathbb E e^{qY}=\exp\!\left(\int (e^{qy}-1)\,d\mu(y)\right).
$$

## Assumptions

The source measure is finite and positive. Its exponential integral at $q$ is finite. No support restriction or nonzero-mass assumption is required.

## Proof Sketch

Normalize the finite measure and apply the previously verified compound-Poisson moment theorem. For nonzero mass, normalization is a finite scalar rescaling and preserves integrability. For zero mass, normalization is a Dirac measure and the compound-Poisson intensity is zero. The identity expressing the original measure as its mass times its normalization then identifies the exponent, with integrability established before splitting the integral.

## Lean Artifacts

- File: `ProofWorkspace/Final/FiniteLevyExponentialFull.lean`
- Theorems: `integrable_exp_normalize`, `integrable_exp_finiteLevyLaw`, `exponentialMoment_finiteLevyLaw`.
