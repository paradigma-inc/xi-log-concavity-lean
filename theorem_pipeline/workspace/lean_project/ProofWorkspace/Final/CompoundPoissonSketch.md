# Positive finite compound-Poisson construction

## Statement

For a genuine probability measure $\nu$ on $\mathbb R$ and rate $r\ge0$, the Poisson-weighted mixture of its finite convolution powers is a probability measure, with characteristic function
$$\widehat\mu(u)=\exp(r(\widehat\nu(u)-1)).$$

## Assumptions

The input is a probability measure and the rate is nonnegative. This module does not yet select the Xi-specific jump laws, take an infinite-activity limit, or prove residual exponential moments.

## Proof Sketch

Finite convolution powers are probability measures by induction. Their nonnegative Poisson weights sum to one, so the countable measure mixture is again a probability measure. The characteristic-function integrand is bounded and continuous, which justifies integration through the countable measure sum. The convolution formula gives powers of the input characteristic function. Summing the complex exponential series then gives the claimed formula. All measures here are actual positive measures, not merely candidate transforms.

## Lean Artifacts

- File: `CompoundPoissonFull.lean`
- Main theorem: `ReciprocalXi.charFun_compoundPoissonLaw`
- Probability instance: `ReciprocalXi.compoundPoissonLaw_isProbability`
