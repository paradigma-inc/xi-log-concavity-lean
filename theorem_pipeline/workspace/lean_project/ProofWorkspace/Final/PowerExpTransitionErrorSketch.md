# Gaussian-parameter perturbation in scaled transitions

## Statement

Under unit half-width and positive-center bounds, perturbing the Gaussian parameter by at most $\delta$ perturbs each normalized transition coefficient by at most $\delta$. For the four theta atoms the original pi midpoint gives parameter error at most $10^{-140}$.

## Assumptions

The center is nonzero for the first and A transitions, and at least one for B; the half-width is in $[0,1]$. The general parameter error is explicit. The theta specialization uses the proved source pi certificate and $k\le4$.

## Proof Sketch

Apply the exact transition-difference identities, take norms, and bound the real factors by one. Multiplying the original $10^{-150}$ pi error by $k^2\le16$ gives the conservative specialized bound.

## Lean Artifacts

`PowerExpTransitionErrorFull.lean`: abs_mul_div_le_of_unit, powerExpScaledFirst_perturbation, powerExpScaledA_perturbation, powerExpScaledB_perturbation, theta48Lambda_midpoint_error.
