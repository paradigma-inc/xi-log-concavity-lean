# Scaled power–exponential transitions

## Statement

At each positive real center, the actual scaled Taylor coefficients satisfy explicit normalized first- and second-order transition formulas. Changing the Gaussian parameter gives exact differences for all transition coefficients.

## Assumptions

The center is positive for derivative transitions and nonzero where cancellation is needed. Parameter-difference identities retain these assumptions explicitly.

## Proof Sketch

Normalize the already proved differential-equation recurrence by its nonzero real center and positive natural factor. Field identities then isolate the dependence on the Gaussian parameter, allowing a rigorous pi perturbation estimate later.

## Lean Artifacts

`PowerExpScaledTransitionFull.lean`: scaledPowerExpCoefficient_one_eq, scaledPowerExpCoefficient_recurrence_eq, powerExpScaledFirst_sub, powerExpScaledA_sub, powerExpScaledB_sub.
