# Finite checks for rounded theta coefficients

## Statement

The fixed radius $E_n=40^n/(n!10^{42})$ is nonnegative and, for $n<40$, at most $10^{-25}$. `ratThetaCoefficientsValid` exposes all finite rounding, state-norm, and error-propagation inequalities required for a forty-coefficient trace. Rational coordinate norms bound the corresponding complex norms.

## Assumptions

The radius facts are unconditional and the finite uniform bound is kernel evaluated. The validity predicate is a list of obligations, not a proof of any concrete trace or of agreement with the actual derivatives.

## Proof Sketch

Positivity follows from the explicit radius formula. Check its forty values using exact rational arithmetic in Lean's kernel. The norm comparison follows from the coordinate norm bound and triangle inequality. The finite validity predicate preserves the fixed rounding radius $10^{-58}$ and transition perturbation $10^{-140}$.

## Lean Artifacts

`RationalThetaCoefficientChecksFull.lean`: thetaCoefficientRadius_nonneg, thetaCoefficientRadius_uniform, ratComplexValue_norm_le_L1, complex_norm_le_rat_approx.
