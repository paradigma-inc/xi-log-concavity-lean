# Scaled coefficients for finite theta quadrature

## Statement

The scaled Taylor coefficients of $z^s e^{-\lambda z}$ satisfy the exact initial identities and second-order recurrence. The actual theta coefficients are twice the sum of the four atom coefficients. Each panel integral has an exact expression in these scaled coefficients.

## Assumptions

The recurrence point lies in the principal slit plane; the theta application has a positive real center. No numerical values are assumed.

## Proof Sketch

Multiply the already proved coefficient recurrence by powers of the panel half-width. Use linearity of differentiation through the finite atom sum to identify the actual theta coefficients. Rewrite the exact monomial integrals in terms of these scaled coefficients. This ties the proposed finite arithmetic recurrence to the actual function derivatives.

## Lean Artifacts

- Full proof: `XiThetaCoefficientFull.lean`
- Theorems: `scaledPowerExpCoefficient_zero`, `scaledPowerExpCoefficient_one`, `scaledPowerExpCoefficient_recurrence`, `complexThetaFiniteIntegrand_atom_sum`, `theta48TaylorCoefficient_scaled_atoms`, `theta48TaylorPanelValue_scaled`.
