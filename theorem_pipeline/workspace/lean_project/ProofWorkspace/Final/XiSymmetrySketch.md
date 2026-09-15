# Reflection symmetry of the reciprocal-Xi density

## Statement

For the actual inverse Fourier expression defined in `XiDefinitionFull.lean`,
$\Lambda(-x)=\Lambda(x)$. Its first derivative is odd and its second derivative
is even. Consequently the curvature expression
$H(x)=\Lambda'(x)^2-\Lambda(x)\Lambda''(x)$ is even.

## Assumptions and conventions

No new analytic assumption is made. These results use the already proved
evenness of the normalized reciprocal transform and Lebesgue measure's
reflection invariance. They remain valid under mathlib's total integral and
derivative conventions, which assign values even when integrability or
differentiability fails. Thus they do not establish either regularity or
positivity; those obligations remain separate.

## Proof Sketch

Write the Fourier integrand as $\phi(u)e^{-ixu}$, with $\phi(-u)=\phi(u)$.
Reflecting both $x$ and $u$ preserves the integrand, and the substitution
$u\mapsto-u$ preserves Lebesgue measure. Taking real parts and applying the
unchanged normalization gives density evenness. Differentiating the reflection
identity changes the sign once and restores it after the second derivative.
Substitution into the curvature numerator proves its evenness.

## Lean Artifacts

File: `XiSymmetryFull.lean` in `ProofWorkspace/Final`.

Theorems: `ReciprocalXi.density_integrand_reflection`,
`ReciprocalXi.density_even`, `ReciprocalXi.deriv_odd_of_even`,
`ReciprocalXi.deriv_even_of_odd`, `ReciprocalXi.density_deriv_odd`,
`ReciprocalXi.density_second_deriv_even`, and
`ReciprocalXi.density_curvature_even`.

The last result supplies the actual density's symmetry premise for the
compact-plus-tail curvature argument. The positivity premises are not proved here.
