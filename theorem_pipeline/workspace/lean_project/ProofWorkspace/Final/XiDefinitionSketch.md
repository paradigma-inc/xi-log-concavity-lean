# Actual Xi normalization and Fourier-density definitions

## Statement

Using mathlib's entire pole-removed completed zeta function $\Lambda_0$, define

$$
\xi(s)=\frac{s(s-1)\Lambda_0(s)+1}{2},\qquad
F(z)=\frac{\xi(1/2+iz/2)}4.
$$

The file proves that $\xi$ is entire, $\xi(0)=\xi(1)=1/2$, $\xi(1-s)=\xi(s)$, and that this definition agrees with $s(s-1)\Lambda(s)/2$ away from $0,1$. It also proves evenness of $F$, the imaginary-axis normalization $F(iu)=\xi((1+u)/2)/4$, and evenness of the normalized reciprocal transform.

## Assumptions

The Xi identities use existing mathlib completed-zeta theorems. Agreement with the meromorphic expression explicitly requires $s\ne0,1$. No claim-specific axiom or analytic hypothesis is added for these identities.

## Proof Sketch

Mathlib defines $\Lambda_0(s)=\Lambda(s)+1/s+1/(1-s)$. Multiplying by $s(s-1)$ shows that the removable correction is exactly $+1$ in the numerator defining $\xi$. The entire-function assertion follows from closure of differentiability under polynomial products and sums. The completed-zeta functional equation and a polynomial identity prove the functional equation for $\xi$, which gives the two claims about $F$. Evenness of the reciprocal transform then follows algebraically.

The actual real inverse Fourier density is defined as

$$
\lambda(x)=\frac{1}{2\pi}\operatorname{Re}\int_{\mathbb R}
\frac{F(0)}{F(iu)}e^{-ixu}\,du.
$$

**No positivity, integrability, nonvanishing-denominator, differentiability, or log-concavity result for this density is proved here.** Lean's Bochner integral and division are total operations; defining the expression does not discharge those analytic obligations.

## Lean Artifacts

- File: `ProofWorkspace/Final/XiDefinitionFull.lean`
- Definitions: `xi`, `F`, `reciprocalTransform`, `density`.
- Theorems: `xi_zero`, `xi_one`, `xi_one_sub`, `xi_eq_completed`, `differentiable_xi`, `F_even`, `F_imaginary_axis`, `reciprocalTransform_even`.
- Namespace: `ReciprocalXi`.
