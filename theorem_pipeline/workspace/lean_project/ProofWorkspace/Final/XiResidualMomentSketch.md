# Actual selected-Xi residual moments

## Statement

For the actual selected zero heat trace, assume its real part is nonnegative on $(0,\infty)$. If every selected root $a$ obeys $q^2<\operatorname{Re}(a^2)$, the constructed residual law has finite one-sided and absolute exponential moments. Its one-sided moment is exactly $\exp(\operatorname{Re}D_S(q^2))$, and its absolute moment is at most twice that value. The residual law is preserved by negation.

## Assumptions

The set indexes actual positive-real-part Xi zero occurrences with multiplicities. Trace nonnegativity is explicit and still needs the finite low-zero certificate for the intended deletion set. The strict spectral gap is explicit. No residual measure or residual moment is supplied as an assumption.

## Proof Sketch

Take real parts of the already integrable complex moment kernel. This verifies the original heat-density exponential-integrability hypothesis. Apply the proved heat-density moment theorem and then the Gaussian variance-mixture theorem at $q$. Their exponents agree with the real part of the existing selected moment exponent by linearity of integration. The two-sided exponential inequality yields the absolute bound, and the Gaussian-mixture symmetry theorem supplies invariance under negation.

## Lean Artifacts

- File: `ProofWorkspace/Final/XiResidualMomentFull.lean`
- Theorems: `integrableOn_F_selectedMoment_real`, `F_selectedMomentExponent_re_eq`, `F_selectedResidualLaw_exponentialMoment`, `F_selectedResidualLaw_absoluteMoment`, `F_selectedResidualLaw_even`.
