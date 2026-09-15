# Selected heat trace: candidate exponential-moment exponent

## Statement

For $x\ge0$, the positive-time kernel satisfies
$$|(e^{xt}-1)/t|\le x e^{xt}.$$
If $x<\operatorname{Re}(a^2)$ for every selected actual occurrence, its product with the selected heat trace is absolutely integrable. The integral is real for conjugation-stable selected sets and has nonnegative real part when the selected trace has nonnegative real part.

## Assumptions

The strict spectral-gap, conjugation and nonnegativity conditions are explicit where used. No probability measure is assumed or constructed.

## Proof Sketch

The elementary exponential tangent inequality gives the kernel bound. The already proved weighted absolute integrability of the actual selected trace then dominates the new integrand. Continuous linear maps commute with the Bochner integral to give reality and nonnegativity from the corresponding pointwise properties. This defines a candidate moment exponent, not an actual moment of a measure.

## Lean Artifacts

- File: `XiMomentExponentFull.lean`
- Main results: `integrableOn_F_selectedMomentIntegrand`, `F_selectedMomentExponent_im`, `F_selectedMomentExponent_re_nonneg` in namespace `ReciprocalXi`.
