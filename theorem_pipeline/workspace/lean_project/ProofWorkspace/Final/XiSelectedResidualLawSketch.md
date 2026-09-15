# Actual selected-Xi residual probability law

## Statement and assumptions

For a conjugation-stable subset of the actual positive-real-part Xi zero occurrences, assume its heat trace is nonnegative. The constructed Gaussian mixture of the heat-subordinator law is a genuine probability measure whose characteristic function is the exponential of the actual selected heat exponent. The module derives the needed positivity from an explicit finite low-zero certificate: all selected zeros below $T\ge100$ are real, and a selected occurrence $a$ satisfies $2\operatorname{Re}a\le T$.

For the complement of any finite deleted occurrence set, the actual reciprocal transform multiplied by the deleted factors equals this law's characteristic function under the same explicit certificate and conjugation condition.

## Proof Sketch

The selected trace has already proved integrability and reality. Its real part therefore defines an integrable nonnegative heat density under the stated positivity hypothesis. Apply the actual subordinator construction and Gaussian-mixture theorem. Reality identifies its real heat integral with the original complex exponent. The proved finite-certificate lower bound supplies positivity when the certificate holds. Finally combine with the previously proved exact finite factor-deletion identity for actual reciprocal Xi.

The finite low-zero certificate is an assumption in this theorem, not a completed numerical certificate. No supplied probability measure, RH, or infinite zero-list assumption is used. Exponential moments and global density curvature remain separate.

## Lean Artifacts

File: `XiSelectedResidualLawFull.lean`. Main theorems: `charFun_F_selectedResidualLaw`, `F_selectedResidualLaw_finite_certificate`, `reciprocalTransform_eq_residual_charFun`.

