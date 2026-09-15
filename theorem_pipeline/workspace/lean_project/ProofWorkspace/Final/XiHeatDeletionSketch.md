# Actual finite factor deletion via the heat exponent

## Statement

For any finite set $s$ of actual positive-half-plane zero occurrences and real $u$,
$$\varphi(u)\prod_{a\in s}(1+u^2/a^2)
=\exp\int_0^\infty \frac{e^{-u^2t}-1}{t}H_{s^c}(t)\,dt.$$
Each single heat term has exponential integral $a^2/(a^2+u^2)$.

## Assumptions

The zeros and multiplicities are those of the actual function. No low-zero reality, finite certificate, RH or probability-law assumption is required. The right side is an analytic residual transform; this result alone does not make it a characteristic function.

## Proof Sketch

An integrable trace admits dominated differentiation of its heat exponent, using the already checked real heat kernel. For a single actual zero the derivative is an explicit resolvent. Multiplying its exponential by $a^2+u^2$ gives a function with derivative zero and value $a^2$ at zero. The denominator is nonzero because its real part is positive. Absolute integrability permits splitting the full actual heat integral into a finite sum and its complementary trace. Exponentiating and cancelling the finite factors proves the formula.

## Lean Artifacts

- File: `XiHeatDeletionFull.lean`
- Main theorem: `ReciprocalXi.reciprocalTransform_delete_finite_heat`
- Single-term identity: `ReciprocalXi.F_heatExponentTerm_exp`
