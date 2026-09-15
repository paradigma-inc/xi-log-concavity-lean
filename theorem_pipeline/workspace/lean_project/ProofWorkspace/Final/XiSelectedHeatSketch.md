# Selected actual-zero heat trace: finite certificate interface

## Statement

For any subset $S$ of actual positive-half-plane zero occurrences, assume every selected zero with real part below $T\ge100$ is real, and that $S$ contains an occurrence $a$ with $2\operatorname{Re}a\le T$. For every $t>0$,
$$\operatorname{Re}H_S(t)\ge\frac{93}{100}e^{-(\operatorname{Re}a)^2t}>0.$$

## Assumptions

The finite low-zero reality condition and designated occurrence are explicit hypotheses. They have not yet been certified for the intended residual subset. No RH assumption about unbounded heights or positive-measure representation is made.

## Proof Sketch

Split the actual selected occurrences into those below $T$ and the rest. The low terms are positive real exponentials and contribute at least the designated term. The high terms have real-part lower bound $-(7/100)e^{-(\operatorname{Re}a)^2t}$, using the unconditional actual-zero exponential budget, including multiplicities. Absolute convergence justifies the split and taking real parts. Adding the bounds gives the result. This is a proved conditional interface, not a completed low-zero certificate.

## Lean Artifacts

- File: `XiSelectedHeatFull.lean`
- Main theorem: `ReciprocalXi.F_selectedHeatTrace_lower_of_finite_zero_certificate`
