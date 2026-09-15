# Selected actual heat trace: weighted integrals and reality

## Statement

Every selected actual-zero heat trace is continuous and integrable on $t>0$. If $x<\operatorname{Re}(a^2)$ for every selected occurrence, then $e^{xt}H_S(t)$ is absolutely integrable and
$$\int_0^\infty e^{xt}H_S(t)\,dt=\sum_{a\in S}(a^2-x)^{-1}.$$
The trace is real when the selected set is closed under conjugation.

## Assumptions

The selected set consists of actual multiplicity occurrences. The weighted integral has the explicit strict spectral-gap assumption above. Reality has an explicit conjugation-stability assumption. Neither positivity nor a probability measure is assumed or established here.

## Proof Sketch

Absolute inverse-square summability implies reciprocal-gap summability: outside finitely many terms the shifted denominator is at least half the original positive real squared-root part. A uniform bound on each closed positive-time interval gives continuity of the trace. Exact exponential integrals and Tonelli bound the integral of the absolute sum; they also justify exchanging the sum and integral. Finally, the actual conjugation involution restricts to the selected set and pairs conjugate heat terms, giving reality.

## Lean Artifacts

- File: `XiSelectedHeatIntegralFull.lean`
- Main results: `integrableOn_F_selectedHeatTrace_weight`, `integral_F_selectedHeatTrace_weight`, `F_selectedHeatTrace_im` in namespace `ReciprocalXi`.
