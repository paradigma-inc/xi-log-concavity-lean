# Actual zero heat trace: convergence, integrability and reality

## Statement

For all actual positive-half-plane zero occurrences $a$, $\operatorname{Re}(a^2)>0$ and $\sum_a1/\operatorname{Re}(a^2)<\infty$. The trace $H(t)=\sum_a e^{-a^2t}$ is absolutely convergent for $t>0$, continuous there, integrable on $(0,\infty)$ and real-valued. Its integral is $\sum_a a^{-2}$.

## Assumptions

These are actual-function results, without RH, a supplied zero list or a trace-positivity assumption.

## Proof Sketch

Actual strip geometry gives $\operatorname{Re}a>1$ and $|\operatorname{Im}a|<1$, hence $\operatorname{Re}(a^2)>0$. Outside finitely many occurrences, $\operatorname{Re}(a^2)\ge|a|^2/2$, so the already proved inverse-square series controls the new reciprocal series. Exponential decay is bounded by $1/(t\operatorname{Re}(a^2))$, proving absolute convergence and locally uniform convergence away from zero. Each term has integral of its norm exactly $1/\operatorname{Re}(a^2)$. Tonelli and the norm-sum inequality give integrability of the trace; summable norm integrals justify exchanging integral and sum. Finally conjugation is an involution on actual zero occurrences, preserving multiplicity, and reindexes the trace to its complex conjugate.

Reality is not nonnegativity. The finite-low-zero and tail-domination proof required for a positive residual law remains open.

## Lean Artifacts

- `XiHeatTraceFull.lean`
- Main results: `summable_norm_F_zeroHeatTerm`, `continuousOn_F_zeroHeatTrace`, `integrableOn_F_zeroHeatTrace`, `integral_F_zeroHeatTrace`, `F_zeroHeatTrace_im`.
