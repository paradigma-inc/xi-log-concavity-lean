# Actual exponential high-zero budget

## Statement

For every $T\ge100$, the actual zero-occurrence sum $\sum_{\operatorname{Re}a\ge T}e^{-\operatorname{Re}a/2}$ is summable and at most $7/100$.

## Assumptions

Only the threshold range. Zeros need not be real; actual multiplicities are retained.

## Proof Sketch

For $A\ge100$, the sixth positive Taylor term proves $e^{A/2}\ge1000(A^2+1)$. Actual zero-strip geometry gives $|a|^2\le(\operatorname{Re}a)^2+1$, hence $e^{-\operatorname{Re}a/2}\le1/(1000|a|^2)$. Sum this comparison over the actual high-zero occurrences and apply the already proved global inverse-square budget of 70.

This controls the high-zero budget only, not the location or simplicity of any low zero.

## Lean Artifacts

- `XiHighZeroBoundFull.lean`
- Main results: `F_highZero_exp_le`, `summable_F_highZero_exp`, `F_highZero_exp_tsum_le`.
