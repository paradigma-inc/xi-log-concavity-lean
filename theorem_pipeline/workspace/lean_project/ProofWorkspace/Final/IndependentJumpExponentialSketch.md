# Exponential moments of the actual infinite independent sum

## Statement

Let $\nu_n$ be probability laws supported on the nonnegative reals, with integrable coordinates and summable absolute first moments. Fix $q\ge0$. If every law has a finite exponential moment $e^{g_n}$ and $\sum_n g_n$ converges, then the previously constructed infinite independent-sum law has a finite exponential moment equal to
$$
\exp\!\left(\sum_n g_n\right).
$$

## Assumptions

The nonnegative-support, first-moment and finite-coordinate exponential-integrability hypotheses are explicit. Exponential integrability of the infinite sum is a conclusion, not a hypothesis.

## Proof Sketch

Independence gives integrability of each finite-sum exponential and the product formula for its expectation. Nonnegative coordinates make these exponentials increase with the truncation index. Almost-sure absolute convergence of the coordinates identifies their pointwise limit. Monotone convergence for nonnegative extended-real integrals then identifies the limit integral with the finite value $\exp(\sum_n g_n)$. This proves integrability of the limiting exponential before converting the identity to a real Bochner integral and pushing it forward to the actual sum law.

## Lean Artifacts

- File: `ProofWorkspace/Final/IndependentJumpExponentialFull.lean`
- Theorems: `integrable_exp_finiteJumpSum`, `exponentialMoment_finiteJumpSum`, `lintegral_exp_independentJumpSum`, `integrable_exp_independentJumpSumLaw`, `exponentialMoment_independentJumpSumLaw`.
