# Source trigonometric seeds and stable recurrence error

## Statement

For rational $0\le q\le1$, define the exact rational polynomials
$$
C(q)=\sum_{j=0}^{60}\frac{(-1)^j q^{2j}}{(2j)!},\qquad
S(q)=\sum_{j=0}^{60}\frac{(-1)^j q^{2j+1}}{(2j+1)!}.
$$
The two seed bounds prove $|\cos q-C(q)|\le1/121!$ and $|\sin q-S(q)|\le1/121!$. Consequently the complex seed $C(q)+iS(q)$ is within $2/121!$ of the exact rotation $R(q)=\cos q+i\sin q$.

The exact rotation has norm one and $R(\theta)^k=R(k\theta)$. For a finite-prefix approximate sequence with $w_0=1$ and residual bounds $|w_{j+1}-w_jR(\theta)|\le e_j$, its error at step $k$ is at most $\sum_{j<k}e_j$. If the implemented seed $r$ has $|r-R(\theta)|\le\eta$, the state satisfies $|w_j|\le M$, and each implemented step has $|w_{j+1}-w_jr|\le\varepsilon$, then the error is at most $k(\varepsilon+M\eta)$.

The real-coordinate corollary matches the source loop: if each seed coordinate is within $\eta$ of the true sine/cosine, each arithmetic update coordinate has rounding residual at most $\rho$, and $|c_j|,|s_j|\le2$ for $j<k$, then both $|c_k-\cos(k\theta)|$ and $|s_k-\sin(k\theta)|$ are at most $k(2\rho+8\eta)$.

## Assumptions

The seed Taylor bounds require only the stated rational interval $0\le q\le1$, which covers the source panel seeds. The recurrence bounds assume the actual finite-prefix local rounding residuals, the seed error, and, in the approximate-seed variants, the explicit intermediate-state magnitude bound. They do not assume the desired final trigonometric error. No source decimal arithmetic is asserted certified by these hypotheses.

## Proof Sketch

For $0\le q\le1$, the sequence $q^n/n!$ is nonnegative and decreases, and its full series is summable. Restricting to the even and odd subsequences preserves these properties. The actual sine and cosine power-series identities and the alternating-series remainder theorem bound the errors of the 61-term sums by the first omitted terms, respectively $q^{122}/122!$ and $q^{123}/123!$. Both are at most $1/121!$.

The sine and cosine addition laws give the rotation power identity, and their squared identity gives unit norm. Subtracting the exact rotation recurrence from the perturbed recurrence decomposes the next error into the current residual plus the previous error multiplied by a norm-one rotation. The triangle inequality therefore accumulates residuals additively. An approximate seed contributes at most $M\eta$ per step. Finally, representing the two real source coordinates as one complex number bounds its norm by the sum of absolute coordinate values, giving the explicit factors $2$ and $8$ in the real-coordinate corollary.

## Scope

These are actual analytic bounds and exact finite-prefix propagation theorems. They neither replay the rounded source recurrence nor certify the 318 recorded coefficient matrices. The source's midpoint arithmetic errors and intermediate magnitude checks remain to be supplied as exact finite evidence.

## Lean Artifacts

- File: `ProofWorkspace/Final/SourceTrigBoundsFull.lean`
- Theorems: `ratSourceCosTaylor_error`, `ratSourceSinTaylor_error`, `sourceRotation_norm`, `sourceRotation_pow`, `sourceRotation_accumulated_error`, `sourceRotation_rounded_error`, `sourceTrigRoundedSequence_error`, `ratSourceRotation_error`.
- Source: `reproduction/scripts/certify_reciprocal_xi_compact_logconcavity.py`, the degree-120/121 seed evaluator and its cosine/sine recurrence.
- Normalized context: `theorem_pipeline/workspace/contexts/reciprocal_xi_global_logconcavity.md`.
