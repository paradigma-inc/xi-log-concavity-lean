# Uniform range bounds for the rounded Gamma evaluator

## Statement

`ratLogGammaFast_abs_le_thirtytwo` bounds both rational endpoints of the existing rounded log-Gamma evaluator in absolute value by $32$, uniformly over its truncation orders. `ratLogGammaFast_scaled_checks` therefore discharges both exponential range checks at every integer scale $m\ge32$.

## Assumptions

The offset $z$ is rational with $|z|\le1/2$. The rounding scale $B$ is a positive natural number. The Gamma-series, integer-zeta, and logarithm truncation orders $N,M,L$ satisfy $N,M,L\le B$. The scaled corollary additionally requires $32\le m$. No evaluated Gamma endpoint, real-valued enclosure, or source-node value is assumed.

The condition $L\le B$ matters: the upper rounded logarithm recurrence can accumulate a positive rounding contribution at every retained term. The theorem allows zero truncation orders; it asserts a range bound, not high precision.

## Proof Sketch

Every binomial Euler weight lies between zero and one. Consequently, for an integer exponent at least two, the absolute Euler summand is bounded by $(j+1)^{-2}$. The finite reciprocal-square sum is at most $2$. Outward rounding adds at most $1/B$ per summand, so both rounded eta sums have absolute value at most $3$ when $M\le B$. The zeta conversion factor lies in $(0,2]$; including its analytic remainder and final rounding gives the common endpoint bound $9$.

For $|z|\le1/2$, the absolute value of the centered Gamma coefficient of index $k$ is at most $2^{-(k+2)}$. Their finite absolute sum is therefore at most $1/2$. Sign-aware multiplication by the zeta endpoints and rounding each coefficient term bounds the absolute coefficient sum by $9/2+N/B\le11/2$.

For each logarithm base in $[1,4]$, the transformed argument $t=(q-1)/(q+1)$ lies in $[0,3/5]$. Its exact odd logarithm series is bounded by a geometric sum. In the rounded recurrence, the step multiplier is at most $1/2$, so the upper error stays below $2/B$ per term. This gives a Taylor upper bound of $7$ when $L\le B$. Adding the explicit logarithm remainder and final rounding bounds both logarithm endpoints by $10$. The certified Machin endpoints for $\pi$ lie in $[1,4]$, so the same argument applies to the actual rounded log-$\pi$ constants. The signed constant $z\log\pi-2z\log2$ then has rational endpoint absolute bounds $17$.

Finally, combine $17$, the coefficient bound $11/2$, the Gamma-series error bound $2$, and the last rounding error at most $1$. The total is $51/2<32$. Dividing by any positive scale at least $32$ proves both required scaled range checks. The proof uses no execution of the high-precision endpoint algorithm.

## Scope

The endpoints are exactly those of `FastGammaBoundsFull`, whose separate soundness theorem already encloses the actual $\log\Gamma(1+z)$. This module supplies their uniform rational range checks. It does not prove that a chosen truncation has a specified narrow width, certify any retained Fourier-node decimal, or complete the compact curvature certificate.

## Lean Artifacts

- Final proof: `ProofWorkspace/Final/GammaRangeBoundsFull.lean`.
- Main theorems: `ratLogGammaFast_abs_le_thirtytwo`, `ratLogGammaFast_scaled_checks`.
- Supporting bounds cover rounding, Euler weights and integer eta, integer-zeta endpoints, Gamma coefficients, and rounded logarithm recurrences.

