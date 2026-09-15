# Eta-grid evaluation from certified eightieth roots

## Statement

`ratEtaRootGrid_enclosure` bounds the actual eta integral at every retained-grid argument $s_k=(k+40)/80$ between two outward-rounded rational endpoints. It uses rational intervals for the eightieth roots of the positive integer bases rather than logarithm and exponential initializations. The directed analytic remainder remains $2^{-N}$.

## Assumptions

The node index $k$ and Euler truncation order $N$ are arbitrary natural numbers, and the rational rounding scale $B$ is a positive natural number. Two functions $\ell,u:\mathbb N\to\mathbb Q$ supply endpoints for each base $a=j+1$, $0\le j<N$. For each such base, the required checks are exactly
$$
0\le\ell(a),\qquad 0\le u(a),\qquad
a\ell(a)^{80}\le1\le au(a)^{80}.
$$
There are no logarithm range checks, exponential range checks, assumed real-power enclosures, or assumed eta identities. The theorem does not itself evaluate these finite polynomial checks for a supplied table.

## Proof Sketch

Monotonicity of the eightieth power on nonnegative real numbers turns the polynomial checks into an actual enclosure of $a^{-1/80}$. The exact identity $(a^{-1/80})^{k+40}=a^{-s_k}$ then permits the accepted outward-rounded power recurrence to enclose each reciprocal power. This is the content of the imported root-grid theorem.

The Euler coefficient for index $j$ is the signed rational number $(-1)^j w_{N,j}$. Multiplication by this coefficient uses the minimum and maximum of the two products, so negative coefficients reverse the endpoint order correctly. Rounding these products outwards gives bounds on the actual Euler summands. Summing preserves the inequalities, and the proved eta acceleration theorem supplies the one-sided remainder
$$
0\le\eta(s_k)-\sum_{j<N}(-1)^j w_{N,j}(j+1)^{-s_k}\le2^{-N}.
$$
One final outward rounding produces the stated bounds for the actual eta integral. Its endpoints lie on the $B$-grid.

The alternative table definitions use the previously verified linear binomial-tail recurrence to share Euler weights across nodes. `ratEtaRootTableLower_eq` and `ratEtaRootTableUpper_eq` prove exact equality to the primary endpoints, not merely an approximation or a replacement interval.

## Scope

The order $N=400$ is supported without changing its analytic remainder, but this generic module does not certify any concrete root table or assert a numerical interval width. It does not compose the eta interval into Xi, validate a source-node decimal, or prove the compact curvature certificate.

## Lean Artifacts

- Proof: `ProofWorkspace/Final/RootEtaGridBoundsFull.lean`.
- Main theorem: `ratEtaRootGrid_enclosure`.
- Supporting theorems: `ratEtaRootGridTerm_enclosure`, `ratEtaRootGrid_mem_grid`, `ratEtaRootTableLower_eq`, `ratEtaRootTableUpper_eq`.

