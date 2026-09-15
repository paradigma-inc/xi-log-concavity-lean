# Reusing powers across the retained grid

For $a>0$ and $s_k=(k+40)/80$, the exact identity
$a^{-s_k}=a^{-1/2}(a^{-1/80})^k$ reduces all grid powers of a fixed base to
two initial real-power intervals and a geometric recurrence.

`ratGeoRound_enclosure` proves by induction that seeded lower/upper iterations
enclose $xy^k$ for nonnegative $x,y$. Every product is rounded outward; the
lower endpoints are nonnegative and every stored result lies on the $B$-grid.
The upper-product inequalities use the corresponding proved nonnegativity.

`ratPowerGrid_enclosure` obtains the two initial intervals from the fully
rounded dyadic natural-power evaluator and proves the actual enclosure for
every $k$. Its hypotheses are only $a,m,n,B>0$ and four explicit rational
log-range checks for the initial exponents. These checks do not depend on $k$.
This proves the recurrence's meaning, not a particular source-node accuracy.
