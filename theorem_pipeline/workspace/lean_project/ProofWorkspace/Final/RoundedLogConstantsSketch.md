# Certified logarithm endpoint literals

Source: `workspace/contexts/reciprocal_xi_global_logconcavity.md`.
Run: `20260909T204310Z_e45f`.

At $n=400$ and $B=10^{180}$, the four displayed rational literals are proved
exactly equal to the accepted outward-rounded lower/upper endpoints for
$\log\pi$ and $\log2$. The latter uses the proved argument bound $r=1/3$.

Candidate literals were obtained by runtime evaluation only to propose the
numbers. All four equalities are then proved with `norm_num`, producing ordinary
kernel-checked proof terms. No runtime result is trusted by those proofs.
The paired lemmas allow downstream calculations to reuse these constants
without recomputing hundreds of logarithm terms. Actual logarithm meaning
comes from the existing enclosure theorems. This is not a retained Xi-node
certificate or a proof of global density curvature.

