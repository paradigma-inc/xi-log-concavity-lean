# First actual retained source sample

Let $\varphi(u)=\xi(1/2)/\xi((1+u)/2)$ be the actual reciprocal-Xi transform. Let $v_1$ be the exact rational value of the source script's 160-significant-digit, round-half-even midpoint of JSONL row $k=1$. This module proves unconditionally
$$|\operatorname{Re}\varphi(1/40)-v_1|\le2\cdot10^{-120}.$$
It also proves the same bound for the exact rational average of the row's endpoints. These centers differ by $2.5\cdot10^{-160}$; the source-rounded center is not silently replaced by the exact average.

The proof uses the actual Xi/eta/Gamma identity and the accepted directed rational evaluator. All 400 algebraic root enclosures, applicability checks, eta endpoints, elementary factors and candidate-ratio comparisons are kernel-checked. The shared 440-row integer-zeta table certifies the two actual log-Gamma endpoint pairs at $1/4$ and $41/160$. These discharge the final numerical hypotheses, giving the unconditional actual-value theorem.

The intermediate `first_source_node_bound_of_gamma_literals` exposes a general center, candidate-interval comparisons and both Gamma identities as parameters. The final two theorems supply proofs of every one of those parameters. Standard Lean foundations are the only axioms.

Source: `evidence/results/reciprocal_xi_fourier_nodes.jsonl.gz`, row $k=1$; the rounded midpoint semantics are `reproduction/scripts/certify_reciprocal_xi_compact_logconcavity.py`, `mid`, under the imported 160-digit `NEAR` context. The literal midpoint and its exact discrepancy are included in the Lean module.

This is one retained nonzero sample, not the full 13,601-sample table, compact certificate, global positivity/log-concavity theorem, or a final independent audit.
