# Executable coefficient form of the original panel check

## Statement

`sourcePanelCheck_iff_dense` proves that the original recorded-bound checker succeeds exactly when a fixed-range rational predicate holds. No error allowance, recorded bound, or mathematical input is changed.

## Assumptions

The equivalence holds for every integer coefficient list and every one of the $318$ panel indices. It does not assert that any particular list is the computed source stream, or that any panel has passed the predicate.

## Proof Sketch

For the degree-$64$ polynomial $P$, define its coefficient function to be the supplied coefficient at indices below $65$ and zero thereafter. The coefficient identities for differentiation give the first two derivative coefficient functions. The antidiagonal product formula then gives every coefficient of $P'^2-PP''$ by finite rational sums. All three input coefficient functions vanish at indices at least $65$, so the curvature coefficients vanish at indices at least $129$. These vanishing statements identify the support-based absolute coefficient norms exactly with sums over fixed ranges, including the norm with the constant curvature coefficient removed. Substitution into the previously proved checker yields an equivalent executable predicate. This replaces non-executable support decisions, not the inequalities being certified.

## Lean Artifacts

- Full proof: `SourcePanelDenseFull.lean`.
- Main theorem: `sourcePanelCheck_iff_dense`.
- Supporting identities: `ratCurvaturePolynomial_coeff_dense`, `ratPanelOffNorm_eq_dense`, and `sourcePanelChecks_iff_dense`.

The actual-density implication remains the earlier `sourcePanelCheck_density_curvature_pos`, with its explicit actual-Xi sample-accuracy premise.
