# Actual compact-panel derivative enclosures

## Statement

For every panel $i\in\{0,\ldots,317\}$, let $c_i=(2i+1)/200$ and let $P_i$ be the real degree-$64$ Taylor polynomial of the normalized sampled quadrature, using the certified source midpoint for $\pi$. With $t=200x-(2i+1)$ and $|t|\le1$, `sourcePanelPolynomial_derivative_errors` proves
$$
|g(x)-P_i(t)|\le E,\qquad
|g'(x)/200-P_i'(t)|\le E,\qquad
|g''(x)/200^2-P_i''(t)|\le E,
$$
where $E=8\cdot10^{-85}+\tau$ and $\tau$ is the unchanged source Taylor-remainder allowance.

`densityCompactEnclosures_of_source_coefficients` constructs the existing `DensityCompactEnclosures` structure from this actual polynomial family. The derivative-error fields are proved rather than assumed.

## Assumptions

The analytic derivative bounds require the explicit retained-node condition
$$
|\operatorname{Re}\varphi(k/40)-v_k|\le2\cdot10^{-120}
\quad(0\le k\le13600).
$$
The structure constructor additionally requires exactly the remaining three recorded coefficient conditions, for every panel: a lower bound for the constant curvature coefficient, an upper bound for the sum of the absolute nonconstant curvature coefficients, and an upper bound for the polynomial perturbation allowance. This module does not prove or numerically check any of these four finite-data obligations.

## Proof Sketch

Every panel center lies in $[0,318/100]$, so the established complex source Taylor error bound applies there. The affine identity $c_i+t/200=x$ converts normalized coordinates back to the physical real variable. The exact real Taylor bridge identifies the complex polynomial jets with the algebraic derivatives of $P_i$, and identifies the normalized complex density jets with $g$, $g'/200$, and $g''/200^2$. Substitution into the three complex real-part error inequalities proves the asserted bounds. Supplying these proved fields and the three explicit coefficient assumptions yields the existing compact evidence structure.

No curvature conclusion is assumed as a field, and no full density-curvature or log-concavity theorem is claimed here.

## Lean Artifacts

- File: `ProofWorkspace/Final/ActualPanelEnclosuresFull.lean`
- Theorems: `sourcePanelCenter_abs_le`, `sourcePanelCenter_add_coordinate`, `sourcePanelPolynomial_derivative_errors`.
- Evidence constructor: `densityCompactEnclosures_of_source_coefficients`.
- Source context: `theorem_pipeline/workspace/contexts/reciprocal_xi_global_logconcavity.md` and the recorded compact certificate; previously proved analytic error bounds are imported unchanged.
