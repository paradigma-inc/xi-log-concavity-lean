# Polynomial bounds on a complete panel

## Statement

For a real polynomial $P$, define $N(P)=\sum_j |p_j|$ and $Q=(P')^2-PP''$. At every $|z|\le1$, $|P(z)|\le N(P)$ and $Q(z)\ge q_0-\sum_{j\ge1}|q_j|$. If each component of an actual derivative jet differs from $(P(z),P'(z),P''(z))$ by at most $e\ge0$, then

$$
q_0-\sum_{j\ge1}|q_j|-e\bigl(2N(P')+N(P)+N(P'')\bigr)-2e^2>0
$$

implies positive curvature of the actual jet. The conclusion holds on the entire panel, not just sampled points.

The recorded geometry is also proved exactly: all $318$ closed panels with centers $(2i+1)/200$ and radius $1/200$ cover $[0,318/100]$. Normalized curvature is $\delta^2$ times physical curvature, so positivity passes to physical coordinates.

## Assumptions

The polynomial coefficients and analytic value/derivative remainder estimates must be supplied. In `curvature_positive_of_enclosed_panel`, the three bounds $q_0^{\rm lower}$, $q_{\rm off}^{\rm upper}$, and $E^{\rm upper}$ must actually enclose the constant coefficient, nonconstant coefficient norm, and curvature error respectively. The theorem does not turn a recorded decimal into an analytic enclosure. Derivative data are explicit; no differentiability or derivative bound is inferred from function samples.

## Proof Sketch

On the unit interval each monomial has absolute value at most one. The triangle inequality therefore bounds a polynomial by the sum of its coefficient absolute values. Splitting off the constant term bounds the polynomial below by the constant coefficient minus the nonconstant coefficient norm. Applying this to $Q$ and combining it with the already checked three-component curvature perturbation estimate gives the positive-margin criterion.

Adjacent panels share endpoints. An induction on their number proves coverage including the two outer endpoints. The affine change of variables $x=c+\delta z$ multiplies first and second derivative components by $\delta$ and $\delta^2$; the curvature numerator consequently scales by $\delta^2$. Thus uniform normalized error bounds and positive margins for every panel imply physical curvature positivity on the complete compact interval.

## Lean Artifacts

File: `PolynomialBoundsFull.lean` in `ProofWorkspace/Final`.

Principal theorems: `ReciprocalXi.abs_eval_le_coefficientNorm`, `ReciprocalXi.coefficientNorm_erase_zero`, `ReciprocalXi.constant_sub_coefficientNorm_le_eval`, `ReciprocalXi.curvature_positive_of_polynomial_panel`, `ReciprocalXi.curvature_positive_of_enclosed_panel`, `ReciprocalXi.curvatureJet_scaled`, `ReciprocalXi.recordedPanels_cover`, and `ReciprocalXi.compact_curvature_positive_of_panels`.

## Scope

This is the algebraic and geometric compact-certificate reduction. It does not yet prove the reciprocal-Xi analytic approximations or their numerical enclosures.
