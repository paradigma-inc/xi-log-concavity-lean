# Common-denominator curvature arithmetic

## Statement

`sourcePanelCheck_iff_integer` proves that the original recorded panel checker is equivalent to computing the polynomial coefficients and their convolutions as integers before dividing by the common scale. The equivalence holds for every vector and every one of the $318$ panels.

## Assumptions

No sample-accuracy or positivity assumptions are needed. The scale is the existing $B=10^{180}$, the polynomial has degrees $0$ through $64$, and the curvature coefficient range is $0$ through $128$.

## Proof Sketch

If $P_j=A_j/B$, differentiation gives $P'_j=(j+1)A_{j+1}/B$ and $P''_j=(j+1)(j+2)A_{j+2}/B$. Consequently every coefficient of $P'^2-PP''$ is an integer convolution divided by $B^2$. Since $B$ is positive, absolute values and finite sums commute with division by $B$ or $B^2$. Substitution of these exact identities into the dense checker proves the equivalence. All recorded bounds, error allowances and comparison directions are unchanged. The rewrite avoids repeated rational normalization inside each convolution sum.

## Lean Artifacts

- File: `SourcePanelIntegerFull.lean`.
- Main theorem: `sourcePanelCheck_iff_integer`.
- Supporting identities: `ratDensePanelCoeff_eq_int`, `ratDensePanelD1_eq_int`, `ratDensePanelD2_eq_int`, `ratDensePanelCurvature_eq_int`, `ratDenseNorm_eq_int`, `ratDenseNorm_panel_eq_int`, `ratDenseNorm_d1_eq_int`, `ratDenseNorm_d2_eq_int`, `ratDenseNorm_off_eq_int`.

This is an exact arithmetic equivalence, not by itself a source-sample certificate.
