# Quantitative two-exponential tail curvature

## Statement

`tail_function_curvature_positive` proves a function-level version of Section 4, equations (7)–(11), of `reciprocal_xi_tail_logconcavity.md`, beginning **after** the three analytic remainder bounds have been established.

Write
$$
v(x)=Ae^{-ax}-Be^{-bx},\qquad H(g)(x)=g'(x)^2-g(x)g''(x),\qquad \Delta=b-a.
$$
Given the assumptions below, the theorem proves $H(g)(x)>0$. Its proof derives, rather than assumes, the complete error estimate
$$
\begin{aligned}
|H(g)(x)-AB\Delta^2e^{-(a+b)x}|
\le {}&A(D_2+2aD_1+a^2D_0)e^{-(a+R)x}\\
 &+B(D_2+2bD_1+b^2D_0)e^{-(b+R)x}\\
 &+(D_1^2+D_0D_2)e^{-2Rx}.
\end{aligned}
$$
`twoExponential_curvature_ge_half_of_majorant` also supplies the quantitative lower bound $H(g)(x)\ge AB\Delta^2e^{-(a+b)x}/2$ whenever the explicit right-hand side is at most half the leading curvature. The logarithmic-threshold theorems establish precisely that condition.

## Exact assumptions

The function-level theorem uses real parameters satisfying:

- $C>0$ and $0<a<b<R$.
- $A\ge Cb$ and $B\ge Ca$; these imply $A,B>0$.
- $D_0>0$, $D_1\ge0$, and $D_2>0$. The source's positive remainder constants meet these stronger-than-necessary strictness conditions.
- `HasDerivAt g g1 x` and `HasDerivAt (deriv g) g2 x`, identifying the two supplied jets with the actual first and second derivatives.
- The three analytic estimates $|g^{(j)}(x)-v^{(j)}(x)|\le D_je^{-Rx}$ for $j=0,1,2$.
- $x\ge X$, where the explicit constants and threshold are
$$
U_1=\frac{D_2+2aD_1+a^2D_0}{Ca\Delta^2},\quad
U_2=\frac{D_2+2bD_1+b^2D_0}{Cb\Delta^2},\quad
U_3=\frac{D_1^2+D_0D_2}{C^2ab\Delta^2},
$$
$$
X=\max\left(0,\frac{\log(6U_1)}{R-b},\frac{\log(6U_2)}{R-a},
\frac{\log(6U_3)}{2R-a-b}\right).
$$
`tailThreshold_nonneg` proves $X\ge0$, so the threshold premise already implies $x\ge0$.

No premise asserts the desired sign of $H(g)$, or assumes an error bound directly on $H(g)$.

## Proof Sketch

The general nonuniform jet bound expands the change in curvature into five products. Applying the triangle inequality bounds these by the separate value, first-derivative, and second-derivative errors. For the two-exponential approximation, the zeroth, first, and second jets have bounds $Ae^{-ax}+Be^{-bx}$, $aAe^{-ax}+bBe^{-bx}$, and $a^2Ae^{-ax}+b^2Be^{-bx}$. Substitution and exact exponential identities give the displayed full error majorant.

The imported curvature identity gives $H(v)(x)=AB\Delta^2e^{-(a+b)x}$. The inequalities $A\ge Cb$ and $B\ge Ca$ imply the three coefficient comparisons for the specified $U_1,U_2,U_3$; these comparisons are proved in Lean, not left as additional final assumptions. Factoring out the leading curvature therefore bounds the relative error by
$$
U_1e^{-(R-b)x}+U_2e^{-(R-a)x}+U_3e^{-(2R-a-b)x}.
$$
All three rates are positive. Exponentiating each logarithmic threshold shows that its corresponding summand is at most $1/6$, so their sum is at most $1/2$. Subtracting this error from the strictly positive leading term leaves at least half the leading curvature. The function-level corollary substitutes the derivative identities supplied by `HasDerivAt`.

## Remaining analytic obligations

This module does **not** prove the convolution identity $g=(l_a*l_b)*\mu$, differentiation under that probability integral, the exponential-moment bound, or the three analytic remainder estimates themselves. It does not establish the pole/moment inputs or identify $g$ with the actual reciprocal-Xi density. Those obligations are necessary before applying this conditional theorem to the target density. No mathematical novelty or unconditional formalization of the full Xi theorem is claimed here.

## Lean artifacts and main APIs

- Namespace: `ReciprocalXi`.
- File: `TailBoundsFull.lean`.
- Definitions: `tailCurvatureMajorant`, `tailThreshold`, `tailU1`, `tailU2`, `tailU3`.
- Error propagation: `curvatureJet_nonuniform_error_bound`, `twoExponential_jet_error_bound`.
- Quantitative margin: `twoExponential_curvature_ge_half_of_majorant`.
- Threshold: `expTailTerm_le_one_sixth`, `relative_tail_sum_le_half`, `tail_majorant_le_relative`, `tail_majorant_le_half_of_threshold`, `tailThreshold_nonneg`.
- Coefficient reduction: `tail_coefficient_bounds_of_pole_lower_bounds`.
- Positive curvature: `twoExponential_tail_curvature_positive`, `twoExponential_tail_curvature_positive_of_pole_bounds`, `tail_function_curvature_positive`.

`lake env lean ProofWorkspace/Final/TailBoundsFull.lean` passed without warnings in the pinned Lean 4.28.0/Mathlib environment. Full-project verification, theorem-axiom audit, and run status are recorded by the enclosing pipeline run.
