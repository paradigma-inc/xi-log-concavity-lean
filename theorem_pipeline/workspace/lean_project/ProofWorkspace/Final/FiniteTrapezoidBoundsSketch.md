# Finite truncation of the actual reciprocal-Xi Fourier grid

## Statement

Write $\varphi(u)$ for `reciprocalTransform u` and $G(z)$ for the actual entire inverse Fourier density `complexDensity z`. For $h>0$ and a natural number $K$, define

$$
T_{h,K}(z)=\frac{h}{2\pi}\sum_{n=-K}^{K}\varphi(hn)e^{-izhn},
\qquad
T_h(z)=\frac{h}{2\pi}\sum_{n\in\mathbb Z}\varphi(hn)e^{-izhn}.
$$

Both cutoff endpoints are retained; the first omitted indices are $\pm(K+1)$. The theorem `infiniteTrapezoid_sub_finite_norm_le` proves, for $hK\ge340$, $|\operatorname{Im}z|\le q<4/5$,

$$
|T_h(z)-T_{h,K}(z)|\le
\frac{h}{\pi}\frac{e^{-200+qhK}}{e^{(4/5-q)h}-1}.
$$

At the concrete mesh and cutoff, `infiniteTrapezoid_sub_finite_grid_lt` proves

$$
|T_{1/40}(z)-T_{1/40,13600}(z)|<\frac{1}{2\cdot10^{85}}
\qquad (|\operatorname{Im}z|\le1/100).
$$

Combining this cutoff estimate with the actual Poisson-alias estimate already proved in `QuadratureBudgetFull`, `finiteTrapezoid_error_grid_lt` gives

$$
|T_{1/40,13600}(z)-G(z)|<\frac{3}{4\cdot10^{85}}
\qquad
(|\operatorname{Re}z|\le4,\ |\operatorname{Im}z|\le1/100).
$$

## Assumptions

The general bound requires only $h>0$, $K\in\mathbb N$, $hK\ge340$, and $|\operatorname{Im}z|\le q<4/5$. The concrete cutoff bound requires only $|\operatorname{Im}z|\le1/100$. The combined numerical bound additionally requires $|\operatorname{Re}z|\le4$. All summability, transform-tail, alias, and exponential estimates are proved for the actual functions; no sampled values or desired error conclusions are assumed.

## Proof Sketch

The previously established actual tail estimate is
$|\varphi(u)|\le e^{-200}e^{-(4/5)(|u|-340)}$ for $|u|\ge340$. Since $|e^{-izu}|\le e^{q|u|}$, each omitted grid term is at most

$$
e^{-200+qhK}e^{-(4/5-q)h(|n|-K)}.
$$

Here the replacement of $340$ by $hK$ only enlarges the majorant. The exact two-sided geometric sum over $|n|>K$ is $2/(e^{(4/5-q)h}-1)$. Subtracting the finite supported head from the proved absolutely convergent actual series identifies precisely the omitted tail. Its norm is bounded by that geometric majorant, and multiplication by $h/(2\pi)$ gives the stated cutoff bound.

For $h=1/40$, $K=13600$, $q=1/100$, the exponential numerator is $e^{-983/5}$ and the denominator is $e^{79/4000}-1$. The elementary bounds $\pi>3$ and $e^x\ge1+x$ show that the prefactor is at most $100/237$. An exact rational Taylor enclosure proves $10\le e^{231/100}$; raising this inequality to the 85th power and using $85(231/100)<983/5$ gives $e^{-983/5}<10^{-85}$. Since $100/237<1/2$, the concrete cutoff budget follows. Finally, the triangle inequality adds the previously proved alias error below $1/(4\cdot10^{85})$ to the cutoff error below $1/(2\cdot10^{85})$.

## Scope

This is an actual finite-quadrature error theorem, not a numerical evaluation of its retained sum. The 27,201 retained values $\varphi(n/40)$ and their complex exponential factors still need certified finite enclosures before a supplied numerical approximation can be connected to $G$. The final quarter of a $10^{-85}$ budget remains available for those finite-value and rounding errors. No density positivity or curvature assertion follows from this module alone.

## Lean Artifacts

- `ProofWorkspace/Final/FiniteTrapezoidBoundsFull.lean`
- Definitions: `ReciprocalXi.finiteTrapezoid`.
- Theorems: `int_mem_symmetric_Icc_iff`, `hasSum_int_cutoff_geometric`, `hasSum_int_cutoff_exp`, `quadratureInput_cutoff_norm_le`, `infiniteTrapezoid_sub_finite_norm_le`, `finiteTrapezoid_total_error_le`, `exp_neg_983_fifths_lt_ten_pow_neg85`, `infiniteTrapezoid_sub_finite_grid_lt`, `finiteTrapezoid_error_grid_lt` (all in namespace `ReciprocalXi`).
- Source: the existing reciprocal-Xi compact quadrature material and analytic run prompt `theorem_pipeline/workspace/prompts/complex_density_contours.txt`.
