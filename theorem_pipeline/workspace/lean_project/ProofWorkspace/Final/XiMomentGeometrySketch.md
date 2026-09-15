# Actual zero gap and reciprocal-power geometry

## Statement

For the actual function $F(z)=\xi(1/2+iz/2)/4$, every zero satisfies
$|\Re z|>7$. For $\Re a>0$ and $|\Im a|\le1$, every natural power satisfies
$$\Re((a^{-1})^n)\ge\frac{1-n^2/(2(\Re a)^2)}{\|a\|^n}.$$

## Assumptions

The actual-zero gap assumes only $F(z)=0$. The general inverse-power
estimate assumes the displayed geometric conditions, not that $a$ is
a zero. Neither theorem assumes RH, a complete zero list, simplicity,
nor numerical sample enclosures.

## Proof Sketch

The existing actual Mellin formula bounds the pole-removed completed
zeta by $4e^{-\pi}/\pi\le1/15$. The elementary positive exponential
sum gives $e^3\ge20$. If $|\Re z|\le7$, the known actual zero strip
places $s=1/2+iz/2$ in $0\le\Re s\le1$ with $|\Im s|\le7/2$.
Thus $|s(s-1)\operatorname{completedZeta}_0(s)|\le53/60<1$,
contradicting the actual formula for $F(z)=0$.

For the angular bound, normalize $u=a/\|a\|$. An induction gives
$|u^n-1|\le n|u-1|$. The exact unit-circle norm-square identity then
bounds $1-\Re(u^n)$ by $n^2(1-\Re u)$. The strip condition implies
$1-\Re a/\|a\|\le1/(2(\Re a)^2)$ by real algebra. Divide by
$\|a\|^n$ and use the exact real-part formula for complex inversion.

## Lean Artifacts

- File: `XiMomentGeometryFull.lean`
- Theorems: `exp_three_ge_twenty`, `thetaMellin_bound_le_one_fifteen`,
  `F_zero_abs_re_gt_seven`, `complex_unit_power_sub_one_norm_le`,
  `complex_unit_power_re_lower`, `complex_normalized_re_deficit`,
  `complex_inverse_power_re_lower`.

