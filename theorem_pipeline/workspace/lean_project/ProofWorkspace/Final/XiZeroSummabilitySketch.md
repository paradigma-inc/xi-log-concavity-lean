# Reciprocal-square summability over all actual zeros

## Statement

The zeros of the actual $F(z)=\xi(1/2+iz/2)/4$, counted with their analytic
multiplicities $m_z$, satisfy
$$\sum_{F(z)=0} \frac{m_z}{|z|^2}<\infty.$$
The unweighted reciprocal-square sum also converges. No RH, finite zero
list, or zero-counting assumption is required.

## Assumptions

The only objects are the existing actual function and its actual zeros.
Jensen's formula, actual global growth, $F(0)\ne0$, finite multiplicities,
and the zero-free unit disk are proved in the preceding modules.

## Proof Sketch

The factorial growth bound obeys
$\log((n+2)^2n!)\le(n+2)\log(n+2)$. Substituting dyadic radii in the
proved Jensen estimate gives
$$N_F(2^k)\le4\cdot2^k(k+2)+C,
\qquad C=\frac{|\log|F(0)||}{\log2}\ge0.$$
A shell $2^k\le|z|<2^{k+1}$ contributes at most
$8(k+3)2^{-k}+C4^{-k}$ to the weighted reciprocal-square sum. This majorant
is summable. Every actual zero has norm greater than one, so belongs to one
such shell. Partition an arbitrary finite set of zeros by shell and bound
its sum by the total majorant; bounded nonnegative finite sums imply
summability on the complete zero set. Positive integral multiplicity bounds
the unweighted series by the weighted one.

Summability is a necessary product input; the equality of a paired product
with the actual $F$ is not claimed here.

## Lean Artifacts

- File: `XiZeroSummabilityFull.lean`
- Main theorems: `F_zeroCount_dyadic`, `F_finite_shell_sum_le`,
  `summable_F_zero_order_div_norm_sq`, `summable_F_zero_inv_norm_sq`.
