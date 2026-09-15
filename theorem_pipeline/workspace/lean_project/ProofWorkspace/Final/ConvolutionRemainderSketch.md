# Convolution tail remainder: formalized analytic step

Companion: `ConvolutionRemainderFull.lean`, namespace `ReciprocalXi`.
Source target: Section 4, equation (7), of `reciprocal_xi_tail_logconcavity.md`.

## Exact mathematical statement

Let μ be a positive measure on the real line. Let C,a,b be nonnegative,
a≤R and b≤R, and suppose `exp(R |y|)` is μ-integrable with integral at most M.
Define

$$
K(t)=C\,[b e^{-a|t|}-a e^{-b|t|}],\qquad
g(x)=\int K(x-y)\,d\mu(y),\qquad
m_r=\int e^{ry}\,d\mu(y).
$$

The central theorem `laplaceConvolution_actual_derivative_remainder` proves,
for every x≥0 and j∈{0,1,2},

$$
\left|g^{(j)}(x)-(-1)^j C
 [b a^j e^{-ax}m_a-a b^j e^{-bx}m_b]\right|
\le 2CM(b a^j+a b^j)e^{-Rx}.
$$

Here `g^(j)` is Lean's actual iterated `deriv`, not an independently supplied
jet. No derivative identity, remainder inequality, or curvature conclusion is
assumed. The weaker nonnegative parameter assumptions cover the source's
strict regime C>0 and 0<a<b<R.

## Proof Sketch

The right exponential derivative formula `rightExponentialJet` and its
reflected left counterpart combine into `twoLaplaceJet`; the zeroth jet is
exactly $K$. When $y\le x$, this kernel jet agrees with its extended right
exponential formula. When $y>x\ge0$, its absolute value is at most
$C(ba^j+ab^j)$, while the extended exponentials are bounded by
$e^{R(y-x)}$. The difference is therefore bounded by
$2C(ba^j+ab^j)e^{-Rx}e^{R|y|}$. This estimate follows directly from the
formulas, without assuming a remainder inequality.

The exponential moment supplies integrable dominating functions for both
terms. Integrating their pointwise difference proves the integral-jet
remainder for every natural $j$. Factoring
$e^{-a(x-y)}=e^{-ax}e^{ay}$ identifies the leading coefficients with the
moments $m_a,m_b$.

The kernel is twice differentiable because its left and right formulas
agree at zero through jet order two: the first derivative vanishes there
by cancellation, and the other two jets are even. A gluing argument handles
this common boundary. Dominated differentiation under the integral then
identifies the first and second derivatives of $g$ with their integral
jets, using a dominating function independent of the differentiation point.
In particular, the argument permits atoms in $\mu$; it does not require a
density or discard the point $x-y=0$. Substitution of these derivative
identities yields the stated actual-derivative remainder.

## Additional proved consequences

- `differentiable_laplaceConvolution` and
  `differentiable_deriv_laplaceConvolution` establish twice differentiability
  directly from the exponential moment.
- `twoLaplaceKernel_pos` proves K(t)>0 when C>0 and 0<a<b.
- `laplaceConvolution_pos` proves g(x)>0 if μ is a probability measure,
  with the required integrability derived from the same moment hypothesis.
- `exponentialMoment_one_le_of_even` proves m_a≥1 for an even probability
  measure. Evenness is stated as measure preservation by y↦−y; the proof
  integrates `exp(z)+exp(-z)≥2`. Consequently the source coefficients
  A=C*b*m_a and B=C*a*m_b have the lower bounds used by the tail comparison.

## Scope and remaining obligations

This module proves the analytic convolution step unconditionally from the
listed ordinary measure and moment hypotheses. It does not construct a
measure from the zeros of the actual regularized Xi function, identify its
Fourier density with g, or prove the required certified exponential moment
bound for that measure. Nor does it prove that the displayed K is itself the
convolution of two normalized Laplace densities at the source value of C.
Those are separate actual-Xi / representation obligations, not conclusions
silently inserted into this theorem's premises.

The source's tail curvature argument can now consume the derived actual
derivative remainders instead of assuming them. The compact interval
certificate's analytic enclosures remain a separate obligation.

The module uses no `sorry`, custom axioms, or `native_decide`.
