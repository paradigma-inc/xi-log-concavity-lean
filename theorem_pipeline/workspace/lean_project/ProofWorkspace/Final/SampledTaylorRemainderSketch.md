# Degree-64 Taylor remainder and its first two derivatives

## Statement

Let
$$A(u)=\operatorname{sampledCosineQuadrature}(c+u/200,1/40,p,13600,v),\qquad
\alpha_n=\frac{A^{(n)}(0)}{n!},\qquad
P_{64}(u)=\sum_{n=0}^{64}\alpha_nu^n.$$
For every real center $c$, real $x$ with $|x|\le1$, and $j\in\{0,1,2\}$, the module proves
$$|A^{(j)}(x)-P_{64}^{(j)}(x)|\le
\tau=e^{66}(1/50)^{65}\frac{66^2}{(1-1/50)^3}.$$
The derivatives are with respect to the normalized displacement $u$, not the physical variable $c+u/200$.

## Assumptions

The normalizer satisfies $p\ge3$. The sample values satisfy, explicitly for every $0\le k\le13600$,
$$|\operatorname{Re}\phi(k/40)-v_k|\le2\cdot10^{-120},$$
where $\phi$ is the actual reciprocal-Xi transform. No accuracy assumption on $p-\pi$ and no restriction on $c$ are needed for this Taylor-only result. The coefficients are actual Taylor coefficients, not the source's rounded coefficient table.

## Proof Sketch

The previously proved reciprocal-transform and cosine estimates bound the sampled quadrature by
$$(1+13600\cdot43046722)/120<5\cdot10^9$$
throughout the physical strip $|\operatorname{Im}z|\le1/4$. After normalization this is a bound on the radius-$50$ disk. Cauchy's estimate therefore gives $|\alpha_n|\le5\cdot10^9/50^n$. The entire Taylor expansion and its geometric majorant show that the actual remainder $A-P_{64}$ is bounded on $|u|\le3/2$ by
$$E=5\cdot10^9(3/100)^{65}/(1-3/100).$$
A circle of radius $1/2$ about any real $|x|\le1$ lies in this disk. Cauchy's derivative estimate bounds the first three jets of the entire remainder by $j!2^jE\le8E$. Finally, exact rational arithmetic and $e^{66}\ge2^{66}$ prove $8E\le\tau$, retaining the frozen source allowance unchanged. Entire differentiability justifies identifying derivatives of the remainder with the corresponding differences of derivatives.

## Lean Artifacts

- Proof: `SampledTaylorRemainderFull.lean` in `ProofWorkspace/Final/`.
- Main declarations: `sampledTaylorPolynomial64`, `sourceTaylorTau`, `sampledTaylorRemainder64_jet_le`, `sampledTaylorPolynomial64_jet_error_le`.
- This does not discharge the still-explicit sample-error hypotheses or certify rounded polynomial coefficients.


