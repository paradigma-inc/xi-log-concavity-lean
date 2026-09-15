# Exact rational eta-integral enclosures

## Statement

For each positive rational $s$, `ratEtaLower` and `ratEtaUpper` are exact
rational expressions enclosing the actual eta integral
$$
\eta_I(s)=\frac{1}{\Gamma(s)}\int_0^\infty
  \frac{t^{s-1}e^{-t}}{1+e^{-t}}\,dt.
$$
The endpoints use finitely many verified real-power enclosures and the
previously proved analytic Euler-acceleration remainder. No real-valued
summand enclosures are assumed.

The `ratEtaNatLower` and `ratEtaNatUpper` variant uses the exact dyadic
integer-base power evaluator. It encloses the same actual integral with
the same analytic truncation error, while evaluating logarithms only at
$2$ and mantissas in $[1,2)$.

## Assumptions

The exponent parameter $s$ is a positive rational. The Euler truncation
order $N$ and logarithm order are arbitrary natural numbers; the exponential
range-reduction factor and exponential order are positive natural numbers.
For every integer $j<N$, both computed rational logarithmic-product
endpoints for $(j+1)^{-s}$, divided by the range-reduction factor, have
absolute value at most $1$. These are explicit, decidable rational
preconditions, not accuracy assumptions about transcendental values.

For the efficient integer-base variant, the corresponding range checks
use the dyadic logarithmic-product endpoints with the computed mantissa
$(j+1)/2^{\lfloor\log_2(j+1)\rfloor}$. The base decomposition and mantissa
range are proved in the integer-power module; neither is an extra
assumption.

## Proof Sketch

Write the exact rational signed Euler coefficient as
$$
c_{N,j}=(-1)^j w_{N,j},\qquad
w_{N,j}=2^{-N}\sum_{j<k\le N}\binom Nk.
$$
The previously proved rational real-power evaluator supplies endpoints
$p_j^-\le(j+1)^{-s}\le p_j^+$. Define the corresponding signed summand
endpoints by
$$
\ell_j=\min(c_{N,j}p_j^-,c_{N,j}p_j^+),\qquad
u_j=\max(c_{N,j}p_j^-,c_{N,j}p_j^+).
$$
Multiplication preserves the power interval when $c_{N,j}\ge0$ and
reverses it when $c_{N,j}\le0$. Thus the minimum and maximum provide a
sound interval for every alternating summand. The exact rational weight
casts to the weight in the actual Euler approximation, and the identity
$(j+1)^{-s}=1/(j+1)^s$ identifies the summands without changing the
mathematical function being approximated.

Summing the finite inequalities bounds the actual Euler approximation
$E_N(s)$ between $\sum_{j<N}\ell_j$ and $\sum_{j<N}u_j$. The independently
proved integral acceleration theorem gives
$$
0\le\eta_I(s)-E_N(s)\le2^{-N}.
$$
Consequently the lower endpoint is $\sum\ell_j$, while the upper endpoint
is $\sum u_j+2^{-N}$. In particular the analytic tail is added only to the
upper endpoint; it is not an unsupported symmetric numerical tolerance.
The exact total width is
$$
\sum_{j<N}(u_j-\ell_j)+2^{-N},
$$
separating finite arithmetic enclosure width from analytic truncation.

The efficient variant repeats precisely this finite interval argument
with the proved integer-base dyadic power endpoints in place of the direct
power endpoints. It does not change the weights, analytic integral,
alternating signs, or remainder. Its width has the same exact
finite-width-plus-$2^{-N}$ decomposition.

## Scope

This proves a rational evaluator for the actual integral at every positive
rational argument satisfying the explicit range checks, including arguments
below $1$. Actual eta/zeta analytic continuation was proved in the imported
analytic modules, but no retained Xi grid node is claimed to have been
numerically evaluated here. No table of transcendental constants, custom
axiom, or unchecked native computation is used. The full curvature target
is still a separate obligation.

## Lean Artifacts

- `RationalEtaBoundsFull.lean`
- Definitions: `ratEtaCoefficient`, `ratEtaTermLower`, `ratEtaTermUpper`,
  `ratEtaLower`, `ratEtaUpper`, `ratEtaNatTermLower`, `ratEtaNatTermUpper`,
  `ratEtaNatLower`, `ratEtaNatUpper`.
- Theorems: `ratEtaCoefficient_cast`, `ratEtaTerm_enclosure`,
  `ratEtaIntegral_enclosure`, `ratEtaIntegral_width`, `ratEtaNatTerm_enclosure`,
  `ratEtaNatIntegral_enclosure`, `ratEtaNatIntegral_width`.

All seven theorems compiled in the pinned Lean 4.28.0/mathlib project, and
their axiom checks contained only `propext`, `Classical.choice`, and
`Quot.sound`.
