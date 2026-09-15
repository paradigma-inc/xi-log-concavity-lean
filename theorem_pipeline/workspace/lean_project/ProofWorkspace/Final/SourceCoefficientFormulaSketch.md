# Exact source Taylor coefficients and trigonometric recurrence

## Statement

For arbitrary real $c,p$ and sample sequence $v$, define
$$
w_{j,k}=\frac{v_k}{40p}\begin{cases}1/2&k=0,\\1&k>0\end{cases}
\frac{(k/8000)^j}{j!}.
$$
Let $T_j(\theta)$ be $\cos\theta,-\sin\theta,-\cos\theta,\sin\theta$ when $j$ is congruent to $0,1,2,3$ modulo $4$, respectively. The actual normalized sampled-quadrature Taylor coefficient is
$$
a_j=\sum_{k=0}^{13600}w_{j,k}T_j(kc/40).
$$
`sampledTaylorCoefficient_source_formula` proves this for every $j$, as equality of the complex coefficient to the cast of the displayed real sum. `realSampledTaylorPolynomial_source_coeff` gives the coefficient of the actual real degree-$64$ polynomial for $j\le64$. The script-shaped `realSampledTaylorPolynomial_source_formula` first selects cosine for even $j$ and sine for odd $j$, sums, and then negates exactly when $j\bmod4\in\{1,2\}$.

The weights obey their source initialization and update $w_{j+1,k}=w_{j,k}(k/8000)/(j+1)$. The exact two-component recurrence initialized at $(c_0,s_0)=(1,0)$ and updated by
$$
c_{k+1}=c_k\cos\theta-s_k\sin\theta,\qquad
s_{k+1}=s_k\cos\theta+c_k\sin\theta
$$
equals $(\cos(k\theta),\sin(k\theta))$ at every index. Taking $\theta=c/40$ gives the angles in the source coefficient loop.

## Assumptions

These are exact identities, with no numerical sample, trigonometric approximation, positivity, or rounding-error hypotheses. The polynomial coefficient statement requires only $j\le64$; the coefficient and recurrence identities hold at every natural order/index. Division uses the usual Lean real-field convention, so the identities also hold at $p=0$, although the source uses its positive approximation to $\pi$.

## Proof Sketch

Rewrite the actual sampled quadrature as a single finite sum including $k=0$. Its constant term is exactly half-weighted. In the normalized coordinate, its $k$th cosine has argument $kc/40+(k/8000)z$, since the panel radius is $1/200$. Differentiating the finite sum and applying the affine chain rule supplies the factor $(k/8000)^j$. The four-cycle of cosine derivatives supplies $T_j$, and the Taylor normalization supplies $1/j!$. The zero-frequency term is handled by the same formula, including $0^0=1$ at order zero and vanishing at positive orders. Polynomial coefficient extraction retains exactly the orders $0$ through $64$. The weight update follows from the factorial recurrence. Finally, induction using the exact sine and cosine addition laws proves the trigonometric recurrence.

This identifies the unrounded mathematical quantities computed by `reproduction/scripts/certify_reciprocal_xi_compact_logconcavity.py`. It does not identify the script's rounded decimal recurrence with exact trigonometry, does not bound that rounding error, and does not check any of the 318 recorded curvature coefficient enclosures.

## Lean Artifacts

- File: `ProofWorkspace/Final/SourceCoefficientFormulaFull.lean`
- Theorems: `sourceCoefficientWeight_zero`, `sourceCoefficientWeight_succ`, `sampledTaylorCoefficient_source_formula`, `realSampledTaylorPolynomial_source_coeff`, `realSampledTaylorPolynomial_source_formula`, `sourceTrigRecurrence_eq`, `sourceTrigRecurrence_panel`.
- Exact source: `reproduction/scripts/certify_reciprocal_xi_compact_logconcavity.py`, especially its weight construction and coefficient loop.
- Normalized context: `theorem_pipeline/workspace/contexts/reciprocal_xi_global_logconcavity.md`.
