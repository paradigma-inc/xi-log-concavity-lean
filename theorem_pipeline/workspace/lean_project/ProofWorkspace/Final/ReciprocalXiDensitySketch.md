# Reciprocal-Xi density: smoothness, probability normalization and strict log-concavity

## Statement and scope

For the standard completed xi function, define
$$
F(z)=\frac14\xi\!\left(\frac12+\frac{iz}{2}\right),\qquad
\phi(u)=\frac{F(0)}{F(iu)},\qquad
\Lambda(x)=\frac1{2\pi}\operatorname{Re}\int_{\mathbb R}\phi(u)e^{-ixu}\,du.
$$
The theorem `ReciprocalXi.density_full_conclusions` states, with no theorem
hypotheses, that this actual density is smooth, even, integrable and everywhere
positive, has integral one, and satisfies
$$
\Lambda'(x)^2-\Lambda(x)\Lambda''(x)>0\qquad(x\in\mathbb R).
$$
Its logarithm is strictly concave on the whole real line. In particular,
$$
\Lambda(x_1-y_1)\Lambda(x_2-y_2)-\Lambda(x_1-y_2)\Lambda(x_2-y_1)>0
\quad(x_1<x_2,\ y_1<y_2).
$$
These are order-one and order-two translation-minor conclusions (PF2).
They make no RH, PF-infinity or novelty claim.

## Assumptions

There are no additional theorem hypotheses. The actual xi and inverse-Fourier
definitions are used, not an abstract density or a function fitted to these
inequalities. The six original endpoint signs, all 13,601 source bounds at
the original $2\cdot10^{-120}$ error, and all 318 original compact-panel checks
are supplied by checked Lean theorems. Original constants and margins are
unchanged.

## Proof sketch

Actual xi estimates give integrability of every polynomially weighted
reciprocal transform, so Fourier differentiation proves smoothness, while
reflection of the integral proves evenness. The zero-location argument uses
the paired product over actual zero occurrences, counting multiplicity.
Certified first and second moments exclude occurrences with real coordinate
at most 24. Exact extraction from 33 source logarithms bounds the scaled
sixteenth-moment residual below $7/10$ after subtracting one occurrence from
each of three original intervals. Their endpoint signs give those occurrences
by the intermediate value theorem. Any further occurrence with real coordinate
at most 60 would contribute more than $7/10$, giving a contradiction. This
establishes the required completeness and simplicity without assuming RH or
a preclassified list of zeros.

After removing the first two real factors, the residual heat trace has a
proved positive lower bound. Its probability law convolves with the normalized
two-Laplace kernel to give the actual density. This representation yields
positivity, integrability and unit mass. The same zero certificate and the
certified value at $F(48)$ provide the tail enclosure and overlap at 3.18.

On the compact interval, rational samples approximate the actual reciprocal
transform with the original certified error. For each original panel, 54
checked transitions identify the proposed coefficient vector with the full
13,601-sample coefficient stream. The checked integer margins, Fourier
approximation and derivative error estimates yield the compact curvature
enclosure. Compact and tail enclosures cover the nonnegative half-line, and
evenness covers the rest. Positive curvature gives strict concavity of the
logarithm, hence the ordered positive two-by-two determinants. The final
theorem assembles these conclusions for the same actual density.

## Lean declarations

- `originalLowRootSigns_checked`
- `density_probability_normalization`
- `sourcePanelStreams_checked`
- `sourceDensityCompactEnclosures` (proof-valued definition)
- `density_global_conclusions`
- `density_full_conclusions`

All six declarations are included in the final direct axiom audit, including
the proof-valued definition.

## Files and verification

Proof: `ProofWorkspace/Final/ReciprocalXiDensityFull.lean`.
Normalized source: `theorem_pipeline/workspace/contexts/reciprocal_xi_global_logconcavity.md`.
The unchanged assembly body first passed Lean in
`theorem_pipeline/logs/91a4_full_assembly_scratch.log` (exit 0).
Final-module compilation, direct axiom audit, cumulative verification and
independent Astra xhigh review are recorded in the final verification report.
The earlier interim source reviews are not a substitute for that final review.
