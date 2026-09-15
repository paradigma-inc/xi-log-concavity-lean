# Conditional assembly for the actual reciprocal-Xi density

## Statement

`density_curvature_positive_of_enclosures` proves

$$
\Lambda'(x)^2-\Lambda(x)\Lambda''(x)>0\qquad(x\in\mathbb R)
$$

**conditional on** the two explicit evidence structures
`DensityCompactEnclosures` and `DensityTailEnclosures`. No inhabitant of either
structure has been constructed. The result is therefore not the completed
reciprocal-Xi theorem.

With the additional assumption that the actual density is positive,
`density_strictConcaveOn_log_of_enclosures` gives strict log
concavity and `density_pf2_minor_pos_of_enclosures` gives every strictly ordered
order-two translation determinant.

## Remaining assumptions, stated precisely

The compact evidence supplies $318$ polynomials, nonnegative errors, and bounds
on the actual density and its first two derivatives in normalized coordinates.
It also states that the three recorded constant/coefficient/error numbers are
genuine enclosures for those polynomials and errors. The positive numerical
margin is not assumed: it has been checked for every row in Lean.

The tail evidence supplies $A,B,C,a,b,R,D_0,D_1,D_2$, with
$C>0$, $0<a<b<R$, $A\ge Cb$, $B\ge Ca$, $D_0,D_2>0$ and $D_1\ge0$.
It supplies the three exponential derivative-remainder bounds for the actual
density relative to $Ae^{-ax}-Be^{-bx}$, and proves that the resulting explicit
logarithmic threshold is at most $3.18$.

Neither structure assumes curvature positivity. They package the genuinely
unproved analytic enclosure obligations; renaming them does not discharge them.
Positivity remains a separate explicit input to the log-concavity and determinant
corollaries. Twice differentiability is no longer assumed: `XiFourierFull`
proves the actual density is smooth from actual Xi/Gamma/theta bounds.

## Proof Sketch

The checked finite margins and supplied compact enclosures imply positive
curvature on every normalized panel. Exact geometry and scaling give the result
on $[0,3.18]$. The tail remainder theorem makes the curvature error at most half
the positive two-exponential leading curvature beyond its logarithmic threshold.
The overlap premise joins these intervals on the nonnegative half-line. The
already proved evenness of the actual curvature reflects the conclusion to the
negative half-line. For a positive twice differentiable density, the second
logarithmic derivative is the negative curvature divided by $\Lambda^2$;
strict log concavity and strict order-two determinant positivity then follow
from the previously checked derivative reductions.

## Lean Artifacts

File: `DensityConditionalFull.lean` in `ProofWorkspace/Final`.

Principal theorems: `ReciprocalXi.density_curvature_positive_of_enclosures`,
`ReciprocalXi.density_strictConcaveOn_log_of_enclosures`, and
`ReciprocalXi.density_pf2_minor_pos_of_enclosures`.

## Full-target status

Incomplete. The next work is constructing the two evidence structures from the
actual Xi/Fourier/convolution estimates and establishing positivity. Actual
Fourier integrability and density regularity have now been proved.
No claim about RH or novelty follows from this conditional assembly.
