# Curvature perturbation and the two-exponential tail model

## Statement

The Lean definition `ReciprocalXi.curvatureJet` is
$$H(v,v_1,v_2)=v_1^2-vv_2.$$
The theorem `curvatureJet_perturbation_bound` proves that, whenever $e,N_0,N_1,N_2\ge0$, $|p_j|\le N_j$, and $|r_j|\le e$ for $j=0,1,2$,
$$
|H(p_0+r_0,p_1+r_1,p_2+r_2)-H(p_0,p_1,p_2)|
\le e(2N_1+N_0+N_2)+2e^2.
$$
`curvatureJet_positive_of_margin` consequently proves strict positive curvature whenever the unperturbed curvature is strictly larger than this error allowance.

For the actual real function $v(x)=Ae^{-ax}-Be^{-bx}$, `twoExponential_curvature` proves
$$
H(v(x),v'(x),v''(x))=AB(b-a)^2e^{-(a+b)x}.
$$
The file proves both derivative formulas; `twoExponential_curvature_pos` proves strict positivity for positive $A,B$ when $a\ne b$. Its algebraic version `twoExponentialJet_curvature_pos` also takes positive exponential factors as explicit scalar hypotheses.

## Assumptions and scope

These are complete proofs of specific conditional and algebraic components, not a formalization of the reciprocal-Xi density theorem. In particular, the module does **not** assume or establish that sampled numerical values control derivatives. The estimates on all three components are explicit hypotheses. Establishing these hypotheses for the density, validating its Fourier approximation and every directed-arithmetic certificate, and proving the analytic tail-remainder bounds are separate obligations.

The first part corresponds to Section 5 of `evidence/results/reciprocal_xi_global_logconcavity.md`; the second corresponds to Section 4 of `reciprocal_xi_tail_logconcavity.md`.

## Proof Sketch

Expanding the difference of curvature numerators gives
$$
2p_1r_1+r_1^2-p_0r_2-r_0p_2-r_0r_2.
$$
The triangle inequality and the stated bounds control its five terms by $2N_1e$, $e^2$, $N_0e$, $eN_2$, and $e^2$. Summing gives the error allowance. A curvature margin larger than that allowance remains strictly positive after perturbation.

For the two-exponential model, differentiation gives $v'=-aAe^{-ax}+bBe^{-bx}$ and $v''=a^2Ae^{-ax}-b^2Be^{-bx}$. Upon substitution, the terms proportional to $A^2$ and $B^2$ cancel, leaving $AB(b-a)^2e^{-(a+b)x}$. The coefficient is positive for positive $A,B$ and distinct rates.

## Lean Artifacts

- File: `CurvatureBoundsFull.lean`
- Namespace: `ReciprocalXi`
- Main theorems: `curvatureJet_perturbation_bound`, `curvatureJet_positive_of_margin`, `twoExponentialJet_curvature`, `twoExponentialJet_curvature_pos`, `twoExponential_curvature`, `twoExponential_curvature_pos`.

## Local verification

`lake env lean ProofWorkspace/Final/CurvatureBoundsFull.lean` passed without warnings in Lean 4.28.0 against the pinned Mathlib checkout. Temporary `#print axioms` checks of the two main perturbation theorems and the two actual-function curvature theorems reported only Mathlib's standard foundations: `propext`, `Classical.choice`, and `Quot.sound`. There are no additional axioms or unresolved proof placeholders in this module. Full project verification and its durable log are recorded by the enclosing pipeline run.
