# Counting the remaining actual zero occurrences

## Statement

Given three distinct actual positive-half-plane occurrences $a,b,c$
whose roots are real and positive and bounded above by the three
original upper interval endpoints, every other occurrence has real
part greater than 60. No simplicity or completeness hypothesis is used.
A separate lemma proves analytic order one when an occurrence is the
unique occurrence at its root value.

## Assumptions

The three actual real root occurrences, their distinctness, positivity
and their stated upper bounds are explicit premises. Their existence
is not proved in this module; the remaining original fine endpoint signs
and intermediate-value argument must supply it. All moment, angular,
source and residual numerical bounds used here are already proved.

## Proof Sketch

Every summand of the actual sixteenth moment is nonnegative. For an
occurrence with real part $24<A\le55$, its scaled contribution is at least
$$60^{32}\Re(a^{-32})\ge\frac19(3600/3026)^{16}>7/10.$$
For $55<A\le60$, use instead
$$60^{32}\Re(a^{-32})\ge(1-512/3025)(3600/3601)^{16}>7/10.$$
These estimates follow from the actual imaginary strip, the proved
angular inequality and monotonicity of positive inverse powers.

If a fourth distinct occurrence existed below 60, the sum of its
contribution and those of the three selected occurrences would not
exceed the full moment, by summability and nonnegativity.
For the real selected roots, subtracting the inverse powers of their
upper bounds gives a conservative residual upper bound. The certified
scaled residual is below $7/10$, contradicting the fourth contribution.
This finite-sum argument already counts multiplicities because the
index type consists of analytic-order occurrences, not distinct values.

Finally the full occurrence fiber at a root is equivalent to
$\operatorname{Fin}(\operatorname{analyticOrderNatAt} F a)$.
Uniqueness makes this finite type inject into the unit type, so its
cardinality is at most one. Actual zero order is positive, hence it is one.

## Lean Artifacts

- File: `XiMomentResidualFull.lean`.
- Counting theorem: `ReciprocalXi.F_three_real_occurrences_exhaust_below_sixty`.
- Multiplicity lemma: `ReciprocalXi.F_pairRoot_simple_of_unique_occurrence`.
- Contribution bound: `ReciprocalXi.F_pairMoment_sixteen_term_large_below_sixty`.
- Direct audit: `AuditXiMomentResidual.lean`, all five public lemmas.

This is a proved conditional counting step. Do not claim that the three
original roots exist, are simple, or exhaust the low zeros until their
existence and the uniqueness specialization have been supplied.
