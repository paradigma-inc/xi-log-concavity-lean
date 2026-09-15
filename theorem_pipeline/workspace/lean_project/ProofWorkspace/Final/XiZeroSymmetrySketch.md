# Conjugate and antipodal symmetry of actual Xi zeros

## Statement

The actual normalized entire function satisfies $F(\overline z)=\overline{F(z)}$ everywhere. Hence its zero set is closed under conjugation; the existing evenness already gives closure under negation. Analytic multiplicity is unchanged by either operation.

## Assumptions

Global conjugation and multiplicity identities have no zero-location or numerical hypotheses. `F_zero_conj` assumes only $F(z)=0$. Intermediate theta-integrand identities require the positive real integration variable; the local Xi reflection identity has the displayed central-strip bounds.

## Proof Sketch

For positive real bases, complex powers commute with conjugation. The actual theta/Mellin integral therefore commutes with conjugation, giving Xi reflection on the central strip. The functional equation converts this into reflection of $F$ on a neighborhood of zero. The conjugate-reflected function is entire, and the identity theorem extends equality to the whole plane. To compare multiplicities, reflect the local factorization into a vanishing power times an analytic nonzero factor; finite analytic order was established in the zero-geometry module. Composition with negation has nonzero derivative and preserves analytic order, while evenness identifies the composed function with $F$ itself.

## Remaining Scope

Symmetry and multiplicity preservation do not establish finite-height completeness, explicit counting, reciprocal-square summability, or the paired infinite-product identity.

## Lean Artifacts

- File: `XiZeroSymmetryFull.lean`.
- Main theorems: `F_conj`, `F_zero_conj`, `F_order_neg`, `F_orderNat_neg`, `F_orderNat_conj`.
- Supporting theorems: `thetaMellinIntegrand_conj`, `thetaMellinIntegral_conj`, `completedRiemannZeta₀_conj_wide`, `xi_conj_central`, `F_conj_of_im_bound`, `analyticAt_conj_reflection`.
