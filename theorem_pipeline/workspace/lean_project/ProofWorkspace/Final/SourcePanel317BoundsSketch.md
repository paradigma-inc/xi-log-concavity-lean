# Recorded curvature checks for panel 317

## Statement

`sourcePanel317Candidate_passes` verifies the original three recorded inequalities for the explicit $65$-coefficient integer vector on panel $317$, centered at $3.175$. The vector is decoded at scale $10^{180}$ and defines a degree-at-most-$64$ polynomial $P$ in normalized coordinates. The checks bound the constant coefficient of $P'^2-PP''$ from below, the absolute sum of its remaining coefficients from above, and the analytic jet-error contribution from above.

## Assumptions and scope

The finite inequalities have no assumptions. Their margins, coefficient-rounding allowance and analytic jet-error allowance are the original ones. This module does not establish that the vector is the output of the source stream, nor that all source samples approximate the actual reciprocal-Xi transform. Those two obligations are necessary before these inequalities imply a fact about the actual density.

## Proof Sketch

The previously proved dense-coefficient identity replaces polynomial support operations by finite coefficient sums without changing any bound. A further exact common-denominator identity computes the convolution as integers and divides only after summation. Reduction in Lean's kernel checks the length and all three inequalities for the displayed integer vector. The earlier rational-only scratch check passed the same inequalities independently of this execution rewrite. No floating-point oracle or native decision shortcut is used.

## Lean Artifacts

- File: `SourcePanel317BoundsFull.lean`
- Theorem: `sourcePanel317Candidate_passes`.
