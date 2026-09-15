# From three certified low zeros to the actual density

## Statement and assumptions

For the actual reciprocal-Xi density, `density_global_conclusions_of_original_signs_and_compact` proves positivity, strictly positive curvature, strict log-concavity and strictly positive order-two translation minors. Its two explicit prerequisites are opposite actual signs at the six original low-root endpoints and `DensityCompactEnclosures` for the actual density. Neither prerequisite is asserted to be discharged by this module. All other analytic, root-counting, moment and tail premises are derived from existing proved results.

## Proof sketch

The moment-based certificate selects the first three real zero occurrences in their original fine intervals, proves simplicity, and places every other positive-half-plane occurrence beyond real coordinate 60. Delete the first two occurrences. The third lies in $(50,51)$, and the proved three-zero heat estimate bounds the residual heat trace below by $\frac1{36}e^{-c^2t}$ for $t>0$. This yields a positive residual probability law and, after convolution with the two deleted real-pole factors, strict positivity of the actual density. The third real root and the strip bound $|\Im z|<1$ for all others give the residual square gap $\Re(z^2)>49^2$.

The already certified lower bound on $F(48)$ supplies the unchanged exponential-moment cap $268341$. The original first-two-root intervals give the unchanged tail overlap at $3.18$. These facts construct the actual tail-enclosure structure; no extra real-zero classification through 102 is required. Finally the actual compact enclosure and the tail enclosure imply positive curvature everywhere by evenness and coverage, hence strict log-concavity and the PF2 determinant inequalities. The six endpoint signs and compact data remain visible until their own certificates are complete.

## Lean artifacts

- `XiMomentDensityBridgeFull.lean`
- `ThreeLowZeroCertificate.residual_heat_nonneg`
- `density_pos_of_threeLowZeroCertificate`
- `density_tail_enclosures_of_threeLowZeroCertificate`
- `density_curvature_positive_of_threeLowZeroCertificate`
- `density_strictConcaveOn_log_of_threeLowZeroCertificate`
- `density_pf2_minor_pos_of_threeLowZeroCertificate`
- `density_global_conclusions_of_original_signs_and_compact`

The Full file is an unchanged copy of the first passing scratch proof. Individual builds and axiom audits do not amount to unconditional completion or cumulative acceptance.
