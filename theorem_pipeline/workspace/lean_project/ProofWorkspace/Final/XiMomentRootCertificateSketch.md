# Original intervals to a three-zero certificate

## Statement and assumptions

The actual function is $F(z)=\xi(1/2+iz/2)/4$. The three original upper endpoints $U_j$ are those in `momentRootUpperEndpoints`, and $L_j=U_j-4\cdot10^{-29}$. Assuming an actual real zero in each $(L_j,U_j)$, Lean constructs `ThreeLowZeroCertificate`: one occurrence at each root, analytic order one at each, and real part greater than 60 for every other positive-half-plane occurrence. `threeLowZeroCertificate_of_signs` derives those interval roots from opposite actual endpoint signs. Those six signs remain explicit prerequisites; this module does not assert their certification.

## Proof sketch

Continuity and real-valuedness of $F$ give an interior real zero by the intermediate value theorem. Each such zero has positive analytic order, so one may select an occurrence without assuming simplicity. The original intervals are positive, disjoint and ordered, hence the three selected occurrences are distinct. The already proved reciprocal-moment bound excludes any fourth occurrence with real part at most 60. In particular, every occurrence at a selected root must be the selected one: another would contradict this bound. The actual occurrence fiber has cardinality equal to analytic order, proving that order is one. Thus multiplicities are accounted for rather than suppressed.

## Lean artifacts

- `XiMomentRootCertificateFull.lean`
- `F_exists_real_zero_of_opposite_signs`
- `threeLowZeroCertificate_of_interval_existence`
- `threeLowZeroCertificate_of_signs`
- `ThreeLowZeroCertificate.exhaustion`

No RH, finite-zero completeness or simplicity premise is used. The file is an unchanged copy of the passing scratch2 proof; individual build and direct axiom audit are recorded separately from cumulative acceptance.
