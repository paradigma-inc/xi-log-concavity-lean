# Actual degree-16 reciprocal-zero moment bound

## Statement

The actual sixteenth reciprocal-zero moment satisfies
$$M_{16}\le U_{16},$$
where $U_{16}$ is the fixed rational `momentSixteenUpper` assembled from
the 33 certified source logarithms, exact coefficient weights and all
analytic/source errors. Every summand $\Re(a^{-32})$ is nonnegative.

## Assumptions

There are no unproved numerical, RH, root-existence, completeness or
simplicity hypotheses. The actual zero gap 24 and inverse-square mass
bound $C<1/150$ have already been proved from certified source values.

## Proof Sketch

At the 33 nodes $u_j=j/40$, the degree-32 moment expansion has common
error at most
$$E=\frac{(1/150)(16/25)^{33}}{33\cdot576^{32}(1-(16/25)/576)}.$$
This follows by monotonicity from $u_j^2\le16/25$, the actual gap 24
and the proved mass bound. The fixed weight identities annihilate every
degree except 16 in the finite Taylor polynomial. Its surviving
coefficient is $-M_{16}/16$.

Replace each actual logarithm by its certified rational value $g_j$.
The weighted error is at most $W(E+10^{-118})$, where
$W=\sum_j|w_j|$ is the exact rational mass, not a floating approximation.
The triangle inequality therefore gives
$$M_{16}\le-16\sum_jw_jg_j+16W(E+10^{-118})=U_{16}.$$
Finally the angular inverse-power bound with exponent 32 is nonnegative
because every positive-half-plane occurrence has real part greater
than 24, so $1-512/(\Re a)^2>0$.

## Lean Artifacts

- File: `XiMomentExtractionFull.lean`.
- Main theorem: `ReciprocalXi.F_pairMoment_sixteen_bound`.
- Positivity: `ReciprocalXi.F_pairMoment_sixteen_terms_nonneg`.
- Exact extraction: `ReciprocalXi.F_momentTaylor_weighted_extraction`.
- Direct audit: `AuditXiMomentExtraction.lean`, all six public lemmas.

The existence of the three original low roots and their removal from
the occurrence sum remain separate obligations.
