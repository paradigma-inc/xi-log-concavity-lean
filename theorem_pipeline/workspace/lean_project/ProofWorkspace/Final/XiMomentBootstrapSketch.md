# Actual reciprocal-zero moment bootstrap

## Statement

The actual positive-half-plane zero occurrences satisfy
$$M_1<\frac1{160},\qquad C=\sum_a|a|^{-2}<\frac1{150},
\qquad M_2<\frac1{400000},\qquad \Re a>24.$$
Here $M_m=\sum_a\Re(a^{-2m})$, with analytic multiplicity retained.

## Assumptions

These conclusions use no unproved numerical or zero-location hypotheses.
The proofs apply the actual Mellin zero gap, actual log-product expansion
and the kernel-checked first two source-log enclosures.
They do not assume RH, existence of the three proposed low roots,
root simplicity or a complete finite zero list.

## Proof Sketch

First use the established actual gap $\Re a>7$ and total inverse-square
mass at most 70 in the degree-one logarithm remainder at $u=1/40$.
The certified logarithm value gives $M_1<1/160$.
The angular bound with inverse power two gives
$M_1\ge(47/49)C$, hence $C<1/150$.

Apply the degree-two remainder at $u=1/40$ and $u=1/20$ with
this sharper mass bound. Four times the first expansion minus the
second cancels $M_1$, leaving $6M_2(1/1600)^2$.
The exact log errors and both analytic remainders give $M_2<1/400000$.

Every $M_2$ summand is nonnegative under the gap 7. If an occurrence
had real part at most 24, the known imaginary strip gives $|a|^2\le577$.
Its angular lower bound would contribute at least
$41/(49\cdot577^2)>1/400000$, contradicting the whole moment bound.
Thus all actual positive-half-plane occurrences have real part greater
than 24. This conclusion is independent of any low-root existence proof.

## Lean Artifacts

- File: `XiMomentBootstrapFull.lean`.
- Main theorem: `ReciprocalXi.F_pairRoot_re_gt_twentyFour`.
- Moment bounds: `F_pairMoment_one_bound`, `F_pairMoment_two_bound`.
- Mass bound: `F_pairRoot_inv_norm_sq_tsum_lt_one_fifty`.
- Direct audit: `AuditXiMomentBootstrap.lean`, all seven public lemmas.

This strengthens the actual zero gap; it is not yet the three-zero
completeness certificate or the final global density theorem.
