# Exact source logarithms and moment witnesses

## Statement

For $0\le j\le32$, the stored rational $g_j$ approximates
$-\log\Re q(j/40)$ with error at most $10^{-118}$.
For the nodes $v_j=j^2/1600$, the fixed rational weights satisfy
$$\sum_j w_jv_j^m=\mathbf1_{m=16}\quad(0\le m\le32).$$
The rational first- and second-moment upper expressions are respectively
less than $1/160$ and $1/400000$. The degree-16 upper expression, after
subtracting inverse 32nd powers of the three original upper root endpoints
and multiplying by $60^{32}$, is less than $7/10$.
These last expressions become bounds on actual moments only after the
separate analytic expansion, bootstrap and extraction proofs are applied.

## Assumptions

The concrete source-log theorem has no unproved numerical hypotheses:
it uses the already checked first source block with error $2\cdot10^{-120}$.
The generic transfer lemma assumes its explicit rational interval predicate
and the corresponding actual sample-error bound. No root existence,
simplicity, completeness or RH assumption enters these arithmetic witnesses.

## Proof Sketch

Apply the established fully rounded logarithm enclosure to
$[q_j-2\cdot10^{-120},q_j+2\cdot10^{-120}]$.
The 24-term odd logarithm expansion uses a uniform transformed-argument
bound $1/500$ and directed rounding at scale $10^{160}$.
Negate the endpoints and check that they lie within $10^{-118}$ of $g_j$.
The actual source theorem transfers these rational inequalities to the
real logarithm. All 33 interval predicates are reduced in Lean's kernel.

The weights were proposed as degree-16 Lagrange coefficient weights,
but their origin is not trusted: Lean checks each of the 33 exact
monomial identities directly. It also checks their absolute mass bound
$W<3\cdot10^{29}$ and every displayed rational comparison.
The residual expression charges the complete analytic Taylor remainder
and all source-log errors, using exact $W$. The original upper endpoints
are used so that the later root subtraction has the correct direction.

## Lean Artifacts

- File: `XiMomentSamplesFull.lean`.
- Actual sample theorem: `ReciprocalXi.momentLogSample_actual`.
- Weight certificate: `ReciprocalXi.momentCoefficientWeights_exact`.
- Residual arithmetic: `ReciprocalXi.momentScaledResidualUpper_bound`.
- Audit inventory: `AuditXiMomentSamples.lean` covers all ten public
  theorems and the named decidability instance.
- Source: the unchanged `sourceFirstMidpoints` block, first 33 entries.

The residual inequality here is arithmetic evidence, not yet a
proof that only three actual zeros occur below coordinate 60.
