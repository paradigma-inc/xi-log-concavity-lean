# The remaining zero-free quotient

## Statement

The pointwise quotient $F/P$ extends across all common zeros to an entire,
nowhere-zero function $Q$. It is even, satisfies $Q(0)=F(0)$, and
$$F(w)=Q(w)P(w)$$
at every complex point.

## Assumptions

The functions are the actual $F$ and the constructed actual-zero paired
product. Their matched analytic orders were proved, not assumed.

## Proof Sketch

The meromorphic order of $F/P$ is the difference of the two finite equal
orders, hence zero everywhere. Convert this quotient to meromorphic normal
form, which fills in removable values. Order zero makes the resulting
function analytic and nonzero everywhere. Away from zeros this extension
agrees with the ordinary quotient; at a zero both sides of $F=QP$ vanish.
Evaluate at zero using $P(0)=1$. The quotient is even near zero, where the
ordinary quotient is nonsingular. Analytic continuation gives global
evenness.

**Open:** proving $Q$ is constant. An entire, even, nowhere-zero function
need not be constant. This module does not conclude $P=F/F(0)$.

## Lean Artifacts

- File: `XiPairedQuotientFull.lean`
- Main theorems: `analyticOnNhd_F_pairQuotient`, `F_pairQuotient_ne_zero`,
  `F_pairQuotient_mul_product`, `F_pairQuotient_zero`, `F_pairQuotient_even`.
