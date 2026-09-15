# Dyadic rational real-power enclosures

## Statement

The module proves exact rational lower and upper bounds for the actual
real power $(2^d r)^q$, where $r>0$ and $q$ are rational and $d$ is a natural
number. For a positive integer base $a$, it computes
$$
d=\lfloor\log_2 a\rfloor,\qquad r=a/2^d,
$$
proves the exact decomposition $a=2^dr$ and the range $1\le r<2$, and
obtains rational bounds on the actual value $a^q$.

## Assumptions

For the general dyadic evaluator, the rational mantissa is positive. The
logarithm order and dyadic exponent are arbitrary natural numbers. The
exponential order and range-reduction factor are positive natural numbers.
Each of the two computed logarithmic-product endpoints, divided by the
exponential range-reduction factor, has absolute value at most $1$.
For the integer specialization, the only extra hypothesis is $a>0$;
the mantissa and exact decomposition are computed, not assumed.

## Proof Sketch

The proved dyadic logarithm enclosure combines directed rational bounds
for $d\log2$ and $\log r$ and uses the actual identity
$\log(2^dr)=d\log2+\log r$. Let its endpoints be $L_-$ and $L_+$. The
minimum and maximum of $qL_-$ and $qL_+$ enclose $q\log(2^dr)$, for either
sign of $q$. Apply the verified scaled exponential enclosure at these
rational endpoints and use exponential monotonicity together with
$(2^dr)^q=\exp(q\log(2^dr))$. This proves the power enclosure without
approximating the large base directly in the logarithm series.

For a positive integer $a$, the natural binary logarithm satisfies
$2^d\le a<2^{d+1}$. Dividing by the positive number $2^d$ gives
$1\le a/2^d<2$, while ordinary rational cancellation proves the exact
decomposition. Substitution in the dyadic theorem gives the integer-base
theorem. Moreover, the logarithm series argument satisfies
$$
0\le\frac{r-1}{r+1}<\frac13.
$$
Thus the large integer base does not force a slowly converging series:
only the fixed base $2$ and a mantissa in $[1,2)$ enter the logarithm
evaluator. The arithmetic and sign checks remain exact rational ones.

## Scope

This is an efficient, sound primitive for integer-base real powers, not a
claim that every eta term or retained Xi sample has already been evaluated.
It neither changes the earlier direct real-power evaluator nor assumes
its output accuracy. No numerical table, custom axiom, or unchecked native
computation is used.

## Lean Artifacts

- `RationalPowerDyadicBoundsFull.lean`
- Definitions: `ratPowerDyadicLogLower`, `ratPowerDyadicLogUpper`,
  `ratPowerDyadicLower`, `ratPowerDyadicUpper`, `ratPowerNatMantissa`,
  `ratPowerNatLower`, `ratPowerNatUpper`.
- Theorems: `ratPowerDyadic_log_enclosure`, `ratPowerDyadic_enclosure`,
  `ratPowerNatMantissa_pos`, `ratPowerNat_decomposition`,
  `ratPowerNatMantissa_mem_Ico`, `ratPowerNatMantissa_logArgument_mem_Ico`,
  `ratPowerNat_enclosure`.

The module uses the pinned Lean 4.28.0/mathlib project. All seven theorem
axiom checks contained only `propext`, `Classical.choice`, and `Quot.sound`.
