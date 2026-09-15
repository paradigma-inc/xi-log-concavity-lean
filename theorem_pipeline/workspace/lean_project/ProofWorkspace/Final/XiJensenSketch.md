# An actual multiplicity-weighted zero-count bound

## Statement

Let $N_F(r)$ count all zeros of the existing entire function
$F(z)=\xi(1/2+iz/2)/4$ in $|z|\le r$, with analytic multiplicities.
For $R>0$ and natural $n$ with $R+1\le2n$,
$$N_F(R/2)\le
\frac{\log((n+2)^2n!)-\log|F(0)|}{\log2}.$$
The associated multiplicity-weighted Jensen logarithmic sum over every zero
in $|z|\le R$ obeys the same numerator bound.

## Assumptions

Only the stated radius inequalities are assumptions. The finite zero set,
its multiplicities, the actual growth estimate, and $F(0)\ne0$ are proved
from the existing definitions. No supplied zero list, RH, or counting oracle
is assumed.

## Proof Sketch

Apply Jensen's formula to $F$ in the radius-$R$ disk. At the center the
divisor vanishes and the meromorphic trailing coefficient is $F(0)$.
The previously proved factorial growth estimate bounds the circle average
of $\log|F|$. At a zero on the circle, Lean's total logarithm takes the
value zero; this remains below the nonnegative logarithm of the chosen
growth bound. The divisor at each point of the disk is exactly its natural
analytic multiplicity. Its support is contained in the finite set of all
actual zeros. For every zero in the smaller disk, $\log(R/|z|)\ge\log2$;
all remaining summands are nonnegative. Summation and division by
$\log2>0$ give the displayed bound.

This bound does not establish low-zero reality/simplicity or an infinite
product. Reciprocal-square summability is a subsequent step.

## Lean Artifacts

- File: `XiJensenFull.lean`
- Definitions: `F_zeroFinset`, `F_zeroCount`.
- Main theorems: `F_jensen_sum_bound`, `F_jensen_finset_sum_bound`,
  `F_zeroCount_log_two_le`, `F_zeroCount_le`.
