# One-pass integer source-coefficient evaluation

## Statement

The function `intSourceCoefficientStream c p v` returns 65 integers. Dividing
each by $B=10^{180}$ yields exactly the list of
`ratSourceRoundedCoefficient c p v j` for $0\le j<65`. This equality is purely
arithmetic and holds for every rational input $c,p,v$; it introduces no sample,
trigonometric, or coefficient-accuracy hypothesis.

The actual-polynomial corollary retains the assumptions $0\le c\le40$,
$p\ge3$, and $|v_k|\le43046722$ for $0\le k\le13600$. Under these assumptions,
each decoded output differs from the corresponding actual coefficient of
`realSampledTaylorPolynomial c p v` by at most the explicit budget
$13601\,\mathrm{sourceRoundedCoefficientTermBudget}<10^{-140}$.

## Proof Sketch

An integer $a$ encodes the rational grid point $a/B$. Initialization evaluates
the rational input weight once per frequency and takes its scaled floor. The
next weight integer is
$$
W_{j+1}=\left\lfloor\frac{W_j k}{8000(j+1)}\right\rfloor.
$$
The trigonometric seed integers are formed once for the panel. A current state
$(X,Y)$ advances by
$$
X'=\left\lfloor\frac{X R_c-Y R_s}{B}\right\rfloor,
\qquad
Y'=\left\lfloor\frac{Y R_c+X R_s}{B}\right\rfloor.
$$
Signed integer division agrees with the rational downward-rounding operation,
including for negative weights and trigonometric factors. The product integer
at degree $j$ is $\lfloor W_j T_j/B\rfloor$, with exactly the source parity and
four-cycle sign.

The inner recursive list carries the current weight and emits all degrees for
a fixed frequency without recomputing earlier weights. Its invariant decodes
the emitted list to the original rounded rational summands. The outer
tail-recursive loop carries the trigonometric pair and a 65-entry integer
accumulator. It adds each emitted row, then advances the trig pair exactly
once. An induction valid for every starting index and finite number of steps
shows that decoding the accumulator gives the corresponding finite sums of
the original rational summands. The initialized full loop therefore gives the
claimed vector equality. Length and indexing lemmas yield the individual
coefficient identity, and the already proved rounding-error theorem supplies
the unchanged actual-coefficient budget.

## Execution and scope

The execution entry point returns the full integer vector; callers should
compute it once and reuse it. `ratSourceStreamCoefficient` is the convenient
mathematical indexing API, not a driver to invoke independently for every
degree. Inner loops use integer products, divisions, and additions; the
rational initialization is outside those loops. Only a single degree row and
the accumulated vector need to be retained.

This module does not evaluate the 318-panel coefficient matrix, certify stored
decimal coefficient values, establish retained sample accuracy, or conclude
the recorded curvature inequalities. It proves equivalence to the sound
fixed-grid evaluator rather than to the original decimal-160 execution.

## Lean artifacts

- Proof: `SourceCoefficientStreamFull.lean`.
- Exact vector identity: `intSourceCoefficientStream_eq`.
- Loop invariant: `intSourceCoefficientStreamFrom_eq`.
- Individual identity: `ratSourceStreamCoefficient_eq`.
- Actual coefficient error: `ratSourceStreamCoefficient_error_budget` and
  `ratSourceStreamCoefficient_error_lt`.

