# High-precision complex exponential certificates

## Statement

A forty-term Taylor sum at norm at most $1/16$ has error at most
$10^{-95}$. Sixteen rounded squarings, with input scaled by $65536$
and every residual at most $2\cdot10^{-160}$, give absolute error
$10^{-90}$. If the input then changes by at most $\epsilon\le1$,
the additional error is at most $2\epsilon(\|w\|+\eta)$.

## Assumptions

The scaled-input norm, negative input real part, finite stored-state norms
and each rounding residual are explicit and kernel-checkable. The relative
input-error lemma assumes only its stated seed and input distance bounds.

## Proof Sketch

The library exponential remainder estimate on the smaller disk provides
the Taylor bound. The proved rounded-squaring induction propagates the
initial error through all sixteen squarings. For input perturbations,
factor $e^v-e^u=e^u(e^{v-u}-1)$ and use the stored approximation to
bound $\|e^u\|$. The rational predicate checks all inputs and intermediate
states and is connected to these complex analytic bounds by exact casts.

## Lean Artifacts

- File: `ComplexExpHighPrecisionFull.lean`
- Main theorems: `complexExp_relative_input_error`,
  `ratComplexExpHighPrecisionValid_error`.

