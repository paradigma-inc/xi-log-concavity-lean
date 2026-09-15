# Exact source pi midpoint

## Statement

`sourcePiMidpoint` is the exact rational literal used by the reviewed compact
certificate after its directed Decimal pi interval is rounded to a midpoint.
The module proves `sourcePiMidpoint_ge_three`, its exact closeness to the finite
Machin midpoint, and `sourcePiMidpoint_error`:

$$|p-\pi|\le 10^{-150},\qquad 3\le p.$$

## Source provenance and rounding semantics

The source is
`reproduction/scripts/certify_reciprocal_xi_fourier_nodes.py`, line 66, where
the directed interval is formed from 150 and 45 term Machin arctangent sums.
The compact script sets a copied Decimal context with precision 160 and
`ROUND_HALF_EVEN` at line 12, defines `mid(x)=(x.lo+x.hi)/2` at line 20, and
uses `mid(PI)` in the coefficient weights at line 69. Thus

$$
p=\frac{3141592653589793238462643383279502884197169399375105820974944592307816406286208998628034825342117067982148086513282306647093844609550582231725359408128481117446}{10^{159}}.
$$

This is a rounded midpoint of the source Decimal interval, not the exact
finite Machin sum used as `machinPiMidpoint` in `PiBoundsFull`.

## Proof Sketch

The exact rational comparison with `machinPiMidpoint` is discharged by ordinary
kernel-checked rational normalization. The accepted `machinPi_error` theorem
then bounds the finite Machin midpoint's distance from $\pi$, while
`machinPi_width_lt` bounds its radius. The triangle inequality gives the
stated $10^{-150}$ error. The lower bound $3\le p$ is a direct exact rational
check. No floating-point value, runtime evaluator, `native_decide`, or custom
axiom is used.

## Scope

This records and bounds the pi literal used by the source compact evaluator.
It does not certify any Xi node, source-table value, compact enclosure, or
global density theorem.

## Lean Artifacts

- Full proof: `ProofWorkspace/Final/SourcePiMidpointFull.lean`.
- Theorems: `sourcePiMidpoint_ge_three`,
  `sourcePiMidpoint_close_to_machin_midpoint`, `sourcePiMidpoint_error`.
- Existing prerequisite: `ProofWorkspace/Final/PiBoundsFull.lean`.
- Source files: `reproduction/scripts/certify_reciprocal_xi_fourier_nodes.py`
  and `reproduction/scripts/certify_reciprocal_xi_compact_logconcavity.py`.
