# Xi tail assembled from finite source inputs

## Statement and assumptions

Two actual zero occurrences have real roots in $[28.269,28.270]$ and $[42.044,42.045]$. The remaining roots below height $102$ are real and at least $50$, and one remaining occurrence has real part at most $51$. The finite-factor Xi quotient at $48$, multiplied by two, is at most $268341$.

These inputs construct a tail-enclosure witness for the actual density. Adding the explicit compact-enclosure witness yields strict log-concavity and the strictly positive order-two translation determinant.

## Proof Sketch

The finite real-root certificate gives the selected heat-trace lower bound; unconditional strip geometry supplies the remaining spectral gap at $49$ and nonvanishing at $48$. The constructed residual law, exact density convolution, and actual exponential moments give all derivative remainder bounds. The kernel-checked source-overlap arithmetic supplies the overlap at $3.18$. The existing compact/tail assembly and positive-kernel convolution then imply the two final conditional corollaries.

This module does **not** supply the finite zero certificate, the moment-cap input, or the compact-enclosure witness. It is not the unconditional full theorem. No RH, supplied positive-law axiom, or assumed curvature inequality occurs.

## Lean artifacts

- `XiSourceTailFull.lean`
- `density_tail_enclosures_of_finite_source_inputs`
- `density_strictConcaveOn_log_of_finite_source_inputs`
- `density_pf2_minor_pos_of_finite_source_inputs`
