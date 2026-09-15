# Checked log-Gamma endpoint literals for the first Fourier node

## Statement

The module identifies the exact rational endpoint pairs produced by the existing log-Gamma evaluator at offsets $z=1/4$ and $z=41/160$. Its parameters remain $N=440$, $M=480$, logarithm order $400$, and outward-rounding scale $10^{180}$. These are the two shared Gamma factors needed for the first nonzero retained Fourier sample.

## Assumptions

There are no extra numerical or analytic assumptions. All 440 integer-zeta coefficient pairs and all 480 Euler weights are kernel-checked in the imported certificate modules. The analytic meaning of the evaluator is supplied by the previously proved actual-Gamma enclosure theorems.

## Proof Sketch

Concatenating the eleven certified coefficient packets yields exactly the established 440-row integer-zeta table, not a replacement approximation. The checked log-pi and log-two literals, directed coefficient sums, and unchanged geometric Taylor remainder determine both rational log-Gamma endpoint pairs. Lean's ordinary kernel evaluates these finite rational expressions and verifies their equality to the displayed literals. Rewriting the exact table equality and the established table-to-evaluator identity then proves that the literal pairs are precisely the outputs of the actual log-Gamma enclosure algorithm.

## Lean Artifacts

- File: `GammaFirstNodeLiteralsFull.lean`.
- Main theorems: `gammaZetaLiteralTable_eq`, `gammaNodeZero_fast_literals`, `gammaNodeOne_fast_literals`.
- This proves the two exact Gamma endpoint identities. The source Fourier-sample inequality is obtained in the separate actual-Xi bridge; no assertion about the remaining retained samples is made here.

