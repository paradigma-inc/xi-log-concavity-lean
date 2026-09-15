# Exact Euler weights and blockwise zeta arithmetic

## Statement

The module certifies the exact 480 Euler weights used by the existing integer-zeta evaluator and proves that summing them in blocks of 16 produces exactly the same lower and upper rational endpoints. The arithmetic precision is unchanged: the Euler order is $480$ and the outward-rounding scale is $10^{180}$.

## Assumptions

There are no additional mathematical assumptions. The shared weight literals are checked against the already proved linear Euler-weight recurrence by Lean's ordinary kernel.

## Proof Sketch

For a list of blocks, induction proves that summing each block with its absolute index offset equals the indexed sum over the flattened list. The literal blocks flatten to the certified 480-element weight list. Instantiating the generic identity with the established signed integer lower and upper division formulas preserves both directed sums exactly. Applying the existing zeta multiplier, analytic Euler remainder, and outward rounding therefore yields precisely the original zeta endpoint pair.

## Lean Artifacts

- File: `GammaZetaWeightsFull.lean`
- Theorems: `gammaEulerWeights480_eq`, `intEtaChunkSum_eq`, `gammaEulerWeightChunks480_eq`, `gammaEtaLowerChunkSum_eq`, `gammaEtaUpperChunkSum_eq`, `gammaZetaChunkPair_eq`.
- This module does not assume or certify any retained Fourier node.

