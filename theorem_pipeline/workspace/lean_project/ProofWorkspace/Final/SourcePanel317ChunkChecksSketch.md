# Kernel-checked coefficient blocks for panel 317

## Statement

`sourcePanel317Chunks_checked` checks every one of the $54$ consecutive blocks covering all $13{,}601$ source samples. Each block checks both the final rotation state and all $65$ accumulated coefficients. `sourcePanel317Seed_checked` checks the initial Taylor-derived rotation seed.

## Assumptions

The concrete finite checks have no assumptions. Their composition with the original full-stream identity is a separate proof obligation. Approximation of the source samples to actual reciprocal Xi is also separate.

## Proof Sketch

Each transition uses the unchanged evaluator and exact frozen source slice. Separate kernel reductions certify the proposed state pairs; separating the reductions bounds transient kernel memory. Case analysis over the finite block index combines the named transition theorems without recomputing an unchecked global answer. The proposal generator is not a trusted oracle.

## Lean Artifacts

- File: `SourcePanel317ChunkChecksFull.lean`.
- Main theorems: `sourcePanel317Seed_checked`, `sourcePanel317Chunks_checked`.
- Transition theorems: `sourcePanel317Chunk00_checked` through `sourcePanel317Chunk53_checked`.
