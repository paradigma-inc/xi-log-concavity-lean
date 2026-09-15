# Original compact panel 110: ChunkChecks

## Statement and scope

The exact initial seed, initial zero accumulator and all 54 consecutive transitions are checked by Lean's kernel. No sample or transition is omitted.

## Proof sketch

Every block uses the original frozen source slice, advances both rotation and all coefficients, and checks equality with its proposed next state. Finite case analysis assembles the named proofs without using a native or external decision oracle. The exact source slice is kernel-certified once and reused by the equality-transfer lemma; the original full-array transition statement is unchanged.

## Source and Lean artifact

- Frozen source SHA-256: `f37fe959487881151234e89d44745e8fca746203f0f151e460e1494323114724`.
- File: `SourcePanel110ChunkChecksFull.lean`.
- Generated values are proposals until their actual Lean build succeeds.
