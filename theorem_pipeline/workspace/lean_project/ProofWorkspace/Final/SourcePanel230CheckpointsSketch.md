# Original compact panel 230: Checkpoints

## Statement and scope

This data module contains 55 proposed states at offsets $0,256,512,\ldots,13568,13601$. It makes no numerical theorem claim.

## Proof sketch

Each state stores the rotation pair and all 65 accumulated coefficients from the unchanged directed-floor recurrence. Only the separately proved transitions justify reuse.

## Source and Lean artifact

- Frozen source SHA-256: `f37fe959487881151234e89d44745e8fca746203f0f151e460e1494323114724`.
- File: `SourcePanel230CheckpointsFull.lean`.
- Generated values are proposals until their actual Lean build succeeds.
