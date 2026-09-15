# Source coefficient checkpoint proposals for panel 317

## Statement and scope

This module supplies the exact integer rotation state and $65$ accumulated coefficients at offsets $0,256,512,\ldots,13568,13601$, plus the exact transition predicate between adjacent checkpoints. These are proposals, not asserted results. The final proposed vector is checked during generation against the already recorded panel-317 vector; only the sibling kernel checks can prove a transition correct.

## Mathematical construction

The frozen source and unchanged floor recurrences generate each proposed pair $(t,A)$. A transition applies the original rotation $n$ times and the original coefficient stream to the next $n\le256$ source values. It compares both outputs to the next proposed pair. No state may be reused as evidence without its proved transition and the preceding chain.

## Source and artifacts

- Frozen source SHA-256: f37fe959487881151234e89d44745e8fca746203f0f151e460e1494323114724.
- File: `SourcePanel317CheckpointsFull.lean`.
- This data module makes no theorem claim. The actual checks are in `SourcePanel317ChunkChecksFull.lean`.
