# Original coefficient source slice 23

## Statement

`sourceCoefficientSlice23_checked` identifies the proposed literal list with the exact original
source-array slice at indices $5888\le k<6144$. It supplies no
approximation claim about the actual function; that remains the separate
source-grid theorem.

## Proof sketch

Lean's kernel reduces equality between the literal list and the unchanged
array slice. The proved generic transition transfer can then reuse that
equality for each panel, without repeating the full-array reduction inside
the coefficient recurrence. Every original value and index is retained.

## Source and Lean artifact

- Frozen source SHA-256: `f37fe959487881151234e89d44745e8fca746203f0f151e460e1494323114724`.
- File: `SourceCoefficientSlice23Full.lean`.
- Theorem: `sourceCoefficientSlice23_checked`.
- The generated equality is a proposal until its Lean build passes.
