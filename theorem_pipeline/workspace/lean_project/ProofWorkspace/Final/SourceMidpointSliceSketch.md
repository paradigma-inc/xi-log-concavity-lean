# Exact source-slice lookup

## Statement and assumptions

`sourceMidpointSlice_lookup` derives the original per-index source lookup from an exact equality between a proposed list and the matching slice of the frozen full array. The index is bounded by the slice count. `sourceBlock5216Midpoints_slice_checked` kernel-checks this equality for all 32 original entries at offset 5216, and `sourceBlock5216Midpoints_lookup_via_slice` recovers exactly the previously proved lookup statement. No numerical approximation or new source value is introduced.

## Proof sketch

Indexing the first $n$ entries of a list agrees with indexing the original list at every index below $n$. Indexing a list after dropping $s$ entries adds $s$ to the index. Apply these two identities to the proved full-slice equality, then use the array-to-list lookup identity. Thus one checked slice equality suffices for all individual lookup statements, instead of independently reducing the full array lookup for every entry. The concrete slice equality is checked by the Lean kernel, not trusted from the Python proposal.

## Lean artifacts

- `SourceMidpointSliceFull.lean`
- `sourceMidpointSlice_lookup`
- `sourceBlock5216Midpoints_slice_checked`
- `sourceBlock5216Midpoints_lookup_via_slice`

The Full file is unchanged from the passing scratch proof. The bounded scratch check took 110.64 seconds elapsed and 6.94 seconds user CPU on the currently paging host; this is not a controlled speedup benchmark. Future source packets may use the proved transfer without changing their numerical data, original lookup statements, or actual-Xi error bound.
