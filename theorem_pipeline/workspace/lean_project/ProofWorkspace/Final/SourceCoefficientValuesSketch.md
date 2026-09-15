# Direct traversal of the source coefficient samples

## Statement

`intSourceCoefficientValues_array_eq_stream` proves that traversing the entries of an array of $13{,}601$ rational samples directly gives exactly the same $65$ integer coefficients as the original indexed coefficient stream. The initial weights, trigonometric recurrence, integer divisions, and accumulation order are unchanged.

## Assumptions

The array has length $13{,}601$. The center $c$, normalization $p$, and rational samples are arbitrary. No accuracy or positivity of the samples is assumed or concluded.

## Proof Sketch

Induction on the number of samples identifies the direct traversal of the list $[v(k),\ldots,v(k+n-1)]$ with the indexed stream started at $k$. Both recursions use the same sample, weight, trigonometric state, and accumulator in each step. Extensionality then identifies an array's underlying list with the list of its in-range indexed values, giving equality of the complete streams. This changes only how the kernel accesses the data; all rational and integer computations remain identical.

## Lean Artifacts

- File: `SourceCoefficientValuesFull.lean`
- Theorems: `intSourceCoefficientValuesFrom_map`, `intSourceCoefficientValues_eq_stream`, `sourceArray_toList_eq_samples`, `intSourceCoefficientValues_array_eq_stream`.

This is an execution-equivalence lemma, not a certificate of the source samples or the final log-concavity theorem.
