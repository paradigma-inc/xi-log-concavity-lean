# Exact streaming eta evaluation

The ordered root-state table at index $k$ stores each accepted integer-root power pair at exponent $k+40$. Applying the outward-rounded step to every state yields exactly the table at $k+1$; repeated advancement is identical at every offset.

Zip this table with the exact signed Euler weights. The lower and upper integer sums equal the already proved root-based eta endpoint sums, term by term. Dividing by $B=10^{180}$ and retaining the directed $2^{-N}$ remainder yields identical rational eta endpoints. At $N=400$ their actual eta enclosure follows from the already certified root table.

Thus a checker may reuse the previous node's power states instead of rebuilding every power from exponent zero. This is exact computational reuse, not a new precision estimate or a claim that retained source-node comparisons have passed.
