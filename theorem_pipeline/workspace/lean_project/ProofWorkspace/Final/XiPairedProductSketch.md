# A convergent paired product from the actual zeros

## Statement

Use each actual zero $z$ of $F$ with positive real part once for every unit
of its analytic multiplicity. The product
$$P(w)=\prod_{\Re z>0,\ F(z)=0}\left(1-(w/z)^2\right)$$
is convergent uniformly on compact sets, is entire and even, and satisfies
$P(0)=1$. Its zero set is exactly the zero set of $F$.

## Assumptions

No extra hypotheses on $F$ or its zeros. Multiplicity occurrences use the
actual analytic orders. Strict zero-strip geometry ensures that no zero
has real part zero, so positive real parts select one side of each pair.

## Proof Sketch

Repeat each zero according to its finite natural multiplicity. The preceding
weighted summability theorem gives summability of $|z|^{-2}$ on this index
type and hence on its positive-real-part subtype. On any compact set the
deviation $(w/z)^2$ is bounded by a constant times this summable majorant.
The uniform infinite-product theorem gives compact uniform convergence;
the locally uniform limit of the finite polynomial products is entire.
Every factor is even and equals one at zero. A vanishing factor occurs
exactly when $w=z$ or $w=-z$. Every actual zero has an occurrence on one
side of this pairing. Conversely, away from the actual zero set all factors
are nonzero, and summability guarantees a nonzero product.

**Not yet proved:** $P=F/F(0)$. Equality of zero sets alone does not prove
equality of multiplicities or eliminate a nonconstant zero-free factor.
This module does not claim the Hadamard factorization identity.

## Lean Artifacts

- File: `XiPairedProductFull.lean`
- Main theorems: `multipliable_F_pairFactors`,
  `F_pairedProduct_hasProdUniformlyOn`, `differentiable_F_pairedProduct`,
  `F_pairedProduct_zero`, `F_pairedProduct_even`, `F_pairedProduct_zero_iff`.
