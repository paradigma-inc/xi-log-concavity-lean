# Multiplicities of the paired product

## Statement

At every complex point $w$, the actual $F$ and the constructed paired product
$P$ have exactly the same analytic order. This includes the multiplicity at
every zero and order zero away from the zeros.

## Assumptions

No supplied zeros or multiplicities. The existing actual analytic orders and
the proved reciprocal-square convergence are used throughout.

## Proof Sketch

Restricting the occurrence index to any subset preserves compact uniform
convergence and entire analyticity. At a positive-real-part zero $a$, its
occurrence fiber is explicitly equivalent to the finite type with
$m_a$ elements. Split the full product into this fiber and its complement:
$$P(w)=(1-(w/a)^2)^{m_a}P_{\ne a}(w).$$
The complementary product is nonzero at $a$, since a vanishing complementary
factor would require a root equal to $a$ or $-a$; the former was removed and
the latter has negative real part. The polynomial factor has order one at
$a\ne0$. Additivity and power multiplication of analytic orders give order
$m_a$ for $P$. Evenness handles all negative-real-part zeros. At every
other point both functions are nonzero and have order zero.

Matching multiplicities permits removal of the apparent singularities of
$F/P$. It does not yet prove this zero-free quotient is constant.

## Lean Artifacts

- File: `XiPairedProductOrderFull.lean`
- Main theorems: `F_pairedProduct_split`, `F_pairRootFiber_product`,
  `F_pairComplement_ne_zero`, `F_pairedProduct_order_eq`.
