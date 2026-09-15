# Exact rational enclosures for integer zeta values

## Statement

For natural numbers $M,j$, define the rational Euler weight

$$
w_{M,j}=2^{-M}\sum_{j<n\le M}\binom{M}{n}.
$$

For a natural integer exponent $k$, the rational finite eta approximation is

$$
S_{M,k}=\sum_{j=0}^{M-1}\frac{(-1)^j w_{M,j}}{(j+1)^k}.
$$

The module proves that its real embedding equals the previously proved actual approximation `etaEulerApprox M (k:ℝ)`. Define exact rational directed endpoints

$$
c_k=\frac{2^k}{2^k-2},\qquad
L_{M,k}=c_kS_{M,k},\qquad
U_{M,k}=L_{M,k}+\frac{2}{2^M}.
$$

`ratZetaNat_enclosure` proves for every $M\in\mathbb N$ and $k\ge2$ that

$$
L_{M,k}\le\operatorname{Re}\zeta(k)\le U_{M,k}.
$$

The exact interval width is $2/2^M$. In particular, `ratZetaNat_480_width_lt` proves

$$
U_{480,k}-L_{480,k}<10^{-140}.
$$

The endpoint definitions use only finite rational arithmetic and natural binomial coefficients. No supplied zeta table or approximate real powers are used.

## Assumptions

Only $k\ge2$ is required for the actual zeta enclosure. The number of Euler terms $M$ is arbitrary, including zero. The exact width identity and its numerical specialization do not require any condition on $k$.

## Proof Sketch

Casting the rational weights to the reals commutes with their finite sums and division by $2^M$. Positive real powers at a natural exponent agree with ordinary natural powers, so casting $S_{M,k}$ yields exactly the established real eta approximation. The prior actual eta-integral and zeta theorems give

$$
0\le(1-2^{1-k})\operatorname{Re}\zeta(k)-S_{M,k}\le2^{-M}.
$$

For $k\ge2$, the elementary inequality $2^k\ge4$ implies $0<c_k\le2$. Exact real-power algebra proves $c_k(1-2^{1-k})=1$. Multiplying the prior two-sided error inequality by the positive $c_k$ therefore gives a nonnegative zeta error at most $c_k2^{-M}\le2\cdot2^{-M}$, which is precisely the asserted directed interval. Subtracting its endpoints cancels the finite approximation and leaves $2/2^M$. Lean's exact rational arithmetic verifies the bound at $M=480$; the exponentiation threshold is locally raised only to permit that finite kernel-checked calculation.

## Scope

This is a sound exact-rational evaluator for the integer zeta coefficients used in the centered log-Gamma series. It neither assumes nor separately certifies a supplied table of evaluated endpoints. Downstream Gamma calculations must evaluate the finite rational expressions and propagate these directed errors through their signed coefficients. No retained Xi samples or curvature certificates are claimed by this module alone.

## Lean Artifacts

- Full proof: `ProofWorkspace/Final/RationalZetaBoundsFull.lean`.
- Definitions: `ratEtaEulerWeight`, `ratEtaNatSum`, `ratZetaNatFactor`, `ratZetaNatLower`, `ratZetaNatUpper`.
- Theorems: `ratEtaEulerWeight_cast`, `ratEtaNatSum_cast`, `ratZetaNatFactor_pos`, `ratZetaNatFactor_le_two`, `ratZetaNatFactor_cancel`, `ratZetaNat_enclosure`, `ratZetaNat_width`, `ratZetaNat_480_width_lt`.
- Namespace: `ReciprocalXi`.
- Source: the existing reciprocal-Xi finite evaluation material and `theorem_pipeline/workspace/prompts/eta_evaluator.txt`.
- Tracked run: `20260909T184117Z_fe26`.
