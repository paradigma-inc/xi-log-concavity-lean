# Global growth of the actual Xi function

## Statement

For every complex $s$ and natural $n$ satisfying $|s|\le n$,
$$|\xi(s)|\le(n+2)^2n!.$$
Consequently the existing normalization $F(z)=\xi(1/2+iz/2)/4$ satisfies
$$|F(z)|\le (n+2)^2n!/4$$
whenever $|z|+1\le2n$.

## Assumptions

Only the indicated radius bounds are required. These are the actual functions,
not an abstract function constrained by a growth hypothesis. No hypothesis
about the zeros, the Riemann hypothesis, or a product formula is used.

## Proof Sketch

Euler's integral gives $|\Gamma(s)|\le\Gamma(\Re s)$ in the right half-plane.
Convexity of the real Gamma function bounds its value on $[1,n+1]$ by
$n!$. For $\Re s\ge2$, combine this with $|\zeta(s)|\le2$ and the
decaying power of $\pi$ in the completed zeta function. In the central
strip $-1\le\Re s\le2$, the previously proved theta-integral estimate
bounds the pole-subtracted completed zeta function by $1/8$, yielding a
quadratic bound for Xi. Reflect the remaining half-plane by
$\xi(1-s)=\xi(s)$. The triangle inequality gives the stated common bound.
The bound for $F$ follows by the affine change of variable.

This is a growth input for zero counting. It does not itself establish a
zero-counting estimate, summability of reciprocal zeros, or a Hadamard product.

## Lean Artifacts

- File: `XiGrowthFull.lean`
- Theorems: `complexGamma_norm_le_real`, `realGamma_le_factorial`,
  `xi_norm_le_factorial_of_two_le_re`, `xi_norm_le_quadratic_central`,
  `xi_norm_le_factorial`, `F_norm_le_factorial`.
