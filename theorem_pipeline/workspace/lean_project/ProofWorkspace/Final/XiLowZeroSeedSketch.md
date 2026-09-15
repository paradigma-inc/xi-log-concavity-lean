# Actual fine-root theta seed transfer

## Statement

For $|x|\le60$, $1\le c\le32$ and $k\le5$, the actual atom exponent
is within $10^{-68}$ of the rational-pi/logarithm input when the logarithm
error is at most $5\cdot10^{-70}$. A stored exponential approximation
$w$ with error $10^{-90}$ therefore has actual atom error at most
$$
10^{-90}+2\cdot10^{-68}(\|w\|+10^{-90}).
$$

## Assumptions

The real coordinate, center and mode bounds are explicit. The log seed
bound and stored exponential error must still be proved for each concrete
case. The pi certificate is the original, already kernel-checked source
midpoint with error at most $10^{-150}$.

## Proof Sketch

The complex exponent has norm at most $16$. Splitting the two input
errors gives $16e+k^2cd$, with $k^2c\le800$. The fixed logarithm and pi
bounds make this at most $10^{-68}$. The exact real-center
power-times-exponential identity and the relative exponential perturbation
lemma give the stated error without losing the small size of far-panel atoms.

## Lean Artifacts

- File: `XiLowZeroSeedFull.lean`
- Main theorem: `lowZeroAtom_relative_seed_error`.

