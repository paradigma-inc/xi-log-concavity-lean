# Direct bounds for far Gaussian atoms

## Statement

For $|x|\le60$, $c\ge1$, $0\le h\le c/16$ and $k^2c\ge72$,
every actual scaled derivative of the theta atom has norm at most
$10^{-50}$. Consequently zero is a valid stored coefficient at that
error radius, for every degree, including all eighty retained degrees.

## Assumptions

Only the stated exact coordinate, mode and geometry inequalities.
No exponential-value, derivative, root or numerical enclosure is assumed.

## Proof Sketch

On the closed disk of radius $c/16$ centered at the positive real
number $c$, the real part is at least $15c/16$. The principal-power
factor has norm at most $2\exp(|x|\pi/8)\le2\cdot3^{30}$.
The Gaussian exponent is at most $-192$, since $\pi>3$ and
$k^2c\ge72$. The previously proved $\exp(96)\ge10^{41}$
gives $\exp(-192)\le10^{-82}$. Their product is less than
$10^{-50}$. Apply Cauchy's derivative estimate on that disk,
cancel the factorial, and use $(h/(c/16))^n\le1$.

This replaces only still-unbuilt far-atom witnesses. It changes neither
the actual integrand nor the original source points and error budget.

## Lean Artifacts

- Full proof: `XiLowZeroFarAtomsFull.lean`.
- Main theorems: `lowZeroFarAtom_scaledCoefficient_norm_le`,
  `lowZeroFarAtom_zeroCoefficient_error`.

