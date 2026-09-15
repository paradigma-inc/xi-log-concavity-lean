# A nonnegative probability law with an infinite Levy exponent

## Statement and assumptions

Let $\mu$ be a positive S-finite measure on the real line, supported on $[0,\infty)$, with $\int |y|\,d\mu(y)<\infty$. There exists a genuine nonnegative probability law whose Laplace transform for $x\ge0$ is
$$\exp\left(\int (e^{-xy}-1)\,d\mu(y)\right).$$
The construction is also given explicitly for any countable sequence of finite positive measures whose absolute first moments are summable.

## Proof Sketch

Decompose the original measure into the library's countable sequence of finite positive measures. Tonelli and the finite absolute first moment imply summability of the pieces' first moments. Each finite piece defines a compound-Poisson probability law with no larger absolute first moment. The actual independent sum of these laws therefore converges absolutely almost everywhere and defines a nonnegative probability law.

For $x,y\ge0$, the inequality $|e^{-xy}-1|\le x|y|$ proves integrability of the proposed exponent against the original measure. Countable additivity of the integral identifies it with the sum of the finite-piece exponents. The proved infinite-sum Laplace convergence and the finite compound-Poisson formulas identify the transform of the constructed law with the stated exponential. The S-finite decomposition is provided by an existing theorem, not an assumed external partition.

The input here must be a positive measure. Applying this theorem to the Xi trace still requires the trace's nonnegativity and the heat-density integration identities. This module does not assert that the unproved finite low-zero certificate holds.

## Lean Artifacts

File: `InfiniteLevyLawFull.lean`. Main theorems: `infiniteLevyLaw_isProbability`, `nonnegativeLaplace_infiniteLevyLaw`, `sfiniteLevyLaw_isProbability`, `ae_nonneg_sfiniteLevyLaw`, and `nonnegativeLaplace_sfiniteLevyLaw`.
