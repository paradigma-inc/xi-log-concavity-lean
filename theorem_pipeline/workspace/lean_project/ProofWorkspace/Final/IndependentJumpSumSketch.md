# A probability law for a convergent independent jump sum

## Statement and assumptions

For a sequence of real probability measures $\nu_n$, assume each absolute first moment is finite and $\sum_n\int |y|\,d\nu_n(y)<\infty$. Their coordinate sum on the actual infinite product probability space converges absolutely almost everywhere. Its pushforward is a probability measure. If every coordinate law is supported on the nonnegative half-line, so is the sum law. The characteristic functions of the finite sums converge pointwise to that of the sum law.

## Proof Sketch

Tonelli identifies the expected sum of coordinate absolute values with the sum of absolute first moments, so it is finite almost everywhere. The sum is almost-everywhere measurable as the limit of measurable finite sums. Pushing forward the product probability measure therefore gives a genuine probability measure. Nonnegative support passes coordinatewise to the convergent sum. Finally, the complex exponential in a characteristic function has modulus one; dominated convergence proves convergence of the finite-sum characteristic functions.

This is a general construction, not yet an instantiation using the Xi heat trace. No Xi-specific positivity or exponential moment is asserted here.

## Lean Artifacts

File: `IndependentJumpSumFull.lean`. Main theorems: `ae_summable_infinitePi_coordinates`, `independentJumpSumLaw_isProbability`, `ae_nonneg_independentJumpSumLaw`, and `tendsto_charFun_finiteJumpSum`.
