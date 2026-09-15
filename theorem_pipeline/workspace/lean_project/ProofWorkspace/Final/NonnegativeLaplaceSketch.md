# Laplace transforms of nonnegative compound-Poisson laws

## Statement and assumptions

For a probability measure $\nu$ supported on $[0,\infty)$, and $x\ge0$, write $L_\nu(x)=\int e^{-xy}\,d\nu(y)$. It is a genuine integrable transform. Its value on the $n$th convolution power is $L_\nu(x)^n$, and on the compound-Poisson law of rate $r$ it is $\exp(r(L_\nu(x)-1))$. For a finite positive measure $\mu$ supported on $[0,\infty)$, the finite Levy law therefore has Laplace transform $\exp\int(e^{-xy}-1)\,d\mu(y)$.

## Proof Sketch

On the nonnegative support the Laplace integrand lies between zero and one. This proves integrability of each probability-law transform. The convolution integral and the addition law of the exponential factor the transform of a convolution, giving finite powers by induction. Integration against the Poisson mixture is justified by bounded integrability, and summing the actual Poisson series gives the exponential formula. Finally normalize the finite measure; handle zero mass separately by the already proved point mass at zero.

These are direct real-integral identities, not an unjustified extension of a characteristic function to complex frequencies. The Xi-specific infinite law is not asserted here.

## Lean Artifacts

File: `NonnegativeLaplaceFull.lean`. Main theorems: `integrable_nonnegativeLaplace`, `nonnegativeLaplace_convolutionPower`, `nonnegativeLaplace_compoundPoissonLaw`, and `nonnegativeLaplace_finiteLevyLaw`.
