# Derivatives of a complex power times an exponential

## Statement

On the principal slit plane, the $n$-th derivative of $z^s$ is $(s)_n z^{s-n}$, where $(s)_n$ is the descending Pochhammer polynomial. The derivative of $z^s e^{-\lambda z}$ is the finite Leibniz sum of these derivatives and the derivatives of the exponential.

## Assumptions

The evaluation point lies in the slit plane. The exponent is any complex number and $\lambda$ is real.

## Proof Sketch

Induct on the derivative order within the open slit plane and apply the principal-power derivative rule. The Pochhammer successor identity gives the next coefficient. Both factors are analytic there, so the finite Leibniz rule yields the product formula. These identities evaluate actual derivatives; they do not assume numerical coefficient bounds.

## Lean Artifacts

- Full proof: `PowerExponentialDerivativesFull.lean`
- Theorems: `iteratedDeriv_cpow_slit`, `complexPowerExpAtom_iteratedDeriv`.
