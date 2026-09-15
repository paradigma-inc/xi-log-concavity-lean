# Exponential moments of finite compound-Poisson laws

## Statement and assumptions

For a probability jump law $\nu$, a real parameter $q$, and integrable $e^{qy}$ under $\nu$, every finite convolution power and every finite-rate compound-Poisson law has a finite exponential moment. The exact formulas are $M_{\nu^{*n}}(q)=M_\nu(q)^n$ and $M_{\mathrm{CP}(r,\nu)}(q)=\exp(r(M_\nu(q)-1))$.

## Proof Sketch

The product of two integrable exponential functions is integrable on the product measure. The addition law of the exponential passes this fact through convolution and factors the moments, giving powers by induction. For the Poisson mixture, the nonnegative Lebesgue integral of the norm becomes a positive Poisson series of those finite moments. The proved exponential series makes that integral finite. Only then is the Bochner integral exchanged with the countable measure sum to obtain the moment formula.

The input exponential integrability is explicit. This does not yet prove exponential moments for the infinite-activity law or the numerical Xi moment bound.

## Lean Artifacts

File: `CompoundPoissonExponentialFull.lean`. Theorems: `integrable_exp_convolutionPower`, `exponentialMoment_convolutionPower`, `integrable_exp_compoundPoissonLaw`, `exponentialMoment_compoundPoissonLaw`.

