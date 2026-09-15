# Real Taylor polynomial and density derivative bridge

## Statement

The polynomial `realSampledTaylorPolynomial` has the real parts of the actual normalized sampled-quadrature Taylor coefficients through degree $64$. For every real argument $x$ and every order $n$, its $n$th algebraic derivative evaluated at $x$ equals the real part of the $n$th complex derivative of `sampledTaylorPolynomial64` at $x$. Explicit first- and second-derivative corollaries match the polynomial fields used by `DensityCompactEnclosures`.

The actual normalized entire density $G_c(z)=G(c+z/200)$ satisfies
$$
\operatorname{Re}G_c(x)=g(c+x/200),\qquad
\operatorname{Re}G_c'(x)=\tfrac1{200}g'(c+x/200),\qquad
\operatorname{Re}G_c''(x)=\tfrac1{200^2}g''(c+x/200).
$$

## Assumptions

These identities hold for every real center $c$, normalization parameter $p$, sample sequence $v$, and real argument $x$. There are no sample-accuracy, positivity, coefficient-enclosure, or numerical-certificate assumptions. The established entire actual density and its agreement with the real density are imported from the earlier analytic modules.

## Proof Sketch

Taking real parts commutes with a finite complex polynomial evaluated on the real axis. For an entire function, restriction to the real axis followed by the real-part map commutes with differentiation: the chain rule identifies the real derivative with the real part of the complex derivative. Induction applies this fact to every complex derivative, which remains differentiable by complex analyticity. Applied to the Taylor polynomial, this identity agrees with the ordinary algebraic polynomial derivative. Applied to the entire density and its already proved real-axis identity, the ordinary real chain rule gives the factors $1/200$ and $(1/200)^2$ in its first two normalized derivatives.

These are exact conversion identities, not proofs of any remaining finite sample or curvature-coefficient bounds.

## Lean Artifacts

- File: `ProofWorkspace/Final/RealTaylorBridgeFull.lean`
- Theorems: `realSampledTaylorPolynomial_eval`, `realSampledTaylorPolynomial_iterated_derivative_eval`, `realSampledTaylorPolynomial_derivative_eval`, `realSampledTaylorPolynomial_second_derivative_eval`, `normalizedComplexDensity_ofReal_re`, `normalizedComplexDensity_deriv_re`, `normalizedComplexDensity_second_deriv_re`.
- Source context: `theorem_pipeline/workspace/contexts/reciprocal_xi_global_logconcavity.md`, with the actual analytic and sampled Taylor definitions in the imported modules.
