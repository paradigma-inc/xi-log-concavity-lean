# Actual positive-real Xi factorization through eta

## Statement

For every real $s>0$ with $s\ne1$, the actual entire Xi function satisfies
$$
\xi(s)=\frac{s}{2}\,\Gamma(s/2)\,\pi^{-s/2}\,
  \eta_I(s)\,\frac{s-1}{1-2^{1-s}}.
$$
The right side is real, so the same expression equals $\operatorname{Re}\xi(s)$.
The denominator $1-2^{1-s}$ is nonzero, and the bracket
$(s-1)/(1-2^{1-s})$ is positive. The removable value is handled separately
by the already proved exact identity $\xi(1)=1/2$.
The same bracket also equals $|s-1|/|1-2^{1-s}|$, giving a positive-factor
form convenient for directed interval arithmetic.

## Assumptions

The factorization assumes only that $s$ is real, $s>0$, and $s\ne1$.
The denominator and bracket sign theorems need only $s\ne1$ and in fact
hold for every real $s$ other than $1$. No eta identity, analytic
continuation, Gamma approximation, or real-valuedness of Xi is assumed.

## Proof Sketch

The previously established actual Mellin continuation proves the
regularized identity
$$
(s-1)\eta(s)=\frac{(1-2^{1-s})\,2\xi(s)}{s\Gamma_{\mathbb R}(s)}
$$
on the complex right half-plane. At a real argument, the actual complex
Mellin integral agrees with $\eta_I(s)$. Complex powers of positive real
bases agree with their real powers, and complex Gamma agrees with real
Gamma. Therefore
$$
\Gamma_{\mathbb R}(s)=\pi^{-s/2}\Gamma(s/2)
$$
as an equality of complex numbers with the real expression embedded.

The factor $s\Gamma_{\mathbb R}(s)$ is nonzero because $s>0$ and the
completed Gamma factor has no zeros in the right half-plane. If $s<1$,
then $2^{1-s}>1$; if $s>1$, then $2^{1-s}<1$. Thus the remaining denominator
is nonzero whenever $s\ne1$, and it has the same sign as $s-1$. This also
proves positivity of the bracket without an appeal to numerical
approximation.

Clearing these verified nonzero denominators in the regularized identity
gives the displayed Xi factorization. All remaining rearrangements are
polynomial identities. Taking real parts proves the real-valued formula
needed by the finite rational evaluator. No limiting argument at $s=1$
is needed, because the entire definition of Xi already gives its exact
removable value there.

## Scope

This is an unconditional analytic identification of the actual Xi value
on the stated positive-real domain. It makes no claim that the numerical
eta, Gamma, power, or bracket factors at all retained quadrature nodes
have been evaluated. It does not establish the full density-curvature
target.

## Lean Artifacts

- `XiEtaFactorizationFull.lean`
- Definition: `xiEtaBracket`.
- Theorems: `xiEta_denominator_ne_zero`, `xiEtaBracket_pos`,
  `xiEta_denominator_neg_of_lt_one`, `xiEta_denominator_pos_of_one_lt`,
  `xiEtaBracket_eq_abs`, `GammaReal_ofReal_eq`, `xi_eq_etaIntegral`,
  `xi_re_eq_etaIntegral`.
- Removable value reused from `XiDefinitionFull.lean`: `xi_one`.

The proof uses the pinned Lean 4.28.0/mathlib project and the previously
proved actual eta continuation. All eight theorem axiom checks contained
only `propext`, `Classical.choice`, and `Quot.sound`.
