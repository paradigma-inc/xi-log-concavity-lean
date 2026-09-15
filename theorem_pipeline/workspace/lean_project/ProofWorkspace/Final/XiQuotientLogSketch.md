# Entire logarithm of the actual zero-free quotient

## Statement

For the actual normalized Xi function $F$, its paired product $P$, and the already constructed entire nonvanishing quotient $Q$, there is an explicit entire function $g$ with $g(0)=g'(0)=0$ and
$$Q(z)=F(0)e^{g(z)},\qquad F(z)=F(0)e^{g(z)}P(z).$$

## Assumptions

Only the definitions and previously proved properties of the actual $F$, $P$, and $Q$. There is no hypothesis that the zero-free factor is constant.

## Proof Sketch

The logarithmic derivative $Q'/Q$ is entire because $Q$ never vanishes. Integrating it along the rectangular path from zero defines $g$; conservativity on every disk proves that its derivative is $Q'/Q$. The entire function $Qe^{-g}$ has derivative zero, hence equals its value $F(0)$ at zero. Evenness of $Q$ makes $Q'(0)$ and consequently $g'(0)$ vanish. This establishes the exponential factor exactly but does not yet prove $g$ vanishes identically; that remaining growth argument is required for the product identity.

## Lean Artifacts

- File: `XiQuotientLogFull.lean`
- Main theorems: `F_pairQuotient_eq_exp`, `F_pairedProduct_exp_factor`, `F_quotientLog_zero`, `F_quotientLog_deriv_zero`.
