# Positive selected heat trace from a three-zero certificate

## Statement

For $c\in[0,51]$, $t>0$, $\operatorname{Re}a\ge60$ and
$|\operatorname{Im}a|\le1$,
$$\operatorname{Re}e^{-a^2t}\ge
-e^{-c^2t}e^{-499\operatorname{Re}a/2400}.$$
For actual positive-real-part zero occurrences, the inverse-square budget
bounds the negative contribution of any such subset by
$(35/36)e^{-c^2t}$. Thus a selected set containing a real occurrence $c$
and having all its other occurrences at real part at least $60$ satisfies
$$\operatorname{Re}F_{\mathrm{selectedHeatTrace}}(t)
\ge \frac1{36}e^{-c^2t}>0.$$

## Assumptions

The retained occurrence is real and has real part at most $51$; all other
selected occurrences have real part at least $60$. These are explicit,
unproved finite-zero inputs at this stage. The zero strip, summability and
global inverse-square bound of $70$ are already established for the actual
zeros, counting analytic multiplicity.

## Proof Sketch

A negative heat term requires a negative cosine phase, which implies
$\operatorname{Re}a\,t\ge3/4$. The squared gap from $c$ then contributes
at least $499\operatorname{Re}a/2400$ to exponential decay. A kernel-checked
32-term rational exponential sum proves
$259272\le e^{499/40}$. Extending this by the quadratic lower bound for
the exponential gives $72(A^2+1)\le e^{499A/2400}$ for $A\ge60$.
Consequently the negative weights are bounded by inverse squared root
norms divided by $72$. Absolute summability permits restricting the sum
and splitting off the retained real occurrence. The budget $70/72=35/36$
leaves the stated positive margin. No reality of high zeros is assumed.

## Lean Artifacts

- File: `XiModerateHeatFull.lean`.
- Theorems: `exp_499_over_40_lower`, `exponential_dominates_moderate_zero_weight`, `moderate_zero_heat_lower`, `F_moderateZero_exp_le`, `F_selectedModerateHeat_lower`, `F_selectedHeatTrace_lower_of_three_zero_certificate`.

The source convention with twice the selected heat trace has margin
$e^{-c^2t}/18$. The module does not prove the required finite-zero data or
the final global log-concavity theorem.

