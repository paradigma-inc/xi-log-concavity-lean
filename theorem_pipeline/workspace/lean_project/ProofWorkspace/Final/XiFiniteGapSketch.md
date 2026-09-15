# Finite zero data imply the residual spectral gap

## Statement and assumptions

Suppose the selected actual roots below height $T$ are real and at least $c>R\ge0$, while $R^2+1\le T^2$ and $T\ge0$. Then every selected root $z$ satisfies $\operatorname{Re}(z^2)>R^2$. Separate theorems prove nonvanishing of $F(r)$ when $r>0$ is excluded from the deleted finite roots and lies below that remaining-root gap.

## Proof Sketch

Below $T$ the real-root certificate gives the assertion directly. Above $T$, the unconditional strip bound $|\operatorname{Im}z|<1$ gives $\operatorname{Re}(z^2)>(\operatorname{Re}z)^2-1\ge R^2$. If $F(r)=0$, its positive analytic multiplicity gives an actual positive zero occurrence. It is not among the deleted roots, contradicting the selected gap. The two-root corollary uses $a<b<r\le L$.

The finite reality and minimum-root data remain explicit assumptions, not verified zero data or new axioms.

## Lean artifacts

- `XiFiniteGapFull.lean`
- `F_selected_gap_of_finite_zero_certificate`
- `F_real_ne_zero_of_deleted_gap`
- `F_real_ne_zero_between_deleted_and_remaining`
