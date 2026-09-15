# Actual theta-atom certificates at all dyadic centers

## Statement

For each of the thirty-two dyadic centers and each $k\le4$, replacing the actual logarithm and pi by the certified rational midpoints changes the atom exponent by at most $10^{-68}$. A stored complex exponential with error $10^{-43}$ therefore approximates the actual atom with error at most $10^{-42}$.

## Assumptions

The center indices satisfy $j<4$ and $i<8$, the atom index satisfies $k\le4$, and the proposed stored value has the stated error relative to the midpoint exponential. The pi and logarithm bounds are proved imports, not supplied assumptions.

## Proof Sketch

The centers lie between one and sixteen, while their half-widths are at most one half. Combine the dyadic logarithm and original pi errors in the already proved exponent perturbation inequality. The actual exponent has nonpositive real part, so the complex exponential perturbation estimate applies. Triangle inequality includes the stored exponential's error.

## Lean Artifacts

`XiThetaPanelSeedFull.lean`: theta48PanelCenter_le_sixteen, theta48PanelHalfWidth_le_half, theta48PanelAtom_exponent_error, theta48PanelAtom_seed_error.
