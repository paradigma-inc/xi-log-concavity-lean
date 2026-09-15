# A probability law from a nonnegative integrable heat density

## Statement and assumptions

Let $H$ be a real integrable function on $(0,\infty)$, nonnegative almost everywhere there. The measure with density $H(t)/t$ on that half-line is positive and S-finite, with finite absolute first moment. The constructed Levy law is a genuine nonnegative probability law with Laplace transform
$$L(x)=\exp\int_0^\infty\frac{e^{-xt}-1}{t}H(t)\,dt,\qquad x\ge0.$$

## Proof Sketch

The measure is represented by the nonnegative extended-real density. The explicit nonnegativity hypothesis ensures this representation equals $H(t)/t$ almost everywhere, without altering the input. Multiplication by $t$ cancels the denominator on the positive half-line, so integrability of $H$ gives a finite first moment. The previously constructed S-finite Levy law then applies. The change-of-density formula converts its Laplace exponent into the heat integral shown above.

This result assumes nonnegativity of $H$ explicitly. It does not prove nonnegativity of the selected Xi heat trace or discharge its finite low-zero certificate.

## Lean Artifacts

File: `HeatSubordinatorFull.lean`. Main theorems: `integrable_id_heatLevyMeasure`, `heatSubordinatorLaw_isProbability`, and `nonnegativeLaplace_heatSubordinatorLaw`. Named proof instance: `heatLevyMeasure_sfinite`.
