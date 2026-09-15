# Rational weighted sums and actual Taylor panels

## Statement

The rational weighted sum of forty stored coefficients for each of four atoms embeds exactly into the real approximate panel integral. Uniform actual scaled-coefficient error at most $10^{-25}$ gives panel error at most $320\cdot10^{-25}$.

## Assumptions

The center is positive, the rational half-width lies in $[0,1/2]$, and the $160$ actual coefficient errors are explicit hypotheses. Concrete traces must discharge them using the coefficient certificate.

## Proof Sketch

Push the rational embedding through the finite sum and its weights; real parts of embedded pairs are their first coordinates. Apply the actual coefficient-to-panel error theorem, reversing the norm difference where necessary.

## Lean Artifacts

`RationalThetaPanelFull.lean`: ratThetaApproxPanelValue_cast, ratThetaPanel_error.
