# Dyadic theta-center logarithms

## Statement

The rational midpoint for the logarithm of each center $c=(17+2i)2^j/16$ has absolute error at most $(j+1)10^{-70}$, hence at most $4\cdot10^{-70}$ for the thirty-two panels. The midpoints lie in $[0,3]$.

## Assumptions

Here $i\in\{0,\ldots,7\}$ and, for the uniform bound, $j<4$. The nine base logarithm certificates are proved in XiThetaLogSeedsFull.

## Proof Sketch

Use $\log c=j\log2+\log((17+2i)/16)$ and add the already certified midpoint errors with the triangle inequality. The finite rational midpoint bounds are checked directly.

## Lean Artifacts

`XiThetaPanelLogFull.lean`: thetaLogBaseSeed_error, thetaLogBaseSeed_bounds, theta48PanelLogSeed_error, theta48PanelLogSeed_error_uniform, theta48PanelLogSeed_bounds.
