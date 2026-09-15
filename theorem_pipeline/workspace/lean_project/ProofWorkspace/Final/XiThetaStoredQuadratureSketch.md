# Error of the stored thirty-two-panel sum

## Statement

If each stored panel approximates its exact forty-term Taylor integral within $320\cdot10^{-25}$, the stored sum approximates the exact quadrature within $10240\cdot10^{-25}$. Including the proved analytic truncation and Taylor errors gives absolute $F(48)$ error at most $3\cdot10^{-16}$.

## Assumptions

All thirty-two panel errors are explicit hypotheses. No particular stored sum or numerical endpoint is certified in this module.

## Proof Sketch

Apply the triangle inequality to the finite double sum. Propagate this error through the affine normalization of $F(48)$, multiplying by $2305/32$, then add the already proved $2\cdot10^{-16}$ error for the exact quadrature. Exact rational arithmetic bounds the total.

## Lean Artifacts

`XiThetaStoredQuadratureFull.lean`: theta48StoredQuadrature_error, F48_storedQuadrature_error.
