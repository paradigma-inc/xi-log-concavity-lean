# Exponential seed at source endpoint 5, panel (1,6), atom 4

## Statement

The stored state encloses the exponential of its exact rational input
within $10^{-90}$. Its transfer to the actual theta atom includes
the proved logarithm and pi errors through the relative-input bound.

## Assumptions

No numerical-value assumptions. The actual-atom theorem uses only
previously proved source pi and logarithm certificates. This one seed
is not a root, endpoint-sign, complete panel or zero-completeness certificate.

## Proof Sketch

The kernel checks the exact forty-term rational Taylor sum at input
divided by $65536$, followed by all sixteen rounded squarings, each
residual at most $2\cdot10^{-160}$. The analytic exponential error
theorem and relative transfer connect these finite checks to the actual
power-times-exponential atom at the unchanged source endpoint.

## Lean Artifacts

- File: `LowZeroSeedP5J1I6K4Full.lean`
- Main theorem: `lowZeroSeedP5J1I6K4_actual_atom_error`.
