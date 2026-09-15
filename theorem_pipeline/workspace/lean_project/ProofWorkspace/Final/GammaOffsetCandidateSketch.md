# Gamma offset candidate

## Statement

`gammaOffsetCandidate` exposes the accepted exact rational construction for
the lower and upper logarithmic Gamma endpoints at any rational offset $z$.
`gammaOffsetCandidate_eq` identifies it with the existing fast Gamma-log
construction for the exact 440-row Gamma/zeta table.

## Scope

This is a shared construction for later residue-class checks.  It does not by
itself certify any retained Fourier node.  Individual residue literals are
checked separately with ordinary kernel reduction.

## Lean Artifacts

- Full proof: `ProofWorkspace/Final/GammaOffsetCandidateFull.lean`.
- Theorem: `gammaOffsetCandidate_eq`.
