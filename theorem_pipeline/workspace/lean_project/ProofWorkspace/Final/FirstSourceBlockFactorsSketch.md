# Actual elementary factors for the first source block

## Statement

For every $0\le k<160$, the stored eta, pi-power, and base-two-power endpoints enclose the corresponding actual real functions. A residue index below $160$ identifies the exact Gamma offset for every natural grid index.

## Assumptions

The first-block enclosure statements assume only the stated grid-index range. They reuse kernel-checked endpoint data and previously proved analytic enclosures. No actual Xi sample-accuracy conclusion is asserted yet.

## Proof Sketch

The eta selector dispatches to the three certified, adjacent batches. Their canonical index identities eliminate the local offsets. The pi-power and base-two table equalities substitute the stored rational pairs into the already established actual-function bounds. Elementary rational arithmetic identifies the Gamma offset with its shared residue, including the initial branch where Gamma recurrence requires an inverse multiplier.

## Lean Artifacts

- File: ProofWorkspace/Final/FirstSourceBlockFactorsFull.lean
- Theorems: sourceFirstEta_enclosure, sourceFirstPi_enclosure, sourceFirstTwo_enclosure, sourceGammaResidueIndex_lt, gammaGridOffset_eq_residue.

