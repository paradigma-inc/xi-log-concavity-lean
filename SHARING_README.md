# Reciprocal-Xi density: Lean proof and supporting evidence

This bundle accompanies Francesco's announcement in #open-problems.
The result is `ReciprocalXi.density_full_conclusions`: the actual reciprocal-Xi
inverse-Fourier density is smooth, even, positive, has integral one, is strictly
log-concave, and has strictly positive ordered 2-by-2 translation minors.
There are no remaining theorem hypotheses. This is not a proof of RH or of
total positivity at all orders, and no novelty claim is made.

## Start here

- `FINAL_VERIFICATION.md`: exact claim, checks, toolchain pins and accounting.
- `EXTERNAL_ASTRA_FINAL_AUDIT.md`: independent Astra xhigh final PASS.
- `theorem_pipeline/workspace/lean_project/ProofWorkspace/Final/ReciprocalXiDensitySketch.md`: readable mathematical argument.
- `theorem_pipeline/workspace/lean_project/ProofWorkspace/Final/ReciprocalXiDensityFull.lean`: final theorem (line 706).

The archive includes every project Lean module and matching proof sketch,
the pinned Lake configuration, original normalized source and numerical data,
the final scratch/module/cumulative build logs, the final direct axiom log,
the two inventory validation records, and parent-only Slurm accounting.
It includes no credentials, model conversations, installed dependencies,
compiled caches or native binaries. The final report also references earlier
per-panel logs retained in the original workspace; this compact bundle does
not contain all historical logs or interrupted cluster attempts.

## Verification scope

The complete cumulative Lean build passed. The final declaration's transitive
axioms are only `propext`, `Classical.choice`, and `Quot.sound`; there are no
custom axioms, unresolved `sorry` placeholders or `native_decide` shortcuts.
All 13,601 retained source bounds, six endpoint signs and 318 interval panels
were proved at the original error bounds and margins.

The independent Astra xhigh reviewer checked source, dependencies, numerical
correspondence and completed verification records. It did not perform a fresh
clean rebuild. Human specialist review and a literature/novelty assessment are
separate from the completed formalization and AI audit.

## Rebuild

Lean 4.28.0 and mathlib commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`
are pinned in the included project. With elan installed, enter
`theorem_pipeline/workspace/lean_project/` and run `lake build` to fetch the
pinned dependencies and check the project. Rebuilding the generated numerical
proofs from scratch is computationally substantial; the short recorded final
assembly build used previously checked caches. Once built, run:

```sh
lake env lean -s131072 -M6000 AuditReciprocalXiDensityFinal.lean
```

The included Python pipeline is optional: from `theorem_pipeline/`, with uv
installed, `uv run -m tproof.cli verify` also checks for unresolved proof
placeholders and forbidden staging artifacts after the build.

Run `20260911T014556Z_remaining-numerical-certificates_91a4`: COMPLETE.
