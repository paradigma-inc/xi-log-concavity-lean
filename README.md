# Strict log-concavity of the reciprocal-Xi density

This repository contains the complete Lean formalization of
`ReciprocalXi.density_full_conclusions`, together with its mathematical sketches,
source data, build records, and independent final audit.

For

$$
F(z)=\tfrac14\xi(\tfrac12+iz/2),\qquad
\Lambda(x)=\frac1{2\pi}\operatorname{Re}\int_{\mathbb R}
\frac{F(0)}{F(iu)}e^{-ixu}\,du,
$$

the theorem proves that the density is smooth, even, strictly positive,
integrable with total mass one, and strictly log-concave on the whole real line.
It also proves strict positivity of its ordered two-by-two translation minors
(PF2). The final declaration has no remaining theorem hypotheses.

This result does not prove the Riemann hypothesis or positivity at every order.
The dated literature assessment is separate from formal verification and does
not certify priority.

## Read the proof

- [Final Lean theorem](theorem_pipeline/workspace/lean_project/ProofWorkspace/Final/ReciprocalXiDensityFull.lean#L706)
- [Mathematical sketch](theorem_pipeline/workspace/lean_project/ProofWorkspace/Final/ReciprocalXiDensitySketch.md)
- [All formal modules and paired sketches](theorem_pipeline/workspace/lean_project/ProofWorkspace/Final)
- [Final verification report](FINAL_VERIFICATION.md)
- [Independent final audit](EXTERNAL_ASTRA_FINAL_AUDIT.md)
- [Explanation and literature comparison](LITERATURE_REVIEW_20260911.md)
- [Packaging and validation notes](PACKAGING.md)

## Build and inspect foundations

The project pins Lean **4.28.0** and mathlib commit
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`; transitive dependencies are recorded in
`lake-manifest.json`.

With elan installed:

```sh
cd theorem_pipeline/workspace/lean_project
lake build
lake env lean -s131072 -M6000 AuditReciprocalXiDensityFinal.lean
```

The clean build checks a large collection of generated numerical certificates
and can require substantial CPU time. Installed dependencies and compiled
caches are excluded from this repository.

The recorded complete build and final axiom audit passed on 11 September 2026.
The final theorem uses only `propext`, `Classical.choice`, and `Quot.sound`.
The independent audit reviewed the proof, its dependencies, numerical
correspondence, and completed verification records; it did not perform another
clean rebuild.

The optional Python verification wrapper is included under `theorem_pipeline/`.
The Lean project can be built directly without it.

## Contents

The formal library contains **4,620 proof/sketch pairs** and the complete
cumulative import index. The distribution includes **4,625 Lean source files**,
including the Lake configuration, root module, and final axiom audit.
`LEAN_SOURCES.sha256` records their checksums relative to this repository root.
Exploratory scratch files, installed dependencies, compiled outputs, and
execution transcripts are excluded.
