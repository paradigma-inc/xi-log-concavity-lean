# Reciprocal-Xi density — final verification

Status: **COMPLETE — formal proof verified; independent Astra xhigh audit PASS**.
Run: `20260911T014556Z_remaining-numerical-certificates_91a4`,
`COMPLETE`.

## Start here if you do not work on RH

We proved a shape property of a curve built from the reciprocal of the xi
function, a function connected to the Riemann hypothesis (RH). The curve is
positive, symmetric and has total area one. On a logarithmic vertical scale,
it bends strictly downward everywhere—this is called strict log-concavity.
The proof covers the whole real line, not just sampled points, and does not
assume RH.

The RH connection involves a family of matrix tests built from values of this
curve. Our result establishes all the two-by-two tests. RH would require all
sizes; this result does not automatically extend to larger matrices.
**We have not proved RH.**

The full proof passes Lean's checker, and an independent AI review found no
blocking issue. A separate literature review found no earlier proof of the
exact result among the works examined; that is not yet a confirmed first proof.
Read the [plain-language explanation and literature comparison](LITERATURE_REVIEW_20260911.md)
for the background, the limits of each check, and the cited RH connection.
The formulas and reproducibility evidence below provide the technical details.

## Proved statement

For
$$
F(z)=\xi(1/2+iz/2)/4,\qquad
\Lambda(x)=\frac1{2\pi}\operatorname{Re}\int_{\mathbb R}
\frac{F(0)}{F(iu)}e^{-ixu}\,du,
$$
`ReciprocalXi.density_full_conclusions` proves, **without theorem hypotheses**:

- smoothness and evenness;
- integrability and total integral one;
- strict positivity at every real point;
- $\Lambda'(x)^2-\Lambda(x)\Lambda''(x)>0$ everywhere;
- strict concavity of $\log\Lambda$;
- positive ordered two-by-two translation minors (PF2).

This is the actual standard xi / inverse-Fourier density, not an abstract or
fitted replacement. **No RH or PF-infinity claim is made; formal verification
does not certify novelty.**
The reviewed source used published finite zero data. The formalization
discharges that input through checked endpoint signs and the proved finite
moment/zero-occurrence argument, rather than leaving it as an assumption.

## Primary artifacts

- [Full Lean proof](theorem_pipeline/workspace/lean_project/ProofWorkspace/Final/ReciprocalXiDensityFull.lean)
- [Mathematical proof sketch](theorem_pipeline/workspace/lean_project/ProofWorkspace/Final/ReciprocalXiDensitySketch.md)
- [Normalized source](theorem_pipeline/workspace/contexts/reciprocal_xi_global_logconcavity.md)
- [Plain-language explanation and literature review — 11 September 2026](LITERATURE_REVIEW_20260911.md)
- Final directory: `theorem_pipeline/workspace/lean_project/ProofWorkspace/Final/`.

## Literature assessment (separate from proof verification)

The [dated supporting review](LITERATURE_REVIEW_20260911.md) reports no
established prior proof of this exact unconditional strict-log-concavity
statement in the literature examined. Its assessment is **apparently new /
novelty candidate, pending specialist confirmation**, not a certified first
proof. It compares the same density in Gröchenig with nearby results about
complete monotonicity, coefficient positivity and the ordinary theta kernel.
The proof audit's novelty disclaimer was a scope boundary, not a finding
that the theorem was already known. The audit itself remains unchanged;
this addendum is not a new mathematical verification or priority certificate.

## Verification evidence

| Check | Result | Evidence |
|---|---|---|
| Original source accuracy | 13,601 / 13,601 at unchanged error | [Source-grid audit](theorem_pipeline/logs/91a4_source_grid.axioms.log) |
| Original endpoint signs | 6 / 6 | [Endpoints 2–5](theorem_pipeline/logs/91a4_endpoints2to5.resume1.log); 0–1 accepted in ee5a |
| Original compact panels | 318 / 318 | Local panel logs and [cluster collections](cluster_cpu_91a4/RUN.md), including batches 1–10 |
| First complete assembly | exit 0, 43.43 s | [Scratch check](theorem_pipeline/logs/91a4_full_assembly_scratch.log) |
| Final module | exit 0, 8,185 jobs, 53.72 s | [Final build](theorem_pipeline/logs/91a4_full_assembly_final.log) |
| Final six-declaration axiom audit | exit 0, 84.39 s | [Direct audit](theorem_pipeline/logs/91a4_full_assembly_axioms.log) |
| Cumulative reindex and verification | exit 0, 8,194 jobs | [Whole-project build](theorem_pipeline/logs/verify_20260911T151936Z.log) |
| Independent Astra xhigh audit | PASS, no blocking findings | [Independent final report](EXTERNAL_ASTRA_FINAL_AUDIT.md), reviewer `final_astra_xhigh_audit` |

The independent final review checked source, dependencies, original numerical
correspondence and completed Lean verification records; it was not a fresh
clean rebuild of all modules. It approves only the exact density theorem,
not RH, PF-infinity, priority or novelty. The final proof, sketch and three
final verification-log hashes still match those recorded by the auditor.

All six final declarations appear exactly once in the direct audit:
`originalLowRootSigns_checked`, `density_probability_normalization`,
`sourcePanelStreams_checked`, the proof-valued definition
`sourceDensityCompactEnclosures`, `density_global_conclusions`, and
`density_full_conclusions`. Their only axioms are Lean's standard
`propext`, `Classical.choice`, and `Quot.sound`.

The final directory contains **4,620 Full/Sketch pairs** and **34,593 public
theorem/lemma declarations**. The cumulative import index contains exactly
all 4,621 modules beneath `ProofWorkspace/` other than the index itself,
including the final theorem;
the root target imports that index. The 3,134 pre-assembly new modules'
26,708 actual public names match the selected saved audits exactly once.
Adding the six assembly declarations gives **26,714 new audited declarations**,
including its proof-valued definition.
[Numerical inventory](theorem_pipeline/logs/91a4_numerical_inventory_validation.json)
and [final inventory](theorem_pipeline/logs/91a4_final_inventory_validation.json).

All 1,485 accepted baseline Full files remain byte-identical. Final and
scratch proof bodies match except their descriptive first comment.
Verification found no unresolved `sorry` or forbidden staging artifacts;
the staging directory is absent. No custom axiom, `sorryAx`,
`native_decide`, or unsafe declaration occurs in the project sources.
The build contains replayed nonblocking linter warnings.

## Reproducibility

Pinned Lean **4.28.0**, compiler commit
`7e01a1bf5c70fc6167d49c345d3bf80596e9a79b`;
mathlib `8f9d9cff6bd728b17a24e163c9402775d9e6a365`.
Original normalized source SHA-256:
`94803cce901cb84ed6714903e37a967852a1d0b3158d2f1bcb83c075b9079444`.
Original numerical data SHA-256:
`f37fe959487881151234e89d44745e8fca746203f0f151e460e1494323114724`.

From `theorem_pipeline/`, run `uv run -m tproof.cli verify`.
From its `workspace/lean_project/`, the final direct audit is
`lake env lean -s131072 -M6000 AuditReciprocalXiDensityFinal.lean`.
Cluster-produced portable Lean caches were independently matched to exact
sources and validated locally by Lake. No Linux native objects or credentials
were imported.

## Compute and interruptions

All tracked cluster jobs are terminal and the queue is empty. Exact total:
**800,916 allocated logical CPU-seconds** (222.476666… CPU-hours), **zero GPU
allocation**. [Parent-only accounting](cluster_cpu_91a4/final-accounting.psv)
includes setup, all preempted/time-limited attempts, successful resumptions,
and intentional cancellations once; Slurm step rows are not double-counted.
This is allocated CPU time, not measured utilization. Local CPU time is not
included in this Slurm total.

The only manual array resume was the 32 exact time-limited tasks, once, with
unchanged proofs, inputs, resources and finite limits. Twenty existing
certificates were reused without proof reruns; twelve completed through the
same cache-aware driver. Earlier failed/interrupted allocations were not
reported as successful allocations. Their logs remain under
`cluster_cpu_91a4/collected/`. No mathematical bound was changed or tuned.

SUCCESS
