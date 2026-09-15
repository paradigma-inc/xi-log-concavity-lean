# Independent final audit: reciprocal-Xi density

**Verdict: PASS for the exact density theorem stated below.** No blocking mathematical, statement-correspondence, assumption, numerical-input, or final-assembly defect was found in this review. This is a final-claim audit, not adoption of either earlier interim Astra review. It does not certify RH, PF-infinity, priority, or novelty.

Reviewer: independent `final_astra_xhigh_audit` agent, assigned as Astra xhigh, 11 September 2026. I did not author or edit the Lean proof sources, rerun cluster work, contact other user-owned tasks, or use a cloud service. The sole artifact added by this audit is this report. I used the `flywheel-prove` skill's artifact, source-context, and verification conventions where applicable to a review of an existing completed pipeline.

## Exact statement and definitions

The target is `ReciprocalXi.density_full_conclusions`, at line 706 of [ReciprocalXiDensityFull.lean](theorem_pipeline/workspace/lean_project/ProofWorkspace/Final/ReciprocalXiDensityFull.lean), with [ReciprocalXiDensitySketch.md](theorem_pipeline/workspace/lean_project/ProofWorkspace/Final/ReciprocalXiDensitySketch.md) as its sidecar. It asserts, with no theorem parameters or hypotheses:

\[
F(z)=\tfrac14\xi(\tfrac12+iz/2),\qquad
\Lambda(x)=\frac{1}{2\pi}\operatorname{Re}\int_{\mathbb R}
\frac{F(0)}{F(iu)}e^{-ixu}\,du,
\]

and that this density is smooth, even, integrable, has integral one, is positive at every real point, and satisfies

\[
(\Lambda'(x))^2-\Lambda(x)\Lambda''(x)>0
\quad\text{for every }x\in\mathbb R.
\]

The remaining conjuncts are `StrictConcaveOn ℝ Set.univ (fun x ↦ Real.log (density x))` and the strictly positive determinant

\[
\Lambda(x_1-y_1)\Lambda(x_2-y_2)
-\Lambda(x_1-y_2)\Lambda(x_2-y_1)>0
\quad(x_1<x_2,\ y_1<y_2).
\]

I checked the actual definitions, not only these descriptions. `XiDefinitionFull.lean` defines xi using mathlib's pole-removed completed Riemann zeta, proves agreement with the usual completed-zeta formula away from 0 and 1, and supplies the removable values. `F` uses the stated argument and factor of four. `F_imaginary_axis` explicitly uses the functional equation to reconcile the apparent minus sign in `F(iu)` with `xi((1+u)/2)/4`. `density` is exactly the displayed real part of a Bochner integral, with the negative exponential and denominator `2 * Real.pi`. `curvatureJet` is explicitly `v1 ^ 2 - v * v2`.

Thus the conclusion concerns the actual inverse-Fourier density, rather than an abstract function with the desired properties. The totality of Lean's integral and derivative operators does not make this proof vacuous: the actual Fourier integrability, smoothness, denominator nonvanishing, and probability normalization are proved. The final statement has neither a remaining certificate hypothesis nor a hidden zero-location premise.

## Critical mathematical connections

I traced the final proof through the following connections, examining the substantive definitions and proofs at these interfaces. Generated arithmetic leaves were assessed by their checkers, source correspondence, compiled dependency inclusion, and axiom records rather than by manually recalculating each leaf.

1. **Actual Fourier regularity.** `XiFourierFull.lean` proves positivity and nonvanishing on the real xi axis, integrability of every exponentially weighted reciprocal transform, and consequently all polynomial Fourier moments. The Fourier-to-density identity retains the `x/(2*pi)` frequency conversion. `contDiff_density` follows from the actual Fourier differentiation theorem. `XiSymmetryFull.lean` supplies integral reflection and the resulting density and derivative parity.

2. **Actual zeros, including multiplicity.** `XiPairedProductFull.lean` indexes zeros by `Σ z : FZero, Fin (analyticOrderNatAt F z.val)` and then restricts to positive real coordinate. It proves summability and convergence of the paired product over those occurrences. `XiPairedQuotientFull.lean`, the quotient-growth chain, and `XiProductIdentityFull.lean` connect that product to `F`. In particular, `F_eq_pairedProduct` is an unconditional equality about actual xi. Neither a supplied zero list nor RH is a parameter of that identity.

3. **The three-zero certificate is inhabited.** `XiMomentSamplesFull.lean` relates the 33 rational logarithm samples to actual reciprocal xi using proved sample and logarithm errors. `XiMomentBootstrapFull.lean` obtains the first and second moment bounds and excludes occurrences of real coordinate at most 24. `XiMomentExtractionFull.lean` uses exact coefficient-extraction identities and a proved Taylor remainder to bound the sixteenth moment. `XiMomentResidualFull.lean` proves that a further occurrence at real coordinate at most 60 would exceed the allowed scaled residual of `7/10`. `XiMomentRootCertificateFull.lean` first obtains one real zero in each original interval from the actual endpoint signs, then proves occurrence-level exhaustion and simplicity. The final module supplies all six endpoint signs. This closes the premise that was still explicit in the normalized source and earlier reductions; it does not assume an externally classified list of zeros.

4. **A probability law for the residual factor.** `XiModerateHeatFull.lean` bounds the negative contribution from the remaining occurrences above 60. The third real occurrence leaves a positive lower bound of `exp(-c^2*t)/36` for the residual heat trace. `XiSelectedResidualLawFull.lean` constructs its law using a heat subordinator and a Gaussian variance mixture. The probability and characteristic-function results require heat nonnegativity, which `XiMomentDensityBridgeFull.lean` supplies from the now-inhabited certificate. `XiResidualMomentFull.lean` and the Levy exponential-moment chain establish genuine integrability of exponential moments before `XiResidualQuotientFull.lean` identifies the moment with the analytic quotient. This avoids inferring moment existence merely from continuation of a transform.

5. **Positivity and unit mass of the same density.** `XiDensityConvolutionFull.lean` proves pointwise equality between `density` and the convolution of that residual probability law with the normalized two-Laplace kernel. The two factors are deleted at distinct, proved real zero occurrences. `XiDensityNormalizationFull.lean` integrates the normalized kernel and convolution, proving both integrability and integral one. Strict positivity uses the positive convolution kernel and a probability law; it is not assumed in this representation.

6. **Compact analytic enclosures.** The finite trapezoid and sampled-quadrature chain bounds the complex density on a complex neighborhood, and `DensityTaylorErrorFull.lean` and `RealTaylorBridgeFull.lean` transfer Cauchy/Taylor bounds to the first two actual real derivatives with the correct `1/200` and `(1/200)^2` scaling. `ActualPanelEnclosuresFull.lean` supplies these fields to `DensityCompactEnclosures`. `SourcePanelCheckerFull.lean` bounds the polynomial coefficient perturbation and compares it to the original recorded fields. `sourceDensityCompactEnclosures` in the final module supplies both the complete sample-error theorem and all panel checks. The proof does not infer derivative bounds from sampled real values alone.

7. **Tail coverage and global conclusion.** `XiThetaCertifiedQuadratureFull.lean` proves the original enclosure `529169286414/10^18 < Re(F(48)) < 529196177592/10^18`. The bridge retains `R=48`, the residual square gap at 49, and moment cap 268341. `SourceTailOverlapFull.lean` proves the tail threshold is at most 3.18. `DensityConditionalFull.lean` glues this tail with the compact interval, using evenness for the negative axis. `GlobalReductionFull.lean` differentiates the logarithm using positivity and actual derivatives, then derives the correctly oriented ordered translation determinant.

The conditional intermediate structures are legitimate interfaces: the final module constructs or supplies every required input. Historical comments saying that an input remains unproved describe those modules in isolation and do not introduce a hypothesis into the completed theorem.

## Independent numerical and dependency checks

I performed additional read-only checks independently of the summary JSON files:

- Compared all **1,485 baseline Full files** against the saved beginning-of-run snapshot by SHA-256: no changes or missing files.
- Checked all **282 frozen source entries** and the frozen numerical-data entry in `cluster_cpu_91a4/manifest.json`: all hashes match.
- Decoded both original-evidence and reproduction gzip node tables. Their **24,001 decoded rows are identical**, despite different gzip-container hashes. Independently reproduced the 160-significant-digit half-even addition/division used for the midpoint and compared all **13,601 retained Lean midpoint literals**: every value and index matches both source copies.
- Compared all three exact recorded margin fields and panel centers in `RecordedMarginsFull.lean` against both compact JSON reports: **318 of 318 match**, and every integer margin is positive. The recorded margin data alone would not establish its analytic meaning; the enclosure and stream proofs above provide that connection.
- Checked that the three stored upper root endpoints equal twice the original displayed ordinate plus `2*10^-29`. The lower-endpoint definition subtracts `4*10^-29`, giving precisely the requested doubled original intervals.
- Inspected the source-block assembly, including the exceptional removable value at grid index 40 and the final one-entry block at 13600. The final theorem is an actual bound of `2/10^120` for every index below 13601.
- Inspected the panel generator and checkpoint composition. The final stream is connected to the frozen array by exact seed, zero-accumulator, and 54 consecutive transition checks, covering offsets 0 through 13601 and all 65 coefficients. Generated candidate vectors become evidence only through `decide +kernel` and the equality/rounding lemmas.
- Reconstructed the final module's local import closure: **4,615 modules**, no missing local imports, containing **all 318 panel Stream modules and all six endpoint modules**. The final source-bound assembly is included. Importing a panel-margin theorem without connecting it to the full stream is not what this assembly does.
- Recounted **4,620 Full/Sketch pairs**, with no missing sketch; **34,593 public theorem/lemma declarations**; and an exact cumulative index of **4,621 distinct project modules**, including the final theorem. The root target imports that index. The staging directory is absent.

These checks preserve the original samples, error, intervals, margins, and normalization. Several analytic arguments are stronger or use a different internal derivation than the narrative source, especially the replacement of external low-zero completeness by the moment argument. The requested conclusion and numerical inputs have not been weakened.

## Verification and foundations

The completed records inspected were:

| Record | Observed result |
|---|---|
| `theorem_pipeline/logs/91a4_full_assembly_scratch.log` | Exit 0, 43.43 seconds |
| `theorem_pipeline/logs/91a4_full_assembly_final.log` | Successful final-module build, 8,185 Lake jobs, exit 0, 53.72 seconds |
| `theorem_pipeline/logs/91a4_full_assembly_axioms.log` | All six final declarations, exit 0, 84.39 seconds |
| `theorem_pipeline/logs/verify_20260911T151936Z.log` | Successful cumulative build, 8,194 Lake jobs; no appended sorry/staging failures |

I inspected `tproof.cli.verify`: it requires build success, no unresolved sorry hits, and no forbidden staging artifacts. I also independently checked index inclusion and staging absence. The Lake job counts include dependencies and replayed cached work; they are not counts of newly compiled files. Replayed linter warnings do not indicate an incomplete proof.

The scratch and final proof bodies are byte-identical after their descriptive first comment. The direct audit imports the final module and names all six declarations, including the proof-valued definition `sourceDensityCompactEnclosures`. Each appears exactly once in that log, and each has only:

`propext`, `Classical.choice`, `Quot.sound`.

I independently extracted **26,714 distinct new audited public names**, including the final proof-valued definition, and found every one in the preserved raw axiom outputs, with no unapproved axiom in any matching record. The preserved retry history repeats 720 names; these repetitions are not missing or extra source declarations. The controller's numerical inventory describes its selected exactly-once subset. My independent raw-log coverage check did not discard the retry history or count only proposed names.

The source inspection found no custom axiom, `sorryAx`, unsafe declaration, `native_decide`, or custom elaboration escape in the project modules. The final declaration's transitive axiom report is the central foundation check; successful arithmetic-generation scripts alone would not suffice.

The pinned toolchain is Lean 4.28.0. The installed mathlib Git HEAD is `8f9d9cff6bd728b17a24e163c9402775d9e6a365`, matching the Lake pin, and its working tree is clean.

Artifact hashes at review:

- Final theorem: `b1eca3f8af78a483d2a008fd0e1a3343ed7a38be9298cac53200e6080e053350`.
- Final sketch: `998cf6356bc52c80dd080af666df4ff6333ed85798adba9f4dcb1688af75524c`.
- Final-module build log: `d24621a8a6beb56bf06669597e574a8e4dc937ade012e0aa163535b960f209ab`.
- Final axiom log: `a57ac0211dd983a34c417a24336607d2ef7fe2b39190bac23f41a23d7d733919`.
- Cumulative verification log: `acc7a4d16716e0208ab84a4cc8e5330a195ac7c6608fc18555574a9414eee8a9`.

## Scope and limitations

This is an independent source, dependency, data-correspondence, and completed-verification-record audit. I did not independently clean-build all 4,620 modules or manually rederive every generated arithmetic calculation. It relies on the recorded successful Lean checks and their ordinary trusted kernel/library/toolchain boundary. The direct final axiom audit and actual dependency inclusion provide stronger evidence than a file count or a successful generator run alone.

The normalized source remains a historical record of the originally conditional argument. Its cautions about external zero inputs should not be mistaken for hypotheses of the final Lean theorem. Conversely, this PASS should not be extended to all statements in the surrounding research notes or to any RH/PF-infinity claim.

As an operational consistency check, the saved parent-allocation accounting totals **800,916 allocated logical CPU-seconds**, with no GPU entry and only terminal states. Repeated job IDs represent the retained allocation/preemption history. I did not query the live cluster. TIMEOUT, preemption, and cancellation records were not treated as mathematical failures or silently relabeled successful computations.

At review time the run is `20260911T014556Z_remaining-numerical-certificates_91a4`, status `VERIFIED_PENDING_EXTERNAL_AUDIT`. This report supplies that final independent audit; updating the run and final handoff from pending is the controller's remaining administrative action.

Final artifact directory: `theorem_pipeline/workspace/lean_project/ProofWorkspace/Final/`.
Normalized source: `theorem_pipeline/workspace/contexts/reciprocal_xi_global_logconcavity.md`.
Main theorem: `ReciprocalXi.density_full_conclusions`.
Final verification log: `theorem_pipeline/logs/verify_20260911T151936Z.log`.

**SUCCESS — PASS for the exact unconditional reciprocal-Xi density theorem, within the review scope above.**
