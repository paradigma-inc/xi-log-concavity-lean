# Credit-assignment audit: reciprocal-Xi PF2

Retrospective contribution audit — 9 September 2026

Public edition — 16 September 2026. The auxiliary model's internal name and infrastructure locations have been removed. The findings, task accounting, and limitations are retained. The original audit predates completion of the Lean formalization on 11 September; historical statements about verification below describe the state on 9 September. See [the final verification report](FINAL_VERIFICATION.md) for the completed formalization.

This is a retrospective model-contribution audit, not an allocation of human authorship or a controlled measurement of time saved. Raw internal prompts and candidate transcripts are not published here, so the public edition alone does not let readers independently reproduce every attribution.

## Finding

The documented argument was primarily developed by the Astra controller. The auxiliary model supplied some correct calculations and proof fragments, most clearly an explicit two-Laplace convolution kernel and a positivity argument. The records do not establish a decisive new idea, a complete major proof obligation, or a net speedup attributable to the auxiliary model.

That is narrower than saying the auxiliary model did nothing. Useful fragments were produced, but many were mixed with invalid steps, and several seemingly important formulas or strategies had already been supplied in the controller's prompts.

This concerns **the auxiliary model at checkpoint step100 and temperature 0.6**. It does not cover other checkpoints or benchmarks.

## Which result?

The [source result](https://flywheel.paradigma.inc/node/4cfbb696-be45-4073-9252-ea03c8f0a566) claims global strict log concavity of the reciprocal-Xi Fourier density. With the source's normalization,

$$
F(z)=\Xi(z/2)/4,\qquad \phi(u)=F(0)/F(iu),\qquad
\Lambda(x)=\frac{1}{2\pi}\int_{\mathbb R}\phi(u)e^{-ixu}\,du,
$$

the conclusion is

$$
\Lambda'(x)^2-\Lambda(x)\Lambda''(x)>0
\quad\text{for every real }x.
$$

This gives order-two total positivity, or PF2. It is **not a proof of the Riemann hypothesis or of total positivity at every order**. A separate AI-assisted mathematical/code review found no blocking error and reproduced the finite certificate, accepting the stated published finite-zero inputs. That is not human peer review, a novelty determination, or a completed Lean verification.

## How attribution was checked

The audit compared original task prompts, saved worker answers, contemporaneous controller judgments, and the resulting proof. The event log records prompts before worker responses, so a formula already present in a prompt cannot be credited as a worker discovery.

The controller's contemporaneous reviews cover all sixteen candidates below. This audit also directly checked selected answers against their prompts and the final argument, including 174/c0, 176/c1, 177/c0, 178/c0, and adjacent task 172/c1. It is **not a fresh independent line-by-line rescore of every statement in all sixteen answers**.

“Accepted” below refers to the controller's recorded assessment and documented use, not to a new blind judging experiment. Correct overlap with the final proof does not by itself show that a fragment was necessary or saved time.

## The eight direct requests

Each request produced two candidates. Candidate numbering is zero-based.

| Task | Requested work and the auxiliary model's response | Attribution to the resulting proof |
|---|---|---|
| 167 — positive probability law | Some correct verdicts, but the proposed construction was incomplete or invalid, strengthened assumptions, and incorrectly rejected self-decomposition. | No accepted complete proof. The controller supplied compound-Poisson truncations, tightness, and the limiting argument. |
| 168 — Gaussian-mixture density | Repeated the correct mixture formula, with invalid integrability/interchange reasoning. | The exact formula was already in the prompt. The controller supplied the justification; this was not a worker discovery. |
| 173 — contour-residue tails | Proposed a contour alternative with sign, normalization, contour, and remainder errors. | No accepted contribution from this route. The final argument instead uses positive convolution. |
| 174 — two-Laplace smoothing | Candidate 0 gave the correct explicit kernel and a valid positivity argument, but its regularity and quantitative curvature reasoning failed. | The clearest directly relevant worker calculation. The convolution strategy was already supplied; the controller supplied derivative remainder bounds and a valid tail threshold. |
| 175 — residual positive law | Made unsupported assertions about characteristic functions, infinite divisibility, and exponential moments after removing two factors. | No accepted complete argument. The controller proved positivity of the residual inverse-Laplace sum and constructed the measure. |
| 176 — zero-free strip | Candidate 1 began with a correct inequality, then used invalid estimates. | The initial inequality and the two-range strategy were already in the prompt. The controller supplied valid estimates and constants. |
| 177 — Taylor/curvature certificate | Candidate 0 contained a valid scalar Taylor-remainder fragment, but its common derivative bound was invalid; neither candidate supplied a valid curvature certificate. | Limited routine assistance. The target error expression was already supplied; the controller handled scaling and cross terms. |
| 178 — Euler-eta evaluator | Candidate 0 correctly interpreted binomial-tail weights and began the finite-sum swap, but obtained the wrong generating function and remainder. | A small algebraic fragment, not the certificate's critical identity. The controller corrected the polynomial identity and derived the rigorous positive remainder. |

### Concrete example: a useful calculation with an invalid conclusion

In task 174/c0, for rates $0<a<b$, the auxiliary model correctly obtained

$$
K(x)=\frac{ab}{2(b^2-a^2)}
\left(b e^{-a|x|}-a e^{-b|x|}\right).
$$

This is useful, as was its positivity argument. But the answer also treated individual Laplace densities as twice continuously differentiable despite their cusp, inferred derivative bounds from function bounds, and claimed a curvature lower bound proportional to $e^{-2ax}$.

The last claim fails even without a residual convolution: writing $C=ab/[2(b^2-a^2)]$, for $x>0$,

$$
K'(x)^2-K(x)K''(x)
=C^2ab(b-a)^2e^{-(a+b)x}.
$$

Because $b>a$, this cannot be bounded below by a fixed positive multiple of $e^{-2ax}$ for all large $x$. The controller had to replace the quantitative argument, rather than simply adopt the answer.

### Concrete example: the important formula was already supplied

Task 168's Gaussian-mixture formula and task 176's starting strip inequality were in their respective prompts. Correctly repeating or beginning to manipulate them is evidence of execution, not evidence that the auxiliary model discovered those steps. Both answers still needed substantial justification or correction.

### Concrete example: the certificate required a correction

Task 178/c0 made a correct start on the finite-sum manipulation but did not obtain the identity needed for the evaluator. The final proof uses

$$
\sum_{j=0}^{N-1}(-1)^j w_j x^{j+1}
=\frac{x}{1+x}\left[1-\left(\frac{1-x}{2}\right)^N\right],
\quad
w_j=2^{-N}\sum_{k=j+1}^{N}\binom Nk.
$$

The corrected identity gives a positive integral remainder and its bound. The records attribute that correction and rigorous remainder to the controller, not to the worker's completed answer.

## Nearby exploratory work, counted separately

Tasks 169–172 explored related rational-kernel lemmas. They should not be presented as four additional direct dependencies of the final actual-Xi proof.

- **169/c1:** correct inverse partial fractions.
- **170/c1:** correct one-anchor inverse formula.
- **171/c1:** useful checked decomposition, limits, and algebra; much of the decomposition was already supplied.
- **172/c1:** a substantially correct nonstrict local primitive log-concavity argument along the supplied identity and route. Strictness was incomplete and the proposed application was wrong; the controller repaired those parts.

These support the more modest finding that the auxiliary model can supply useful local calculations and proof fragments. They do not establish that it discovered the global Xi argument.

## Recorded usage and outcome

| Measure | Direct task group |
|---|---:|
| Requests | 8 |
| Candidates | 16 |
| Completion tokens, including reasoning and final output | 235,317 |
| Candidates recorded completed with normal stop | 16 |
| Complete proofs accepted in the contemporaneous controller reviews | 0 |

Completion-token totals by task: 167: 38,315; 168: 24,450; 173: 29,796; 174: 22,699; 175: 25,606; 176: 22,419; 177: 31,199; 178: 40,833.

No truncation or retry is recorded for this group. The model settings were step100, temperature 0.6, top_p 1.0, and repetition penalty 1.15. These are worker completion tokens, not total controller-plus-worker cost. Candidate latencies must not be added and reported as elapsed time because requests/candidates can overlap.

Zero accepted complete proofs is **not a zero mathematical-quality score for every fragment**, nor a measured causal contribution of zero.

## What we can and cannot conclude

**Supported:** Astra supplied the decisive residual-measure argument, repaired tail estimates, strip constants, and the rigorous numerical certificate. The auxiliary model supplied several usable fragments, with the task-174 kernel calculation the clearest direct example. Substantial verification and correction were necessary.

**Not measured:** net controller time saved, whether Astra would have reached the same result at the same speed without the auxiliary model, or the marginal value of each accepted fragment. There was no matched Astra-only replay of this exact derivation. The separate Astra-only research lane is not that counterfactual.

The defensible description is: **some useful calculation assistance, but no demonstrated decisive discovery or net end-to-end benefit in this result.** This is an attribution finding, not a checkpoint ranking or a general judgment of the auxiliary model's usefulness.

## Evidence pointers

The audit was read-only; no experiment was rerun and no job or graph was changed.

- Main result: https://flywheel.paradigma.inc/node/4cfbb696-be45-4073-9252-ea03c8f0a566
- Positive-law prerequisite: https://flywheel.paradigma.inc/node/ddd3eaa1-2995-4544-8748-debd25b87249
- Tail prerequisite: https://flywheel.paradigma.inc/node/326d0d8a-69d3-49c4-b4d0-3dd2601c6cab
- Source proof SHA-256: `94803cce901cb84ed6714903e37a967852a1d0b3158d2f1bcb83c075b9079444`.
- Internal run location omitted from this public edition. The underlying execution records are not included in this repository.
- Internal evidence consists of `workspace/problems/`, `workspace/results/status_NNN.json`, `workspace/WORKER_NOTES.md`, `workspace/RECOVERY.md`, and `turns/000008.events.jsonl`.
- Raw candidate/request records: `workspace/workers/000009/broker/<request-id>/`.

| Task | Request ID |
|---|---|
| 167 | `4e70bf79576c450b95b95b07a4d4b969` |
| 168 | `37eee4e6570c431784b68e92ef1db253` |
| 173 | `d430edaed81c4560ba301e83e8fd5f80` |
| 174 | `f2cfcfd88c1043a1a371cb1944e5ad04` |
| 175 | `49c9b391fb0d4d06bf11a2f977be8bb2` |
| 176 | `4ed6cb75c4dc4631afa80e55f6763c32` |
| 177 | `5ff4060e613e44b09d834a7f0f0e2548` |
| 178 | `abb3b49c4e2d4c909e84fbb376816bb8` |

The separate proof-review packet concerns correctness and certificate reproduction; this report concerns worker attribution.
