# What we proved, how it relates to RH, and whether it was already known

Date: **11 September 2026**.

The proof is complete and checked in Lean. **The result may be new, but we have
not established that nobody proved it before.** The explanation below needs
no background in the Riemann hypothesis; formulas and detailed references follow.

## The short version

We proved a precise shape property of a curve built from a mathematical
function connected to the Riemann hypothesis. Earlier work showed that this
curve offers another way to formulate RH: it would have to pass a whole
family of increasingly large matrix tests. We have proved the two-by-two
level, for every choice of the points involved. **That is not enough to prove
RH.** Our literature review has not located an earlier proof of this exact
result, but a specialist should check that conclusion.

## What is RH, and what is this curve?

The Riemann hypothesis, or **RH**, is a famous conjecture about the zeta
function, a function closely connected to the distribution of prime numbers.
It says that certain zeros—inputs where the function equals zero—all lie on
one particular line in the complex plane.

The **xi function** is a standard reformulation that preserves the zeros
relevant to RH. Our curve is not xi itself. We take a reciprocal, meaning
one divided by an expression involving xi, and apply an inverse Fourier
transform: a standard mathematical operation that turns a frequency-side
description into a function of position. The result is the curve called
the **reciprocal-Xi density** in the technical sections.

## What did we prove about it?

The curve is smooth, symmetric about zero, and positive everywhere. Its total
area is one, so it is a probability density. The central shape result is
**strict log-concavity**: on a logarithmic vertical scale, the curve bends
strictly downward everywhere. This is stronger than simply having one peak;
it does not say that the curve is Gaussian.

The result applies to the entire real line, not just a plot or sampled
points. The proof combines checked numerical bounds on finite intervals
with mathematical estimates for the infinite tails. It does not assume RH.
That is what **unconditional** means here.

## Why is it relevant to RH—but not a proof of RH?

Gröchenig's Theorem 4 relates this same curve, up to a change of scale, to
RH. Form matrices from shifted values of the curve and test whether their
determinants are nonnegative. RH is equivalent to passing these tests at
**every matrix size and every allowed choice of points**.
[Theorem 4](https://arxiv.org/html/2007.12889).

We prove positivity of the curve and strict positivity of all ordered
two-by-two determinants. Mathematicians call this **PF2**. Positivity at all
sizes is called **PF-infinity**. Passing every two-by-two test does not
automatically give the three-by-three tests, let alone all larger sizes.
This is one level of an RH-equivalent condition, not a known percentage of
the work needed to solve RH. We claim no new conclusion about prime counts here.

## Three separate questions

| Question | Where we stand |
|---|---|
| Is the stated result proved? | The complete formal proof passes Lean's checker, without unfinished proof placeholders or extra assumed results. |
| Does the formal statement match what we intended? | An independent Astra xhigh AI review found no blocking mismatch in the definitions, numerical inputs or proof connections. It reviewed source and recorded checks, not another clean rebuild. |
| Is the result new? | We found no prior proof of the exact statement in the literature reviewed. That is evidence worth following up, not proof that no such publication exists. |

Lean checks a precisely written mathematical argument. It does not search the
literature, decide whether a theorem is important, or certify who proved it
first. The independent AI review is also not human specialist review.

## What did the earlier papers establish?

Several papers use similar words while studying different mathematical objects.

| Work | Plain-language comparison |
|---|---|
| Gröchenig (2020) | Studies the same curve and explains the RH connection; does not prove our shape result. |
| Zhang (2022–2023) | Studies related positivity properties. The original and revised papers make different claims; neither inspected version establishes our strict shape result. |
| Katkova (2005/2007) | Proves positivity tests for lists of coefficients, not for shifted values of our curve. A larger numbered test there is not a stronger version of our result. |
| Planat–Solé and Gershon (2026) | Study the usual theta kernel associated with xi, not the curve obtained from reciprocal xi. Similar titles do not mean the same theorem. |
| Polson | Makes stronger claims, but our review has a specific unresolved objection to the displayed argument. It needs checking against the original PDF before public criticism. |

The detailed comparisons and links are below. A reasonable description is:
**“We have a checked proof of this result and have not found a prior proof in
the literature we reviewed.”** Neither “already known” nor “confirmed first
proof” is justified by the present review.

## Technical assessment and recommended wording

The delegated exact-statement literature comparison found no established prior
proof of unconditional, everywhere-strict log-concavity of this reciprocal-Xi
Fourier density. That makes the result a credible candidate for mathematical
novelty, not a certified first proof. The absence of a novelty claim in the
[independent proof audit](EXTERNAL_ASTRA_FINAL_AUDIT.md) was a scope boundary,
not evidence that the theorem was already known. Lean formalization is a
separate contribution; machine verification alone does not establish originality.

Suggested wording:

> We give an unconditional, Lean-verified proof of strict log-concavity of the
> reciprocal-Xi Fourier density. We have not located a prior proof of this
> statement in the literature reviewed.

The completed formalization and its evidence remain in
[FINAL_VERIFICATION.md](FINAL_VERIFICATION.md). This assessment does not change
the proof's `COMPLETE` status or extend the independent auditor's verdict.

## Technical details: exact function and theorem

For the standard completed xi function, set
$$
F(z)=\frac14\xi\!\left(\frac12+\frac{iz}{2}\right),\qquad
\phi(u)=\frac{F(0)}{F(iu)}
=\frac{\xi(1/2)}{\xi(1/2+u/2)},
$$
where the final equality uses the functional equation. Define
$$
\Lambda(x)=\frac1{2\pi}\operatorname{Re}
\int_{\mathbb R}\phi(u)e^{-ixu}\,du.
$$

The theorem `ReciprocalXi.density_full_conclusions`, at line 706 of
[ReciprocalXiDensityFull.lean](theorem_pipeline/workspace/lean_project/ProofWorkspace/Final/ReciprocalXiDensityFull.lean),
proves without hypotheses that this density is smooth, even, integrable,
has total mass one, is positive everywhere, and satisfies
$$
\Lambda'(x)^2-\Lambda(x)\Lambda''(x)>0\qquad(x\in\mathbb R).
$$
It also proves strict log-concavity and strictly positive ordered two-by-two
translation minors. These are **PF2 conclusions, not PF-infinity or RH**.
Pointwise strict curvature is not a claim of a uniform positive lower bound
on $-(\log\Lambda)''$.

## Detailed literature comparisons and sources

### 1. Gröchenig: the same density, but an all-orders equivalence

Karlheinz Gröchenig, *Schoenberg's Theory of Totally Positive Functions and the
Riemann Zeta Function* (2020), Theorem 4, defines
$$
\Lambda_G(x)=\frac1{2\pi}\int_{\mathbb R}
\frac{e^{-ix\tau}}{\xi(1/2+\tau)}\,d\tau.
$$
Our normalization gives
$$
\Lambda(x)=2\xi(1/2)\Lambda_G(2x).
$$
This follows by substituting $u=2\tau$; the Fourier integral is real by
symmetry. Thus the objects agree up to positive scaling and dilation. His
theorem characterizes RH by the all-orders Pólya-frequency property. It does
not prove unconditional log-concavity. The subsequent discussion says even
nonnegativity/positive-definiteness did not seem known then: useful historical
context, not a statement about the whole literature today.
[Source: Theorem 4 and following discussion](https://arxiv.org/html/2007.12889).

### 2. Zhang: distinguish the original claim from the revised paper

Ruiming Zhang's original version, *On the Positivity of Certain Theta Kernels*
(8 June 2022), Corollary 5, claims positivity of a zero-theta sum and complete
monotonicity of $1/\xi(1/2+\sqrt{x})$ and a derivative ratio.
[Source: arXiv:2206.05104v1](https://arxiv.org/html/2206.05104v1).

If established, the reciprocal complete-monotonicity result would give a
positive Gaussian-mixture representation. Our comparison does not infer
log-concavity from that: positive Gaussian mixtures need not be log-concave.

The latest version inspected, v8 dated 24 December 2023, is retitled *On Certain
Genus 0 Entire Functions*. Its Corollary 4 instead gives an RH-equivalent
hierarchy of complete-monotonicity conditions. The superseded v1 claim should
not be presented as an unchanged settled theorem. Neither inspected version
establishes our everywhere-strict density-curvature conclusion.
[Revised paper](https://arxiv.org/html/2206.05104),
[version history](https://arxiv.org/abs/2206.05104).

### 3. Katkova: coefficient positivity is a different statement

Olga M. Katkova, *Multiple positivity and the Riemann zeta-function*
(2005 preprint / 2007 journal), proves finite-order positivity, including
$\xi_1\in PF_{44}$, and asymptotic positivity results for coefficient
sequences and generating functions. The relevant matrices are coefficient
Toeplitz matrices, not continuous translation matrices of our reciprocal-Xi
density. Shared PF terminology does not make these statements equivalent;
the finite-order coefficient results do not by themselves establish our
density theorem.
[Source: definitions, Theorem 1 and subsequent results](https://arxiv.org/html/math/0505174).

### 4. Recent theta-kernel concavity: different Fourier-side objects

Michel Planat and Patrick Solé, *Second-Level Concavity of the Riemann Xi
Kernel* (19 August 2026), concern the classical Jacobi-theta kernel $\Phi$ in
Xi's Fourier representation. They define $s(t)=\Phi(\sqrt{t})$ and
$f(t)=s'(t)^2-s(t)s''(t)$, and claim strict concavity of $\log f$.
This is not the reciprocal density above; the comparison identified no direct
implication of our theorem.
[Source: abstract and paper](https://arxiv.org/abs/2608.19160).

Likewise, Avi Gershon's *On the Log-Concavity of the Riemann Xi Kernel*
(2026; the inspected page presents v2, posted 29 June 2026) concerns the
ordinary theta kernel, not reciprocal Xi. Its abstract also claims Lean
formalization. Neither a similar title nor use of Lean establishes that the
mathematical statements coincide. The page identifies the manuscript as a
non-peer-reviewed preprint.
[Source](https://www.preprints.org/manuscript/202604.0159).

### 5. Polson: stronger claims and a specific unresolved objection

Nicholas Polson's *Riemann, Thorin, van Dantzig Pairs, Wald Couples and
Hadamard Factorisation* contains stronger generalized-gamma-convolution
(GGC) and RH claims. They were not accepted as established prior results in
this comparison.
[Displayed HTML source](https://arxiv.org/html/1804.10043).

The delegated review identifies this specific concern in the displayed
Theorems 23–25: the claimed positive Thorin measure
$U^*=\delta_{3/4}+u^*(z)\,dz$ contains an independent
$\operatorname{Exp}(3/4)$ component, while subsequent exponential untilting
asserts $\mathbb E[e^{H^*}]<\infty$. Under that positive-measure decomposition,
the exponential component already makes the moment at one infinite.

This is our mathematical objection to the displayed argument, not an
established published refutation or a blanket verdict on the author's work.
**PDF/source correspondence must be checked before using this criticism
publicly.** This addendum records the concern; it does not resolve that
remaining source-correspondence check or commission a new proof audit.

## What the search covered, and what it could have missed

The side conversation reports searches covering reciprocal-Xi/xi laws,
log-concavity, strong unimodality, finite/all-order total positivity,
coefficient inequalities and nearby theta-kernel results. Some recent SSRN
full texts were inaccessible. Failure to find an exact match in that bounded
review is not a priority certificate. No specialist was contacted, and no
independent new proof rebuild was performed in that side conversation.

This addendum incorporates the assessment delegated by task
`01a0911b-1542-7d81-a591-daec833b2b1e` at Francesco's explicit request.
The main task reopened the linked primary-source pages and checked the
central object/version distinctions when incorporating it on 11 September
2026. That incorporation is not a repeat of the full literature search.

The Lean proof, sidecar, independent final audit, compiled verification logs
and original source/data evidence have not been edited. No new Slack
announcement or other external publication is authorized by this addendum.

The previously prepared `reciprocal-xi-lean-proof-and-audit-20260911.zip` and
the reports already uploaded to Slack predate this addendum. They remain
unchanged and do not include this literature assessment.

**Bottom line:** a credible novelty candidate awaiting specialist confirmation,
not “known already,” not “first proof established,” and not RH.
