# Exact rational Machin enclosure for pi

## Statement

For rational $q$ and $N\in\mathbb N$, define exact rational quantities

$$
A_N(q)=\sum_{n=0}^{N-1}\frac{(-1)^nq^{2n+1}}{2n+1},
\qquad
E_N(q)=\frac{|q|^{2N+1}}{1-q^2}.
$$

For $|q|<1$, `ratArctanTaylor_error` proves
$|\arctan q-A_N(q)|\le E_N(q)$.
Using the source series lengths, define

$$
p=16A_{150}(1/5)-4A_{45}(1/239),\qquad
E=16E_{150}(1/5)+4E_{45}(1/239).
$$

The rational endpoints are $p_-=p-E$ and $p_+=p+E$. The main theorems prove

$$
p_-\le\pi\le p_+,
\qquad
p_+-p_-<10^{-160},
\qquad
0<p_-.
$$

All endpoints are exact rational expressions. The midpoint is the rational finite Machin sum, not a rounded decimal copied from the source.

## Assumptions

The general arctangent bound requires only $|q|<1$. The concrete pi enclosure, width bound, and positive lower endpoint have no hypotheses. No decimal pi value, numerical arctangent evaluation, or unverified arithmetic oracle is assumed.

## Proof Sketch

Mathlib's proved arctangent power series is valid inside the unit interval. Remove its first $N$ terms. The absolute value of each remaining term is at most its numerator $|q|^{2(N+n)+1}$ because its positive odd denominator is at least one. These numerators form an exact geometric series with ratio $q^2$. Summing the absolute majorant gives $E_N(q)$ and therefore the directed arctangent enclosure. This slightly looser geometric bound is sufficient and does not require an alternating-series remainder theorem.

The actual Machin identity $\pi=16\arctan(1/5)-4\arctan(1/239)$ is already proved in mathlib. Substituting the two finite sums and applying the triangle inequality gives $|\pi-p|\le E$. Thus $p\pm E$ are directed rational endpoints. Their difference is exactly $2E$; cancellation removes the large midpoint from the width calculation. Lean's ordinary exact rational arithmetic proves $2E<10^{-160}$ using the source lengths 150 and 45. Only the exponentiation evaluation threshold is raised to 512 for this finite arithmetic proof; the produced proof term is kernel checked. Combining the width bound with the actual inequality $\pi>3$ gives positivity of the lower endpoint.

## Scope

This module certifies a numerical primitive for the retained-node evaluator. It does not certify any Xi sample or silently replace source interval endpoints. Downstream logarithm or Gamma calculations must use these explicit directed pi endpoints and propagate their uncertainty. No density or curvature conclusion is claimed.

## Lean Artifacts

- Full proof: `ProofWorkspace/Final/PiBoundsFull.lean`.
- Definitions: `ratArctanTaylor`, `ratArctanError`, `machinPiMidpoint`, `machinPiRadius`, `machinPiLower`, `machinPiUpper`.
- Theorems: `arctanTaylor_error`, `ratArctanTaylor_error`, `machinPi_error`, `machinPi_enclosure`, `machinPi_width_lt`, `machinPiLower_pos`.
- Namespace: `ReciprocalXi`.
- Source: the existing reciprocal-Xi finite evaluation material and `theorem_pipeline/workspace/prompts/eta_evaluator.txt`.
- Tracked run: `20260909T184117Z_fe26`.
