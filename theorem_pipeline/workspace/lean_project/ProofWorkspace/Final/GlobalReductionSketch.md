# From positive curvature to log concavity and order-two minors

## Statement

For a positive real function $f$ with first and second derivative functions $f_1,f_2$, suppose $f_1(x)^2-f(x)f_2(x)>0$ for every real $x$. Then $\log f$ is strictly concave, and for all $x_1<x_2$ and $y_1<y_2$,

$$
f(x_1-y_1)f(x_2-y_2)-f(x_1-y_2)f(x_2-y_1)>0.
$$

Separately, an even curvature function positive on $[0,B]$ and $[X,\infty)$ is positive everywhere if $X\le B$. The exact rational numbers $317649680434/100000000000$ and $318/100$ satisfy this overlap. This comparison alone does not establish the numerical tail threshold for Xi.

## Assumptions

Every derivative statement is an explicit `HasDerivAt` hypothesis, positivity is an explicit hypothesis, and curvature positivity is an explicit hypothesis. The coverage theorem explicitly assumes evenness and positivity on its two ranges. Nothing in this file asserts these assumptions for the Xi density.

## Proof Sketch

The chain and quotient rules give

$$
(\log f)'=f_1/f,\qquad (\log f)''=(f_2f-f_1^2)/f^2<0.
$$

Mathlib's second-derivative criterion yields strict concavity. The quotient $f_1/f$ is strictly decreasing. For $e>0$, the function $g(t)=\log f(t)-\log f(t-e)$ has negative derivative and is therefore strictly decreasing. Evaluating at $t$ and $t+d$, where $d>0$, and using the monotonicity of logarithm gives the strict translation-minor inequality. Substituting $t=x_1-y_1$, $d=x_2-x_1$, and $e=y_2-y_1$ gives arbitrary ordered nodes.

The coverage result splits nonnegative inputs at $B$; inputs beyond $B$ are at least $X$, and negative inputs reduce to nonnegative inputs by evenness.

## Lean Artifacts

- File: `ProofWorkspace/Final/GlobalReductionFull.lean`
- Theorems: `certified_ranges_overlap`, `positive_of_even_compact_tail`, `deriv_log_eq_jet`, `deriv2_log_eq_jet`, `strictConcaveOn_log_of_positive_curvature`, `translation_minor_pos_of_positive_curvature`, `pf2_minor_pos_of_positive_curvature`.
- Namespace: `ReciprocalXi`.

These are proved generic implications, not a completed reciprocal-Xi theorem.
