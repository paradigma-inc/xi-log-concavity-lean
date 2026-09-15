# Concrete theta truncation budget at 48

## Statement

The exact finite theta integral with $T=16$ and four Gaussian terms approximates $\operatorname{Re}F(48)$ to absolute error at most $10^{-16}$.

## Assumptions

There are no numerical hypotheses. This result uses the previously proved theta integral identity and its explicit truncation bound.

## Proof Sketch

The elementary inequality $e\ge 5/2$ gives $e^{48}\ge 10^{19}$. Since $\pi>3$, both omitted tails are bounded by $10^{-19}$. Substitution into the exact truncation formula, followed by rational arithmetic, gives the stated error. This theorem does not evaluate the retained finite integral and does not yet certify the source endpoint for $F(48)$.

## Lean Artifacts

- Full proof: `XiThetaTruncationBudgetFull.lean`
- Theorems: `exp_48_lower_for_theta`, `F48_finite_theta_truncation_error`.
