# Actual residual moment as a finite-factor Xi quotient

## Statement

Delete a finite multiset of actual positive Xi zero occurrences. Assume the remaining set is conjugation closed, its actual heat trace is nonnegative, and all remaining squared roots have real part greater than $R^2$ for some $R>0$. Inside $|\operatorname{Re}w|<R$, the actual residual moment-generating function satisfies
$$
M(w)F(w)=F(0)\prod_{a\ \mathrm{deleted}}(1-w^2/a^2).
$$
At real $r$ with $|r|<R$ and $F(r)\ne0$, this identifies the actual one-sided moment with the real part of the quotient. The absolute exponential integral is finite and at most twice that quotient.

## Assumptions

All zero occurrences, traces and functions are the actual previously defined objects. Conjugation closure, heat-trace nonnegativity, the strict spectral gap and nonvanishing at the evaluated point are explicit. The finite low-zero certificate and numerical evaluation at the intended radius are still not discharged here.

## Proof Sketch

The proved residual moment theorem supplies actual absolute exponential integrability at $R$. On the imaginary axis, the characteristic-function identity and exact finite factor deletion give the displayed equation. The complex moment-generating function is therefore holomorphic on the open strip for a justified probabilistic reason. Apply the analytic identity theorem to its product with the entire function $F$. On the real axis, divide only under the explicit nonzero hypothesis and take real parts. The already verified two-sided inequality supplies the absolute-moment bound.

## Lean Artifacts

- File: `ProofWorkspace/Final/XiResidualQuotientFull.lean`
- Theorems: `F_selectedResidualLaw_complexMGF_mul`, `F_selectedResidualLaw_moment_quotient`, `F_selectedResidualLaw_absoluteMoment_quotient`.
