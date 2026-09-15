# Fourier transform of the Laplace atom

## Statement

For $a>0$ and real $u$, the function $e^{-a|x|}e^{iux}$ is integrable and
$$
\int_{\mathbb R} e^{-a|x|}e^{iux}\,dx=\frac{2a}{a^2+u^2}.
$$

## Assumptions

Only positivity of $a$ and reality of $u$ are required. No Fourier transform or improper-integral value is assumed.

## Proof Sketch

On the nonpositive half-line the integrand is $e^{(a+iu)x}$, and on the positive half-line it is $e^{(-a+iu)x}$. The verified decaying complex-exponential integral formulas establish integrability and give the two integrals. Adding them and simplifying yields the rational transform; all denominators are proved nonzero.

## Lean Artifacts

- File: `ProofWorkspace/Final/LaplaceAtomFourierFull.lean`
- Theorems: `laplaceAtomCharacter_nonpos`, `laplaceAtomCharacter_nonneg`, `integrableOn_laplaceAtomCharacter_Iic`, `integrableOn_laplaceAtomCharacter_Ioi`, `integrable_laplaceAtomCharacter`, `integral_laplaceAtomCharacter`.
