# Compound-Poisson law of a finite positive measure

## Statement and assumptions

For any finite positive measure $\mu$ on the real line, take its total mass as the Poisson rate and its probability normalization as the jump law. The resulting probability law has characteristic function $\exp\int(e^{iuy}-1)\,d\mu(y)$. If $\mu$ has finite absolute first moment, the constructed law does too, with absolute first moment at most $\int |y|\,d\mu(y)$. The zero measure gives a point mass at zero, and nonnegative support is preserved.

## Proof Sketch

The library normalization writes $\mu$ as its mass times a probability measure, including the zero-mass case. Substitute this identity into the compound-Poisson characteristic-function and first-moment formulas. Normalization of a nonzero measure preserves integrability by finite rescaling; at zero it is a Dirac measure and is still integrable. Characteristic-function uniqueness identifies the zero-rate law with the point mass at zero, which also handles that case in the support proof.

No signed measure is normalized. These are actual positive finite measures; selecting the Xi-specific finite pieces remains a separate obligation.

## Lean Artifacts

File: `FiniteLevyLawFull.lean`. Main theorems: `finiteLevyLaw_isProbability`, `charFun_finiteLevyLaw`, `lintegral_norm_finiteLevyLaw_le`, `finiteLevyLaw_zero`, and `ae_nonneg_finiteLevyLaw`.
