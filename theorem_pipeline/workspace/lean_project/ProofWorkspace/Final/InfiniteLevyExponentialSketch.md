# Exponential moments of the constructed infinite Lévy law

## Statement

A positive S-finite real-line measure $\mu$, supported on $[0,\infty)$ with finite absolute first moment, generates the previously constructed probability law. If $q\ge0$ and $\int(e^{qy}-1)\,d\mu$ is finite, that law has an integrable exponential with moment
$$
\exp\!\left(\int(e^{qy}-1)\,d\mu\right).
$$

## Assumptions

Nonnegative support, first-moment integrability and exponential-kernel integrability concern the original measure, not the constructed probability law. A companion theorem covers explicitly supplied countable finite pieces.

## Proof Sketch

Restrict the exponential kernel to each finite piece. Adding its integrable constant part gives the finite-piece exponential integrability required by the finite Lévy law theorem. The original kernel's integrability makes the sequence of its piecewise integrals summable. The already proved first-moment bound supplies summable moments of the independent jumps. Apply the verified infinite-independent-sum exponential theorem, then identify the sum of exponents with the original integral. The library's S-finite decomposition supplies the pieces without an additional existence assumption.

## Lean Artifacts

- File: `ProofWorkspace/Final/InfiniteLevyExponentialFull.lean`
- Theorems: `infiniteLevyLaw_exponentialMoment`, `sfiniteLevyLaw_exponentialMoment`.
