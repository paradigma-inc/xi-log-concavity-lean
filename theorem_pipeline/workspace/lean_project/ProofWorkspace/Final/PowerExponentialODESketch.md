# Exact coefficient recurrence for a power-exponential atom

## Statement

For $f(z)=z^s e^{-\lambda z}$ on the principal slit plane, $zf'(z)=(s-\lambda z)f(z)$. If $a_n=f^{(n)}(z)/n!$, then
$$z(n+2)a_{n+2}=(s-\lambda z-n-1)a_{n+1}-\lambda a_n.$$

## Assumptions

The point is in the slit plane; $s$ is complex and $\lambda$ is real.

## Proof Sketch

Differentiate the product to obtain the first-order identity. Repeated differentiation of multiplication by the identity function gives $D^{n+1}(zf)=zD^{n+1}f+(n+1)D^nf$. Apply this to the first-order identity, using equality on the open slit plane, and divide by the nonzero factorials. The recurrence describes derivatives of the actual analytic function, not an unidentified sequence.

## Lean Artifacts

- Full proof: `PowerExponentialODEFull.lean`
- Theorems: `iteratedDeriv_id_mul_succ`, `complexPowerExpAtom_analyticAt`, `complexPowerExpAtom_ode`, `complexPowerExpAtom_derivative_recurrence`, `complexPowerExpTaylorCoefficient_recurrence`.
