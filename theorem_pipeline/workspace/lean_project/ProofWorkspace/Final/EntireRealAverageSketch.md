# Rigidity from subquadratic positive-real-part averages

## Statement

If $f$ is entire, $f(0)=f'(0)=0$, and
$$R^{-2}\operatorname{avg}_{|z|=R}\max(0,\operatorname{Re}f(z))\longrightarrow0,$$
then $f$ vanishes identically.

## Assumptions

Exactly the three hypotheses in the statement. This general theorem is separately instantiated with the actual Xi quotient logarithm; no hypothesis is dropped in that application.

## Proof Sketch

The Cauchy kernel and its conjugate give a representation of $f(w)+\overline{f(0)}$ using twice the boundary real part. The conjugate-kernel term is evaluated by reflecting it to a holomorphic rational kernel with its pole outside the disk. Since the average real part is zero, the average absolute real part is twice its positive-part average. For $|w|<R/2$, this bounds $|f(w)|$ by eight times the positive-part average on radius $R$. The zero value and zero derivative allow the order-two Schwarz estimate, improving the bound to $32|w|^2/R^2$ times that average. Letting $R$ tend to infinity proves $f(w)=0$ for every fixed $w$.

## Lean Artifacts

- File: `EntireRealAverageFull.lean`
- Main theorem: `entire_eq_zero_of_subquadratic_positive_average`.
- Supporting representation: `entire_realpart_cauchy`.
