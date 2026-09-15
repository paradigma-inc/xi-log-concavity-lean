# Analytic identity after verified exponential integrability

## Statement

Suppose a real-line measure has an integrable absolute exponential at radius $R>0$. For entire functions $A,B$, an identity
$$
M(iu)A(iu)=B(iu)\qquad(u\in\mathbb R)
$$
for its actual complex moment-generating function implies $M(w)A(w)=B(w)$ whenever $|\operatorname{Re}w|<R$.

## Assumptions

The absolute exponential integral is finite before analytic continuation is used. Both comparison functions are entire. The imaginary-axis identity is explicit.

## Proof Sketch

The absolute exponential dominates every real exponential with parameter in $[-R,R]$. Thus the open interval lies inside the interior of the moment-integrability set. The verified complex moment-generating-function theorem gives holomorphy on the corresponding connected vertical strip. The imaginary-axis sequence $i/(n+1)$ provides distinct equality points accumulating at zero. The analytic identity theorem extends the identity throughout that strip. This argument identifies an already existing moment; it does not infer moment existence from formal continuation.

## Lean Artifacts

- File: `ProofWorkspace/Final/ExponentialAnalyticIdentityFull.lean`
- Theorems: `integrable_exp_of_absoluteMoment`, `interior_integrableExpSet_of_absoluteMoment`, `complexMGF_identity_from_imaginary`.
