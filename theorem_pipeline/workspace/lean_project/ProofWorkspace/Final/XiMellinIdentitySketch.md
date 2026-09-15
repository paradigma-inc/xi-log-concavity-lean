# Actual theta/Mellin identity and central Xi nonvanishing

Companion: `XiMellinIdentityFull.lean`, namespace `ReciprocalXi`.

## Statement and assumptions

Write $\theta(t)=\operatorname{cosKernel}(0,t)$ for mathlib's actual theta
series and $\Lambda_0(s)=\texttt{completedRiemannZeta₀}(s)$ for its actual
pole-removed completed zeta function. For every complex $s$ with
$0\le\Re(s)\le1$, the module proves

$$
\Lambda_0(s)=\frac12\left[
\int_1^\infty t^{s/2-1}(\theta(t)-1)\,dt+
\int_1^\infty t^{(1-s)/2-1}(\theta(t)-1)\,dt\right].
$$

It consequently proves

$$
\lVert\Lambda_0(s)\rVert\le\frac{4e^{-\pi}}{\pi}<1.
$$

In particular the normalized actual entire function
$\xi(s)=[s(s-1)\Lambda_0(s)+1]/2$ has positive real part at every real
$s\in[0,1]$. A further corollary proves $\xi(s)\ne0$ on the complex rectangle
$0\le\Re(s)\le1$, $|\Im(s)|\le1/2$.

The only assumptions of these main theorems are the stated bounds on $s$.
The integral identity, theta estimates, and completed-zeta bounds are not
premises; they are proved from the library definitions and the preceding
`XiThetaBoundsFull` module.

## Proof Sketch

Let $H(t)=\mathbf 1_{t>1}(\theta(t)-1)$. The modified kernel in mathlib's
definition of the pole-removed completed zeta satisfies
$f_{\mathrm{modif}}(t)=H(t)+t^{-1/2}H(t^{-1})$ for every $t>0$.
On $t>1$ and at $t=1$ this follows directly from the definition. On $0<t<1$
it follows from the actual theta functional equation
$\theta(t)=t^{-1/2}\theta(t^{-1})$. The zero value at $t=1$ matches the
library's exact convention, so no endpoint assumption is hidden.

The upper theta-kernel bound proves the needed Mellin integrability. The
inverted term is also Mellin-integrable by the library's inversion change
of variables and power-shift identity. Thus the Mellin transform of the
sum can be split. The upper part is the integral over $(1,\infty)$, while
the transformed lower part has Mellin parameter $1/2-s/2$. Substitution
into the actual definition of $\Lambda_0$ gives the displayed identity,
including its normalization factor $1/2$.

Each upper integral has norm at most $4e^{-\pi}/\pi$, by the preceding
Gaussian theta estimate. The triangle inequality and factor $1/2$ retain
the same bound for their average. The elementary inequalities $\pi\ge2$
and $e^\pi\ge\pi+1$ imply $e^{-\pi}<1/2$, hence
$4e^{-\pi}/\pi<1$.

For real $s\in[0,1]$, the weaker bound
$\Re\Lambda_0(s)<2$ already suffices: since
$0\le s(1-s)\le1/4$, the identity
$\Re\xi(s)=[1-s(1-s)\Re\Lambda_0(s)]/2$ is strictly positive.

For the rectangle corollary, put $\sigma=\Re(s)$ and $d=|\Im(s)|$.
The triangle inequality gives
$|s||s-1|\le(\sigma+d)(1-\sigma+d)$, which is at most $1$ when
$0\le\sigma\le1$ and $d\le1/2$. Hence
$|s(s-1)\Lambda_0(s)|<1$, so this product cannot equal $-1$ and $\xi(s)$
cannot vanish. The argument does not use the false stronger product bound
$|s(s-1)|\le1/2$ at this rectangle's height.

## Scope

These are unconditional results about the actual library completed zeta
and the actual normalized Xi definition. They do not prove positivity or
log concavity of the reciprocal Fourier density, nor the Riemann hypothesis.
They discharge the central real-axis nonvanishing step needed before using
the independently proved reciprocal-transform tail bounds and Fourier
regularity arguments.

## Main Lean declarations

- `hurwitzZero_f_modif_eq`
- `mellin_hurwitzZero_f_modif`
- `completedRiemannZeta₀_eq_thetaMellin`
- `completedRiemannZeta₀_norm_lt_two`
- `xi_re_pos_of_mem_Icc`
- `completedRiemannZeta₀_norm_le_thetaBound`
- `completedRiemannZeta₀_norm_lt_one`
- `xi_ne_zero_of_central_rectangle`

Source context: `theorem_pipeline/workspace/contexts/reciprocal_xi_global_logconcavity.md`,
supplemented by the pinned mathlib definitions in `RiemannZeta.lean`,
`HurwitzZetaEven.lean`, `AbstractFuncEq.lean`, and `MellinTransform.lean`.

No `sorry`, custom axiom, or `native_decide` is used.
