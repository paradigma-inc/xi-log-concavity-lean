# Actual reciprocal-Xi bounds throughout the closed unit strip

Companion: `ReciprocalStripFull.lean`, namespace `ReciprocalXi`.

## Statement

Let $\Phi(z)=F(0)/F(iz)$ be the actual complex reciprocal extension, and
let $\varphi(u)=\Phi(u)$ on the real axis. For every complex $z$ with
$|\Im z|\leq1$, the module proves

$$
|\Phi(z)|\leq5|\varphi(\Re z)|.
$$

There is no restriction on $\Re z$. These are the previously defined
actual functions, with no assumed reality, positivity, product formula,
or factor comparison. The already established real-axis tail estimate
also yields, for every real $r$ and $|\Re z|\geq3$,

$$
|\Phi(z)|\leq5C_r\exp(-r|\Re z|),
$$

where $C_r=\texttt{reciprocalTailConstant}\ r$ is the explicit real-axis
constant defined in `XiRealBoundsFull`.

## Proof Sketch

Put $s=(1+z)/2$. The exact normalization of the reciprocal extension is
$\Phi(z)=\xi(1/2)/\xi(s)$. For $\Re z\geq3$, write $\sigma=\Re s\geq2$;
the strip condition gives $|\Im s|\leq1/2$. The actual Xi factorization is

$$
\xi(s)=\frac{s(s-1)}2\,\pi^{-s/2}\Gamma(s/2)\zeta(s).
$$

The inequalities $|\sigma|\leq|s|$ and
$|\sigma-1|\leq|s-1|$ show that the polynomial factors favor the complex
denominator. The norm of the pi-power depends only on the real part, so
it is unchanged. The proved vertical Gamma inequality, applied at
$x=\sigma/2\geq1$ and $t=\Im s/2$, bounds its ratio by $e^{t^2}$.
Since $t^2\leq1/16$, the kernel-checked rational Taylor enclosure of
$e^{1/16}$ bounds this by $5/4$. The actual absolutely convergent zeta
and Möbius series, already formalized in `ZetaVerticalBoundsFull`, give
$|\zeta(\sigma)|\leq4|\zeta(s)|$. Multiplication yields

$$
|\xi(\sigma)|\leq5|\xi(s)|.
$$

The previously proved zero-free strip makes the relevant denominators
nonzero. Dividing the common numerator $|\xi(1/2)|$ by this comparison
proves the reciprocal estimate on the right tail. On $|\Re z|\leq3$,
the actual theta/Mellin estimate from `XiStripBoundsFull` gives the
stronger factor $2$. Finally, exact evenness of $F$, and hence of both
$\Phi$ and $\varphi$, reflects the right tail to the left without changing
the strip condition. The central and two tail regions cover all real
parts.

Substituting the already proved real-axis exponential bound into the
uniform comparison gives the displayed tail corollary. This uses no
contour-shift assumption.

## Main declarations

- `exp_sixteenth_le_five_fourths`
- `Gamma_half_vertical_norm_comparison`
- `xi_norm_eq_factors_of_one_lt_re`
- `xi_vertical_norm_comparison_outer`
- `reciprocalExtension_norm_le_five_right`
- `reciprocalExtension_even`
- `reciprocalExtension_norm_le_five`
- `reciprocalExtension_norm_le_exp_of_abs_re_three_le`

## Scope

Together with the previously established holomorphic extension, this
supplies the actual strip bounds needed by later contour and numerical
enclosure arguments. It does not itself prove a contour-shift identity,
the compact certificate's analytic enclosures, or positivity or positive
curvature of the inverse Fourier density.

Normalized source:
`theorem_pipeline/workspace/contexts/reciprocal_xi_global_logconcavity.md`.
The numerical exponential step uses `RationalExpBoundsFull`, rather than
an external floating-point result. No `sorry`, custom axiom, or
`native_decide` is used.
