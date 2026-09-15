# Actual Xi zero-free strip and reciprocal holomorphy

Companion: `XiZeroStripFull.lean`, namespace `ReciprocalXi`.

## Statement

The actual normalized entire function $\xi$ is nonzero throughout the closed
horizontal strip

$$
\{s\in\mathbb C:|\Im s|\le1/2\}.
$$

For the actual normalization $F(w)=\xi(1/2+iw/2)/4$, define

$$
\Phi(z)=\frac{F(0)}{F(iz)}
       =\frac{\xi(1/2)}{\xi((1+z)/2)}.
$$

The module proves the displayed identity for every complex $z$, agreement
$\Phi(u)=\texttt{reciprocalTransform}(u)$ for every real $u$, nonvanishing of
the denominator when $|\Im z|\le1$, and complex differentiability of $\Phi$
on the open strip $|\Im z|<1$.

The main results have no assumptions beyond the displayed strip bounds.
In particular, neither a zero-free region nor a representation of Xi by an
unverified surrogate is assumed.

## Proof Sketch

On the half-plane $\Re s>1$, the actual library zeta function is nonzero by
absolute convergence and the Euler-product theorem. Its Gamma factor is
also nonzero there. The previously proved identity
$\xi(s)=s(s-1)\Gamma_{\mathbb R}(s)\zeta(s)/2$ consequently shows that
$\xi(s)$ cannot vanish. The functional equation $\xi(1-s)=\xi(s)$ gives
the same result on $\Re s<0$.

The remaining region $0\le\Re s\le1$, $|\Im s|\le1/2$ is precisely the
rectangle established in `XiMellinIdentityFull`: the actual theta/Mellin
formula gives $|\Lambda_0(s)|<1$, while the elementary product estimate is
$|s(s-1)|\le1$. Therefore $s(s-1)\Lambda_0(s)$ cannot equal $-1$. These three
regions cover the entire horizontal strip, including both vertical
boundaries of the central rectangle.

Substituting $iz$ into the definition of $F$ and applying the same functional
equation gives $F(iz)=\xi((1+z)/2)/4$ exactly. If $|\Im z|\le1$, the argument
$(1+z)/2$ lies in the proved zero-free strip, so the denominator is nonzero.
Since $F$ is entire, the quotient defining $\Phi$ is complex differentiable
at every point of the stated open strip. Its equality with the real-axis
transform is definitional, with no change to the Fourier normalization.

## Scope and remaining work

This module establishes a genuine analytic extension of the actual
reciprocal transform. It does not prove decay or integrability on shifted
complex lines, justify a contour shift, provide quadrature enclosures, or
prove log concavity of the inverse Fourier density. Such claims require
additional bounds and are not inserted as premises here. This small
zero-free strip is not a proof of the Riemann hypothesis.

## Main Lean declarations

- `xi_ne_zero_of_one_lt_re`
- `xi_ne_zero_of_re_lt_zero`
- `xi_ne_zero_of_abs_im_le_half`
- `F_imaginary_axis_complex`
- `F_imaginary_axis_complex_ne_zero`
- `reciprocalExtension`
- `reciprocalExtension_ofReal`
- `reciprocalExtension_eq_xi_ratio`
- `differentiable_F_complex`
- `differentiableAt_reciprocalExtension`
- `differentiableOn_reciprocalExtension`

Normalized source context:
`theorem_pipeline/workspace/contexts/reciprocal_xi_global_logconcavity.md`.
The underlying nonvanishing and Gamma results are from the pinned mathlib
`LSeries.Dirichlet` and Gamma modules.

No `sorry`, custom axiom, or `native_decide` is used.
