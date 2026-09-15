# Vertical isolation and simplicity of actual zeros

## Statement

For the actual entire function $F$, the derivative of
$y\mapsto\operatorname{Im}F(x+iy)$ is $\operatorname{Re}F'(x+iy)$.
A strict sign of this derivative throughout $-1<y<1$ forces any zero in
the column onto the real axis. A nonzero real part of $F'$ at a zero
implies analytic order one.

## Assumptions

The derivative sign is an explicit hypothesis on the whole vertical
interval, not a statement inferred from samples. The zero must be an
actual zero of $F$. No finite rectangle sign or zero-list certificate
is supplied by this module.

## Proof Sketch

The complex chain rule, restriction to the real line and the continuous
linear imaginary-part map give the derivative identity. Conjugation
symmetry makes $F(x)$ real. A strict derivative sign therefore makes the
imaginary part strictly monotone, with its unique zero at $y=0$.
The previously proved zero strip places each actual zero in the relevant
open interval. Finally, a nonzero derivative gives analytic order one by
the standard analytic-order theorem.

## Lean Artifacts

- File: `XiFiniteVerticalFull.lean`.
- Theorems: `F_vertical_im_hasDerivAt`, `F_vertical_im_zero`, `F_vertical_zero_of_deriv_pos`, `F_vertical_zero_of_deriv_neg`, `F_zero_real_of_vertical_deriv_sign`, `F_zero_simple_of_deriv_re_ne_zero`.

This is an analytic implication; the finite sign bounds remain to be proved.

