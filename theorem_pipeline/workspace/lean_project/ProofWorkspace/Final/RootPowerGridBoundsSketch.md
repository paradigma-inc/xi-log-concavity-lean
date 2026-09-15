# Algebraic-root evaluation of retained-grid powers

Source: `workspace/contexts/reciprocal_xi_global_logconcavity.md`.
Run: `20260909T204310Z_e45f`.

For $a>0$, the actual positive number $a^{-1/80}$ satisfies $x^{80}=1/a$.
Consequently nonnegative rational $l,u$ satisfying $a l^{80}\le1\le a u^{80}$
enclose it, by strict monotonicity of the natural power on the nonnegative
half-line. These are integer/rational polynomial checks, not estimates based
on floating-point logarithms.

The exact identity $(a^{-1/80})^{k+40}=a^{-(k+40)/80}$ converts one certified
root interval into every power needed by the eta grid. The already proved
outward-rounded power iteration preserves this actual-function enclosure.
The method changes only evaluation, not the eta integral, the grid, its
analytic remainder or the target theorem. Concrete root-row data and the
retained Xi comparisons require separate checking.

