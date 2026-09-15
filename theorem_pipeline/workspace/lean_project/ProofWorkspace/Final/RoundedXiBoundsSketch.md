# Actual Xi and reciprocal-grid enclosures with rounding

At $s_k=(k+40)/80$, the accepted factorization expresses actual $\xi(s_k)$
as $s_k/2$ times four positive factors: Gamma, a power of $\pi$, eta and
$(s_k-1)/(1-2^{1-s_k})$. The special-function intervals include all proved
series errors and their outward-rounded intermediate computations.
The eta evaluator reuses two initial powers of each integer base across the grid.

For $s_k\ne1$, exact sign lemmas convert the final bracket to
$|s_k-1|/|1-2^{1-s_k}|$. A checked positive rational denominator lower bound
makes interval division sound. Sign-aware subtraction and final outward
rounding retain the actual bracket. At $s_k=1$, the exact value $\xi(1)=1/2$
is used instead, without dividing by a vanishing expression.

Clamp lower factor bounds to zero, multiply the four nonnegative intervals,
and round the resulting Xi endpoints outward. This proves
`ratXiRoundedGrid_enclosure`. Its `XiRoundedEvalChecks` hypotheses contain
only positive integer settings, explicit rational log-range inequalities,
the node-independent finite eta initialization checks and denominator positivity.
There is no assumed real-valued special-function enclosure.

Actual $\varphi(k/40)=\xi(1/2)/\xi(s_k)$ then gives
`ratReciprocalRoundedGrid_enclosure`, provided the evaluated denominator lower
endpoint is positive. The returned reciprocal endpoints are also rounded.
This proves the evaluator's analytic meaning. Concrete high-precision checks
against the retained source table and global density curvature are not asserted.
