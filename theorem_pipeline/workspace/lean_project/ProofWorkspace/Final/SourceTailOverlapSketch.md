# Source tail overlap at radius 48

## Statement and assumptions

For $28.269\le a\le28.270$ and $42.044\le b\le42.045$, take the unchanged source constants $R=48$, $M=268341$, $C=ab/[2(b^2-a^2)]$, and $D_j=2CM(ba^j+ab^j)$. The exact logarithmic threshold satisfies $X\le318/100$.

## Proof Sketch

Algebra cancels $C$ from the three relative coefficients: $U_1=U_2=2M(a^2+6ab+b^2)/(b-a)^2$ and $U_3=2MU_1$. Rational interval arithmetic bounds $U_1$ by $27{,}500{,}000$. The existing exact Taylor enclosure, scaled twenty times, proves $e^{18.93}\ge165{,}000{,}000$. This controls the first two logarithms; squaring controls the third. The given root intervals then bound the three logarithmic quotients by $3.18$.

The coarse intervals are only consequences required from the frozen finer root enclosures. This proves neither those root enclosures nor the actual residual moment cap. No source normalization, radius, or overlap was changed.

## Lean artifacts

- `SourceTailOverlapFull.lean`
- `twoLaplace_tail_coefficients_simplified`
- `exp_1893_div100_lower`
- `source_tail_ratio_upper`
- `source_tail_threshold_le_overlap`
