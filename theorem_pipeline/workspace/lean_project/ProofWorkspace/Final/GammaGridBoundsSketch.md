# Gamma values on the retained grid

The source needs $\Gamma((k+40)/160)$ for natural $k$. If $k<40$, put $x=(k+40)/160$ and use the exact positive recurrence $\Gamma(x)=\Gamma(1+x)/x$; here $1+x\in[5/4,3/2)$. Otherwise let $r=(k-40)\bmod160$ and $n=\lfloor(k-40)/160\rfloor$. Then $x=1/2+r/160+n$.

Induction in the actual Gamma recurrence proves $\Gamma(y+n)=\Gamma(y)\prod_{j<n}(y+j)$ for $y>0$. The rational multiplier is positive, and $y\in[1/2,3/2)$. Thus every grid argument reduces exactly to the proved central rational Gamma enclosure. `ratGammaGrid_enclosure` multiplies its endpoints by the exact positive rational multiplier.

All floor/modulus calculations are in natural numbers before casting. The only remaining numerical hypotheses are the central evaluator's explicit rational scaled-exponential range checks. No recurrence error or special-function table is assumed.

