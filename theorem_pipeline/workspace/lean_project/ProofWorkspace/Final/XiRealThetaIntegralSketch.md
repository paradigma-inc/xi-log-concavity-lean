# Exact real theta-integral formula for F

## Statement and assumptions

For every real $x$, define
$$g_x(t)=t^{-3/4}\cos((x/4)\log t)(\theta(t)-1).$$
This is integrable on $(1,\infty)$, and the actual function satisfies
$$\operatorname{Re}F(x)=\frac{1-\frac{1+x^2}{4}\int_1^\infty g_x(t)\,dt}{8}.$$
There are no numerical or zero-location hypotheses.

## Proof Sketch

The real part of the actual Mellin integrand is the displayed cosine expression, by the complex power formula on the positive axis. The established theta bound supplies integrability. On the critical line the two completed-zeta Mellin integrals are conjugates. Their sum therefore reduces to twice the real part of one integral. Substitution into the fixed definition $F(x)=\xi(1/2+ix/2)/4$, with $s(s-1)=-(1+x^2)/4$, gives the exact constants.

This is an evaluation identity, not yet a finite quadrature or a numerical lower bound at $48$.

## Lean artifacts

- `XiRealThetaIntegralFull.lean`
- `thetaMellinIntegrand_re_cosine`
- `integrableOn_realThetaCosineIntegrand`
- `F_real_eq_theta_cosine_integral`
