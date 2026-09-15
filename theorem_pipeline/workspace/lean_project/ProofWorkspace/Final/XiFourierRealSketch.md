# Reality of the actual reciprocal-Xi density

For real arguments, the actual theta/Mellin integrand is real because positive
real powers agree with their complex counterparts. Conjugation commutes with
the integral, so the actual pole-removed completed zeta is real on the central
interval. The Dirichlet/Gamma formula and Xi functional equation prove reality
on the two remaining real half-lines. Thus $\overline{\xi(s)}=\xi(s)$ for every
real $s$.

The normalized transform therefore equals the real positive ratio
$$
\varphi(u)=\frac{\Re\xi(1/2)}{\Re\xi((1+u)/2)}>0.
$$
Positivity uses the already-proved actual Xi positivity, not a numerical
approximation or an assumed characteristic-function representation.

Conjugating $\varphi(u)e^{-ixu}$ equals evaluating the integrand at $-u$, since
$\varphi$ is even and real. Lebesgue reflection and conjugation of integrals
show the full complex Fourier integral is real. `density_eq_complex_integral`
therefore proves that taking its real part in the original density definition
discards nothing, with the exact $1/(2\pi)$ normalization.

At $x=0$, the defining integral is the integral of the positive continuous,
integrable function $\varphi$. This proves `density_zero_pos`.
It does **not** prove density positivity for every real $x$: a positive Fourier
transform need not have a positive inverse. The residual probability-law
construction remains a separate obligation for the full theorem.
